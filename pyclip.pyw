"""PyClip - a Ditto-style clipboard manager for Windows (single-file edition).

Runs in the system tray, records everything you copy (text, images, files),
and lets you pick an older item from a searchable, previewed list and paste it
straight back into the app you were using.

Run with:
    pythonw pyclip.py     # no console
    python  pyclip.py     # with logs
Press Ctrl+Shift+Alt+V (or click the tray icon) to open the history.
"""

import os
import re
import sys
import time
import json
import sqlite3
import hashlib
import logging
import threading
import tempfile
import uuid
import winreg
import ctypes
from ctypes import wintypes
from logging.handlers import RotatingFileHandler

from PySide6.QtCore import (
    Qt, QObject, Signal, QByteArray, QBuffer, QIODevice, QSize, QRect, QEvent,
    QPoint, QTimer, QUrl, QMimeData, qInstallMessageHandler,
)
from PySide6.QtGui import (
    QColor, QFont, QFontMetrics, QPixmap, QPainter, QPen, QGuiApplication,
    QCursor, QIcon, QImage, QImageReader, QKeySequence, QTextCursor,
    QDesktopServices, QTextBlockFormat, QTextCharFormat, QTextFormat,
)
from PySide6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLineEdit, QLabel,
    QListWidget, QListWidgetItem, QStyledItemDelegate, QStyle, QMenu,
    QAbstractItemView, QSystemTrayIcon, QMessageBox, QTextEdit, QToolButton,
    QSizePolicy, QStackedWidget, QScrollArea, QFrame, QCheckBox,
    QDialog, QDialogButtonBox, QComboBox, QPushButton, QFileDialog,
)

APP_VERSION = "1.1.0"
HISTORY_LIMIT = 300       # newest un-pinned items to keep
HISTORY_MAX_BYTES = 500 * 1024 * 1024
LARGE_CLIP_BYTES = 10 * 1024 * 1024
CLEANUP_KEEP_PINNED = False  # the storage cap also applies to pinned clips
PASTE_DELAY_MS = 140      # let the target window regain focus before Ctrl+V
MAX_IMAGE_PIXELS = 40_000_000
MAX_ENCODED_IMAGE_BYTES = 100 * 1024 * 1024
THUMBNAIL_SIZE = 96
WINDOW_EDGE = 6           # how thick the invisible resize border is
WINDOW_CORNER = 10        # corners get a bigger square, so they're easy to hit
HISTORY_MIN_WIDTH = 300   # the clip list stays readable however narrow it's dragged
WINDOW_MIN_HEIGHT = 300
HISTORY_WIDTH_KEY = "history_width"     # how wide the clip list was dragged
WINDOW_HEIGHT_KEY = "window_height"     # how tall the window was dragged
NOTEPAD_WIDTH = 260      # default width of the expandable notepad panel
NOTEPAD_MIN_WIDTH = 200   # narrow enough to stay a margin note
NOTEPAD_MAX_WIDTH = 900   # wide enough to draft in, without hiding the history
NOTE_GRIP_WIDTH = 8       # the drag handle down the pad's left edge
NOTE_SAVE_DELAY_MS = 600  # debounce typing before writing the note to disk
NOTE_COUNT = 5            # tabs a fresh pad starts with
NOTE_MIN_COUNT = 1        # the last note cannot be closed
NOTE_MAX_COUNT = 12       # more than this and a tab is too narrow to read
NOTE_TAB_MIN_WIDTH = 32   # past this the tab strip scrolls instead of shrinking
NOTE_TITLE_MAX = 14       # characters a tab caption keeps
NOTE_TEXT_KEY = "notepad_text"
NOTE_TITLE_KEY = "notepad_title"
NOTE_COLOR_KEY = "notepad_color"
NOTE_ID_KEY = "notepad_sync_id"
NOTE_SYNC_CONFIG_KEY = "notepad_sync_config"
NOTE_SYNC_STATE_KEY = "notepad_sync_state"
NOTE_SYNC_INTERVAL_MS = 15000
NOTE_SYNC_FOLDER = "PyClip Notes"
NOTE_OPEN_KEY = "notepad_open"
NOTE_TAB_KEY = "notepad_tab"            # which note was showing last (a slot id)
NOTE_ORDER_KEY = "notepad_order"        # slot ids, left to right along the strip
NOTE_WIDTH_KEY = "notepad_width"        # how wide the pad was dragged
NOTE_PINNED_KEY = "notepad_pinned"      # notepad-only, always-on-top mode
DIR_OPEN_KEY = "directory_tab_open"
NOTE_STAMP_FORMAT = "%Y-%m-%d %H:%M"   # what F5 drops into the notepad
NOTE_RICH_PREFIX = "<!--pyclip-rich-->"  # a stored note starting with this is HTML
NOTE_BODY_PX = 12                        # the pad's body text; matches its stylesheet
NOTE_HEADING_PT = {1: 18, 2: 14, 3: 12}  # Word-style Heading 1-3, all bold
NOTE_FONT_SIZES = (8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 28, 36, 48)  # points
NOTE_HIGHLIGHTS = (
    ("Red", "#f28b82"),
    ("Yellow", "#fdd663"),
    ("Green", "#81c995"),
)
NOTE_HIGHLIGHT_INK = "#1b1f27"  # dark text, so a highlight stays readable on the dark pad

# Colours a tab can take. The first NOTE_COUNT double as the defaults, so the
# tabs already tell apart before anyone renames or recolours one.
NOTE_COLORS = (
    ("Blue", "#4c8bf5"),
    ("Teal", "#2ab5a5"),
    ("Green", "#5fb85f"),
    ("Amber", "#e0a33e"),
    ("Rose", "#e4636f"),
    ("Purple", "#a274e8"),
    ("Slate", "#8a909c"),
)


# =============================================================================
#  Storage  (SQLite in %APPDATA%\PyClip)
# =============================================================================

APP_DIR = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "PyClip")
IMAGES_DIR = os.path.join(APP_DIR, "images")
THUMBS_DIR = os.path.join(APP_DIR, "thumbnails")
DB_PATH = os.path.join(APP_DIR, "history.db")
LOG_PATH = os.path.join(APP_DIR, "PyClip.log")


def configure_logging():
    """Write diagnostics to a bounded log, including in windowed builds."""
    logger = logging.getLogger("pyclip")
    logger.setLevel(logging.INFO)
    if not logger.handlers:
        try:
            os.makedirs(APP_DIR, exist_ok=True)
            handler = RotatingFileHandler(
                LOG_PATH, maxBytes=1_000_000, backupCount=3, encoding="utf-8"
            )
        except OSError:
            # Logging must never become a new reason the tray app cannot start.
            handler = logging.StreamHandler() if sys.stderr else logging.NullHandler()
        handler.setFormatter(logging.Formatter(
            "%(asctime)s %(levelname)s %(threadName)s %(message)s"
        ))
        logger.addHandler(handler)
    return logger


logger = configure_logging()


def install_exception_logging():
    """Capture otherwise silent Python/Qt failures from the .pyw executable."""
    def log_exception(exc_type, exc_value, exc_tb):
        if issubclass(exc_type, KeyboardInterrupt):
            return sys.__excepthook__(exc_type, exc_value, exc_tb)
        logger.critical("Unhandled exception", exc_info=(exc_type, exc_value, exc_tb))

    sys.excepthook = log_exception

    if hasattr(threading, "excepthook"):
        def log_thread_exception(args):
            log_exception(args.exc_type, args.exc_value, args.exc_traceback)
        threading.excepthook = log_thread_exception

    def qt_message_handler(msg_type, context, message):
        # Warnings are common in Qt; keep them visible without treating them as fatal.
        logger.warning("Qt: %s", message)
    qInstallMessageHandler(qt_message_handler)


class SafeApplication(QApplication):
    """Keep a faulty event handler from silently terminating the tray process."""

    def notify(self, receiver, event):
        try:
            return super().notify(receiver, event)
        except Exception:
            logger.exception("Unhandled Qt event error in %r", receiver)
            return False


def _atomic_write(path, data):
    """Replace a file only after its complete contents reach disk."""
    temp_path = f"{path}.tmp-{os.getpid()}-{time.time_ns()}"
    try:
        with open(temp_path, "wb") as fh:
            fh.write(data)
            fh.flush()
            os.fsync(fh.fileno())
        os.replace(temp_path, path)
    finally:
        try:
            os.remove(temp_path)
        except FileNotFoundError:
            pass


def _thumbnail_path(image_path):
    return os.path.join(THUMBS_DIR, os.path.basename(image_path))


def _save_thumbnail(image, path):
    os.makedirs(THUMBS_DIR, exist_ok=True)
    thumb = image.scaled(
        THUMBNAIL_SIZE, THUMBNAIL_SIZE,
        Qt.AspectRatioMode.KeepAspectRatio,
        Qt.TransformationMode.SmoothTransformation,
    )
    temp_path = f"{path}.tmp-{os.getpid()}-{time.time_ns()}"
    try:
        if not thumb.save(temp_path, "PNG"):
            raise OSError("Qt could not encode thumbnail")
        os.replace(temp_path, path)
    finally:
        try:
            os.remove(temp_path)
        except FileNotFoundError:
            pass


def load_thumbnail(image_path):
    """Decode only a small preview instead of every full-resolution image."""
    thumb_path = _thumbnail_path(image_path)
    pm = QPixmap(thumb_path)
    if not pm.isNull():
        return pm

    reader = QImageReader(image_path)
    reader.setAutoTransform(True)
    size = reader.size()
    if size.isValid():
        size.scale(
            THUMBNAIL_SIZE, THUMBNAIL_SIZE,
            Qt.AspectRatioMode.KeepAspectRatio,
        )
        reader.setScaledSize(size)
    image = reader.read()
    if image.isNull():
        logger.warning("Could not decode image preview: %s (%s)",
                       image_path, reader.errorString())
        return QPixmap()
    try:
        _save_thumbnail(image, thumb_path)
    except OSError:
        logger.exception("Could not cache image thumbnail: %s", thumb_path)
    return QPixmap.fromImage(image)


# Where a Windows path can begin inside text: "C:\", "C:/", "\\server\share\" or
# "%VAR%\". The look-behind skips URLs ("https://") and words ending in a letter.
_PATH_START = re.compile(
    r"(?<![\w\\/:%])(?:[A-Za-z]:[\\/]|\\\\[^\\/\s\"'<>|*?]+[\\/]|%[A-Za-z_][\w()]*%[\\/])")
_PATH_STOP = re.compile(r"[\"<>|*?\t]")          # characters no Windows path contains
_PATH_TRAIL = " .,;:!)]}'\u2019\u201d"           # sentence punctuation after a path
_FILE_URL = re.compile(r"file:/{2,3}[^\s\"'<>|]+", re.IGNORECASE)
_FILE_NAME = re.compile(r".+\.[A-Za-z0-9]{1,8}")
_MAX_PATH_SCAN = 100_000                          # characters of a text clip scanned
_MAX_PATH_CUTS = 12                               # shorter prefixes tried per path


def _absolute_path(path):
    path = os.path.expandvars(path.strip())
    if not os.path.splitdrive(path)[0] or not os.path.isabs(path):
        return None
    return os.path.normpath(path)


def _existing_folder(path, roots):
    """The folder `path` names (or the folder holding it, for a file), if it exists.
    `roots` caches whether each drive or share is reachable, so an offline one is
    asked about once rather than for every prefix tried."""
    path = _absolute_path(path)
    if not path:
        return None
    root = os.path.splitdrive(path)[0] + os.sep
    try:
        if root not in roots:
            roots[root] = os.path.isdir(root)
        if not roots[root]:
            return None
        if os.path.isdir(path):
            return path
        if os.path.isfile(path):
            return os.path.dirname(path)
    except (OSError, ValueError):
        pass
    return None


def _paths_in_text(text):
    """(raw path text, whether it is the whole line) for each path-like run."""
    for line in text[:_MAX_PATH_SCAN].splitlines():
        whole = line.strip().strip("\"'").rstrip(_PATH_TRAIL)
        for url in _FILE_URL.findall(line):
            local = QUrl(url.rstrip(_PATH_TRAIL)).toLocalFile()
            if local:
                yield local, url.rstrip(_PATH_TRAIL) == whole
        line = _FILE_URL.sub(" ", line)
        starts = [m.start() for m in _PATH_START.finditer(line)]
        for n, start in enumerate(starts):
            raw = line[start:starts[n + 1] if n + 1 < len(starts) else len(line)]
            stop = _PATH_STOP.search(raw)
            if stop:
                raw = raw[:stop.start()]
            yield raw, raw.rstrip(_PATH_TRAIL) == whole


def _folder_from_text(raw, whole_line, roots):
    """Paths in prose may contain spaces and run into the sentence around them, so
    try the longest prefix first and back off one word at a time until a real
    folder or file is found."""
    cuts = [len(raw)] + [m.start() for m in reversed(list(re.finditer(r"\s", raw)))]
    tried = set()
    for cut in cuts[:_MAX_PATH_CUTS]:
        piece = raw[:cut]
        for candidate in (piece.rstrip(), piece.rstrip(_PATH_TRAIL)):
            if candidate and candidate not in tried:
                tried.add(candidate)
                folder = _existing_folder(candidate, roots)
                if folder:
                    return folder
    if not whole_line:
        return None
    # A line that is nothing but a path is kept even if its drive or share is
    # offline right now; a name with an extension is taken to be a file.
    path = _absolute_path(raw.rstrip(_PATH_TRAIL))
    if path and _FILE_NAME.fullmatch(os.path.basename(path)):
        path = os.path.dirname(path)
    return path


def clipboard_directories(kind, text, data, roots=None):
    """Find folders in file drops, or anywhere in text that looks like a path."""
    roots = {} if roots is None else roots
    directories = {}
    if kind == "files":
        try:
            candidates = json.loads(data)
        except (TypeError, ValueError):
            return []
        if not isinstance(candidates, list):
            return []
        folders = (_existing_folder(c, roots) for c in candidates if isinstance(c, str))
    elif kind == "text" and text:
        folders = (_folder_from_text(raw, whole, roots) for raw, whole in _paths_in_text(text))
    else:
        return []
    for folder in folders:
        if folder:
            directories[os.path.normcase(folder)] = folder
    return list(directories.values())


class Database:
    """Clipboard, directory history and settings. Images are saved separately;
    text and file-lists are stored inline."""

    def __init__(self):
        os.makedirs(IMAGES_DIR, exist_ok=True)
        os.makedirs(THUMBS_DIR, exist_ok=True)
        self.conn = None
        try:
            self._open()
        except sqlite3.DatabaseError:
            logger.exception("Clipboard database is damaged; preserving and rebuilding it")
            self._close_quietly()
            self._quarantine_database()
            self._open()

    def _open(self):
        self.conn = sqlite3.connect(DB_PATH, timeout=15)
        self.conn.row_factory = sqlite3.Row
        self.conn.execute("PRAGMA busy_timeout = 15000")
        self.conn.execute("PRAGMA journal_mode = WAL")
        self.conn.execute("PRAGMA synchronous = NORMAL")
        self._init_schema()
        result = self.conn.execute("PRAGMA quick_check").fetchone()[0]
        if result != "ok":
            raise sqlite3.DatabaseError(f"quick_check failed: {result}")
        self.enforce_size_limit()

    def _close_quietly(self):
        if self.conn is not None:
            try:
                self.conn.close()
            except sqlite3.Error:
                pass
            self.conn = None

    @staticmethod
    def _quarantine_database():
        stamp = time.strftime("%Y%m%d-%H%M%S")
        for suffix in ("", "-wal", "-shm"):
            source = DB_PATH + suffix
            if os.path.exists(source):
                target = os.path.join(APP_DIR, f"history.corrupt-{stamp}.db{suffix}")
                os.replace(source, target)
                logger.error("Preserved damaged database file as %s", target)

    def _init_schema(self):
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS clips (
                id         INTEGER PRIMARY KEY AUTOINCREMENT,
                kind       TEXT NOT NULL,          -- 'text' | 'image' | 'files'
                text       TEXT,                   -- full text (text clips)
                data       TEXT,                   -- image path, or JSON list of paths
                preview    TEXT,                   -- short label shown in the list
                hash       TEXT UNIQUE,            -- de-duplication key
                pinned     INTEGER DEFAULT 0,
                created_at REAL
            )
            """
        )
        self.conn.execute("CREATE INDEX IF NOT EXISTS idx_created ON clips(created_at)")
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS settings (
                key   TEXT PRIMARY KEY,
                value TEXT
            )
            """
        )
        self.conn.execute(
            """CREATE TABLE IF NOT EXISTS directories (
                path_key TEXT PRIMARY KEY,
                path TEXT NOT NULL,
                used_at REAL NOT NULL
            )"""
        )
        # Kept apart from `directories` so clearing DIR history never unpins one.
        self.conn.execute(
            """CREATE TABLE IF NOT EXISTS favorite_directories (
                path_key TEXT PRIMARY KEY,
                path TEXT NOT NULL,
                added_at REAL NOT NULL
            )"""
        )
        self.conn.commit()
        # "2": rescan once more now that paths are also found inside text.
        if self.get_setting("directory_history_imported") != "2":
            roots = {}
            for clip in self.conn.execute(
                    "SELECT kind, text, data, created_at FROM clips "
                    "WHERE kind IN ('text', 'files')").fetchall():
                self.remember_directories(
                    clipboard_directories(clip["kind"], clip["text"], clip["data"], roots),
                    clip["created_at"],
                )
            self.set_setting("directory_history_imported", "2")

    def get_setting(self, key, default=""):
        """Small key/value store for things that aren't clips (e.g. the notepad)."""
        row = self.conn.execute(
            "SELECT value FROM settings WHERE key = ?", (key,)
        ).fetchone()
        if row is None or row["value"] is None:
            return default
        return row["value"]

    def set_setting(self, key, value):
        with self.conn:
            self.conn.execute(
                "INSERT INTO settings (key, value) VALUES (?, ?) "
                "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
                (key, value),
            )

    def delete_setting(self, key):
        """Drop a setting entirely, so its default applies if it comes back."""
        with self.conn:
            self.conn.execute("DELETE FROM settings WHERE key = ?", (key,))

    def add_clip(self, kind, text, data, preview, h):
        """Insert a clip, or bump an existing identical one to the top."""
        self.remember_directories(clipboard_directories(kind, text, data))
        cur = self.conn.cursor()
        row = cur.execute("SELECT id FROM clips WHERE hash = ?", (h,)).fetchone()
        now = time.time()
        if row:
            cur.execute("UPDATE clips SET created_at = ? WHERE id = ?", (now, row["id"]))
            self.conn.commit()
            self.enforce_size_limit()
            return row["id"]
        cur.execute(
            "INSERT INTO clips (kind, text, data, preview, hash, pinned, created_at) "
            "VALUES (?, ?, ?, ?, ?, 0, ?)",
            (kind, text, data, preview, h, now),
        )
        self.conn.commit()
        self.enforce_size_limit()
        return cur.lastrowid

    def remember_directories(self, paths, used_at=None):
        when = time.time() if used_at is None else float(used_at)
        with self.conn:
            self.conn.executemany(
                "INSERT INTO directories (path_key, path, used_at) VALUES (?, ?, ?) "
                "ON CONFLICT(path_key) DO UPDATE SET path = excluded.path, "
                "used_at = excluded.used_at WHERE excluded.used_at >= directories.used_at",
                ((os.path.normcase(os.path.normpath(path)), os.path.normpath(path), when)
                 for path in paths),
            )

    def get_directories(self, search=""):
        # Filtering in Python gives Unicode case folding and literal '%'/'_' searches.
        query = search.strip().casefold()
        rows = self.conn.execute(
            "SELECT path, used_at FROM directories ORDER BY used_at DESC, path"
        ).fetchall()
        return [row for row in rows if query in row["path"].casefold()]

    def forget_directory(self, path):
        with self.conn:
            self.conn.execute("DELETE FROM directories WHERE path_key = ?",
                              (os.path.normcase(os.path.normpath(path)),))

    def add_favorite(self, path):
        path = os.path.normpath(path)
        with self.conn:
            self.conn.execute(
                "INSERT OR IGNORE INTO favorite_directories (path_key, path, added_at) "
                "VALUES (?, ?, ?)", (os.path.normcase(path), path, time.time()))

    def remove_favorite(self, path):
        with self.conn:
            self.conn.execute("DELETE FROM favorite_directories WHERE path_key = ?",
                              (os.path.normcase(os.path.normpath(path)),))

    def get_favorites(self, search=""):
        """Favourites in the order they were added, so they stay where you put them."""
        query = search.strip().casefold()
        rows = self.conn.execute(
            "SELECT path, added_at FROM favorite_directories ORDER BY added_at, path"
        ).fetchall()
        return [row for row in rows if query in row["path"].casefold()]

    def favorite_keys(self):
        return {row[0] for row in
                self.conn.execute("SELECT path_key FROM favorite_directories")}

    def get_clips(self, search=None, limit=500, include_content=True):
        params = []
        columns = "*" if include_content else (
            "id, kind, data, preview, hash, pinned, created_at, "
            "length(CAST(COALESCE(text, '') AS BLOB)) AS text_bytes"
        )
        query = f"SELECT {columns} FROM clips"
        if search:
            query += " WHERE preview LIKE ? OR text LIKE ?"
            params += [f"%{search}%", f"%{search}%"]
        query += " ORDER BY pinned DESC, created_at DESC LIMIT ?"
        params.append(limit)
        return self.conn.execute(query, params).fetchall()

    def get_one(self, clip_id):
        return self.conn.execute("SELECT * FROM clips WHERE id = ?", (clip_id,)).fetchone()

    def storage_entries(self):
        """Measure saved payloads without loading full text or decoding images."""
        rows = self.conn.execute(
            "SELECT id, kind, data, pinned, created_at, "
            "length(CAST(COALESCE(text, '') AS BLOB)) AS text_bytes FROM clips"
        ).fetchall()
        return [dict(row, size_bytes=clip_size_bytes(row) or 0) for row in rows]

    def _clean_storage(self, target_bytes, minimum_bytes=0):
        entries = self.storage_entries()
        total = sum(entry["size_bytes"] for entry in entries)
        removed = []
        for entry in sorted(entries, key=lambda row: (-row["size_bytes"], row["id"])):
            if total <= target_bytes or entry["size_bytes"] < minimum_bytes:
                break
            if (CLEANUP_KEEP_PINNED and entry["pinned"]) or not entry["size_bytes"]:
                continue
            removed.append(entry)
            total -= entry["size_bytes"]
        if removed:
            with self.conn:
                self.conn.executemany("DELETE FROM clips WHERE id = ?",
                                      ((entry["id"],) for entry in removed))
            for entry in removed:
                self._remove_asset(entry)
            logger.info("Clipboard cleanup removed %s entries (%s payload bytes)",
                        len(removed), sum(entry["size_bytes"] for entry in removed))
        return {
            "removed_ids": [entry["id"] for entry in removed],
            "removed_bytes": sum(entry["size_bytes"] for entry in removed),
            "total_bytes": total,
        }

    def enforce_size_limit(self, max_bytes=None):
        """Delete the largest saved clips until the total meets the storage cap."""
        return self._clean_storage(HISTORY_MAX_BYTES if max_bytes is None else max_bytes)

    def clean_large_clips(self):
        """Manual cleanup removes all clips of at least LARGE_CLIP_BYTES."""
        return self._clean_storage(0, minimum_bytes=LARGE_CLIP_BYTES)

    def delete(self, clip_id):
        row = self.conn.execute(
            "SELECT kind, data FROM clips WHERE id = ?", (clip_id,)
        ).fetchone()
        with self.conn:
            self.conn.execute("DELETE FROM clips WHERE id = ?", (clip_id,))
        self._remove_asset(row)

    def toggle_pin(self, clip_id):
        self.conn.execute(
            "UPDATE clips SET pinned = CASE pinned WHEN 1 THEN 0 ELSE 1 END WHERE id = ?",
            (clip_id,),
        )
        self.conn.commit()

    def clear(self, keep_pinned=True):
        where = " WHERE pinned = 0" if keep_pinned else ""
        rows = self.conn.execute("SELECT kind, data FROM clips" + where).fetchall()
        with self.conn:
            self.conn.execute("DELETE FROM clips" + where)
        for row in rows:
            self._remove_asset(row)

    def enforce_limit(self, max_items=300):
        """Trim un-pinned history to ``max_items`` newest entries."""
        rows = self.conn.execute(
            "SELECT id, kind, data FROM clips WHERE pinned = 0 ORDER BY created_at DESC"
        ).fetchall()
        expired = rows[max_items:]
        with self.conn:
            self.conn.executemany(
                "DELETE FROM clips WHERE id = ?", ((row["id"],) for row in expired)
            )
        for row in expired:
            self._remove_asset(row)

    def close(self):
        if self.conn is not None:
            try:
                self.conn.execute("PRAGMA wal_checkpoint(PASSIVE)")
            except sqlite3.Error:
                logger.exception("Database checkpoint failed during shutdown")
            self._close_quietly()

    @staticmethod
    def _remove_asset(row):
        if row and row["kind"] == "image" and row["data"]:
            # History cleanup may remove only PyClip's own saved assets.
            # Legacy or damaged records must never turn into arbitrary file deletion.
            image_path = os.path.realpath(row["data"])
            if os.path.normcase(os.path.dirname(image_path)) != os.path.normcase(os.path.realpath(IMAGES_DIR)):
                logger.warning("Kept image outside PyClip's image folder: %s", row["data"])
                return
            for path, directory in ((image_path, IMAGES_DIR),
                                    (_thumbnail_path(image_path), THUMBS_DIR)):
                path = os.path.realpath(path)
                if os.path.normcase(os.path.dirname(path)) != os.path.normcase(os.path.realpath(directory)):
                    continue
                try:
                    os.remove(path)
                except FileNotFoundError:
                    pass
                except OSError:
                    logger.exception("Could not remove image asset: %s", path)


# =============================================================================
#  Win32 glue  (global hotkey, foreground window, synthetic paste)
# =============================================================================

user32 = ctypes.windll.user32
kernel32 = ctypes.windll.kernel32

MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_SHIFT = 0x0004
MOD_WIN = 0x0008
MOD_NOREPEAT = 0x4000
WM_HOTKEY = 0x0312

user32.RegisterHotKey.argtypes = [wintypes.HWND, ctypes.c_int, wintypes.UINT, wintypes.UINT]
user32.RegisterHotKey.restype = wintypes.BOOL
user32.UnregisterHotKey.argtypes = [wintypes.HWND, ctypes.c_int]
user32.UnregisterHotKey.restype = wintypes.BOOL
user32.GetForegroundWindow.restype = wintypes.HWND
user32.SetForegroundWindow.argtypes = [wintypes.HWND]
user32.SetForegroundWindow.restype = wintypes.BOOL
user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
user32.GetWindowThreadProcessId.restype = wintypes.DWORD
user32.AttachThreadInput.argtypes = [wintypes.DWORD, wintypes.DWORD, wintypes.BOOL]
user32.AttachThreadInput.restype = wintypes.BOOL
user32.BringWindowToTop.argtypes = [wintypes.HWND]
user32.BringWindowToTop.restype = wintypes.BOOL
kernel32.GetCurrentThreadId.restype = wintypes.DWORD
kernel32.CreateMutexW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
kernel32.CreateMutexW.restype = wintypes.HANDLE
kernel32.CreateEventW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.BOOL, wintypes.LPCWSTR]
kernel32.CreateEventW.restype = wintypes.HANDLE
kernel32.SetEvent.argtypes = [wintypes.HANDLE]
kernel32.SetEvent.restype = wintypes.BOOL
kernel32.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
kernel32.WaitForSingleObject.restype = wintypes.DWORD
kernel32.GetLastError.restype = wintypes.DWORD
kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
kernel32.CloseHandle.restype = wintypes.BOOL

ERROR_ALREADY_EXISTS = 183
INSTANCE_MUTEX_NAME = r"Local\PyClip-8C393C90-0AD6-4D47-A85B-53C8C1F534B8"


class SingleInstance:
    """Prevent duplicate tray processes from racing on the same database."""

    def __init__(self):
        self.handle = kernel32.CreateMutexW(None, False, INSTANCE_MUTEX_NAME)
        if not self.handle:
            raise ctypes.WinError()
        self.already_running = kernel32.GetLastError() == ERROR_ALREADY_EXISTS
        self.activation = kernel32.CreateEventW(None, False, False, INSTANCE_MUTEX_NAME + "-Show")
        if not self.activation:
            error = ctypes.WinError()
            kernel32.CloseHandle(self.handle)
            self.handle = None
            raise error

    def request_activation(self):
        """A manual second launch asks the tray instance to show its window."""
        if not kernel32.SetEvent(self.activation):
            raise ctypes.WinError()

    def take_activation(self):
        # Auto-reset event retains a request even while the first copy starts up.
        return kernel32.WaitForSingleObject(self.activation, 0) == 0

    def close(self):
        if self.activation:
            kernel32.CloseHandle(self.activation)
            self.activation = None
        if self.handle:
            kernel32.CloseHandle(self.handle)
            self.handle = None


class GlobalHotkey(QWidget):
    """A hidden window that owns a system-wide hotkey and emits ``activated``."""

    activated = Signal()

    def __init__(self, modifiers, vk, hotkey_id=1, parent=None):
        super().__init__(parent)
        self._id = hotkey_id
        hwnd = wintypes.HWND(int(self.winId()))  # forces native handle creation
        self.registered = bool(user32.RegisterHotKey(hwnd, hotkey_id, modifiers, vk))

    def nativeEvent(self, event_type, message):
        if event_type == b"windows_generic_MSG":
            msg = wintypes.MSG.from_address(int(message))
            if msg.message == WM_HOTKEY and msg.wParam == self._id:
                self.activated.emit()
                return True, 0
        return super().nativeEvent(event_type, message)

    def unregister(self):
        if getattr(self, "registered", False):
            user32.UnregisterHotKey(wintypes.HWND(int(self.winId())), self._id)
            self.registered = False


def get_foreground_window():
    return user32.GetForegroundWindow()


def force_foreground(hwnd):
    """Bring ``hwnd`` to the front, working around focus-stealing prevention."""
    if not hwnd:
        return
    cur_thread = kernel32.GetCurrentThreadId()
    target_thread = user32.GetWindowThreadProcessId(hwnd, None)
    attached = False
    try:
        if target_thread and target_thread != cur_thread:
            attached = bool(user32.AttachThreadInput(cur_thread, target_thread, True))
        user32.BringWindowToTop(hwnd)
        user32.SetForegroundWindow(hwnd)
    except Exception:
        logger.exception("Could not force foreground window %s", hwnd)
        user32.SetForegroundWindow(hwnd)
    finally:
        if attached:
            user32.AttachThreadInput(cur_thread, target_thread, False)


INPUT_KEYBOARD = 1
KEYEVENTF_KEYUP = 0x0002
VK_CONTROL = 0x11
VK_V = 0x56
PUL = ctypes.POINTER(ctypes.c_ulong)


class _KEYBDINPUT(ctypes.Structure):
    _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD),
                ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD),
                ("dwExtraInfo", PUL)]


class _MOUSEINPUT(ctypes.Structure):
    _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG),
                ("mouseData", wintypes.DWORD), ("dwFlags", wintypes.DWORD),
                ("time", wintypes.DWORD), ("dwExtraInfo", PUL)]


class _HARDWAREINPUT(ctypes.Structure):
    _fields_ = [("uMsg", wintypes.DWORD), ("wParamL", wintypes.WORD),
                ("wParamH", wintypes.WORD)]


class _INPUTUNION(ctypes.Union):
    _fields_ = [("ki", _KEYBDINPUT), ("mi", _MOUSEINPUT), ("hi", _HARDWAREINPUT)]


class _INPUT(ctypes.Structure):
    _anonymous_ = ("u",)
    _fields_ = [("type", wintypes.DWORD), ("u", _INPUTUNION)]


user32.SendInput.argtypes = [wintypes.UINT, ctypes.POINTER(_INPUT), ctypes.c_int]
user32.SendInput.restype = wintypes.UINT


def _key(vk, up=False):
    inp = _INPUT(type=INPUT_KEYBOARD)
    inp.ki = _KEYBDINPUT(vk, 0, KEYEVENTF_KEYUP if up else 0, 0, None)
    return inp


def send_paste():
    """Send Ctrl+V to whichever window currently has focus."""
    events = (_INPUT * 4)(
        _key(VK_CONTROL), _key(VK_V), _key(VK_V, up=True), _key(VK_CONTROL, up=True)
    )
    sent = user32.SendInput(4, events, ctypes.sizeof(_INPUT))
    if sent != 4:
        logger.warning("SendInput sent %s of 4 keyboard events (WinError %s)",
                       sent, kernel32.GetLastError())


# =============================================================================
#  Run at startup  (HKCU\...\Run registry entry, no admin needed)
# =============================================================================

APP_NAME = "PyClip"
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
# Windows passes this flag at login so the app knows to stay in the tray.
STARTUP_FLAG = "--startup"


def _startup_command():
    """The command Windows runs at login: pythonw (no console) + this script."""
    # A frozen build is already a standalone executable.  Its ``__file__``
    # points inside PyInstaller's extraction area and must not be persisted.
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}" {STARTUP_FLAG}'
    exe = sys.executable
    pythonw = os.path.join(os.path.dirname(exe), "pythonw.exe")
    if os.path.exists(pythonw):
        exe = pythonw
    return f'"{exe}" "{os.path.abspath(__file__)}" {STARTUP_FLAG}'


def is_startup_enabled():
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as key:
            winreg.QueryValueEx(key, APP_NAME)
            return True
    except OSError:  # value (or key) missing
        return False


def set_startup(enabled):
    with winreg.CreateKeyEx(winreg.HKEY_CURRENT_USER, RUN_KEY, 0,
                            winreg.KEY_SET_VALUE) as key:
        if enabled:
            winreg.SetValueEx(key, APP_NAME, 0, winreg.REG_SZ, _startup_command())
        else:
            try:
                winreg.DeleteValue(key, APP_NAME)
            except FileNotFoundError:
                pass


def _ensure_startup_flag():
    """Add ``--startup`` to a startup entry written by an older version.

    Only the flag is appended: the recorded executable and path are left
    alone, so an entry pointing at an installed build keeps pointing there.
    """
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0,
                            winreg.KEY_READ | winreg.KEY_SET_VALUE) as key:
            try:
                command, kind = winreg.QueryValueEx(key, APP_NAME)
            except FileNotFoundError:  # startup simply not enabled
                return
            if kind != winreg.REG_SZ or STARTUP_FLAG in command.split():
                return
            winreg.SetValueEx(key, APP_NAME, 0, winreg.REG_SZ,
                              f"{command} {STARTUP_FLAG}")
            logger.info("Startup command updated to stay in the tray at login")
    except OSError:
        logger.exception("Could not update the startup command")


# =============================================================================
#  Clipboard watcher
# =============================================================================

class ClipboardMonitor(QObject):
    clip_added = Signal()

    def __init__(self, db):
        super().__init__()
        self.db = db
        self.clipboard = QApplication.clipboard()
        self._internal_change = False
        self.clipboard.dataChanged.connect(self._on_change)

    def set_internal(self, active):
        """Ignore synchronous events caused by PyClip restoring an old clip."""
        self._internal_change = active

    def _on_change(self):
        if self._internal_change:
            return
        mime = self.clipboard.mimeData()
        if mime is None:
            return
        try:
            if mime.hasImage() and self._save_image():
                pass
            elif mime.hasUrls() and self._save_files(mime):
                pass
            elif mime.hasText():
                if not self._save_text(mime):
                    return
            else:
                return
        except Exception:  # never let a bad clip crash the watcher
            logger.exception("Clipboard capture failed")
            return
        self.clip_added.emit()

    def _save_image(self):
        img = self.clipboard.image()
        if img.isNull():
            return False
        pixels = img.width() * img.height()
        if pixels > MAX_IMAGE_PIXELS:
            logger.warning("Skipped oversized clipboard image: %sx%s", img.width(), img.height())
            return False
        buf_bytes = QByteArray()
        buf = QBuffer(buf_bytes)
        if not buf.open(QIODevice.OpenModeFlag.WriteOnly):
            raise OSError("Could not allocate image buffer")
        try:
            if not img.save(buf, "PNG"):
                raise OSError("Qt could not encode clipboard image")
        finally:
            buf.close()
        raw = bytes(buf_bytes)
        if not raw or len(raw) > MAX_ENCODED_IMAGE_BYTES:
            logger.warning("Skipped clipboard image with encoded size %s bytes", len(raw))
            return False
        digest = hashlib.sha1(raw).hexdigest()
        path = os.path.join(IMAGES_DIR, digest + ".png")
        if not os.path.exists(path):
            _atomic_write(path, raw)
        thumb_path = _thumbnail_path(path)
        if not os.path.exists(thumb_path):
            try:
                _save_thumbnail(img, thumb_path)
            except OSError:
                logger.exception("Could not create image thumbnail")
        self.db.add_clip("image", None, path,
                         f"Image  {img.width()}×{img.height()}", "img:" + digest)
        return True

    def _save_files(self, mime):
        paths = [u.toLocalFile() for u in mime.urls() if u.isLocalFile()]
        paths = [p for p in paths if p]
        if not paths:
            return False  # likely a web URL -> let the text branch handle it
        data = json.dumps(paths)
        names = [os.path.basename(p.rstrip("/\\")) or p for p in paths]
        preview = "  |  ".join(names)
        if len(paths) > 1:
            preview = f"{len(paths)} items:  " + preview
        h = "files:" + hashlib.sha1(data.encode("utf-8")).hexdigest()
        self.db.add_clip("files", None, data, preview[:200], h)
        return True

    def _save_text(self, mime):
        text = mime.text()
        if not text or not text.strip():
            return False
        h = "txt:" + hashlib.sha1(text.encode("utf-8", "ignore")).hexdigest()
        preview = " ".join(text.split())[:200]
        self.db.add_clip("text", text, None, preview, h)
        return True


# =============================================================================
#  History popup  (search box + previewed list)
# =============================================================================

def humanize(ts):
    try:
        delta = max(0, time.time() - float(ts))
    except (TypeError, ValueError):
        return "unknown time"
    if delta < 60:
        return "just now"
    if delta < 3600:
        return f"{int(delta // 60)} min ago"
    if delta < 86400:
        return f"{int(delta // 3600)} hr ago"
    return f"{int(delta // 86400)} d ago"


def clip_size_bytes(clip):
    """Size of the saved payload, excluding database/preview overhead and RAM.

    File clips store only a JSON list of paths, not the referenced files.
    Images use their saved PNG size without decoding the full image.
    """
    if clip["kind"] == "image":
        try:
            return os.path.getsize(clip["data"]) if clip["data"] else None
        except (OSError, ValueError):
            return None
    if clip["kind"] in ("text", "files"):
        if clip["kind"] == "text" and "text_bytes" in clip.keys():
            return clip["text_bytes"]
        payload = clip["text"] if clip["kind"] == "text" else clip["data"]
        return len((payload or "").encode("utf-8"))
    return None


def format_size(size):
    """Compact file-size notation, using 1024 bytes per KB."""
    if size is None:
        return "size unavailable"
    if size < 1024:
        return f"{size} B"
    for unit in ("KB", "MB", "GB", "TB"):
        size /= 1024
        if size < 1024 or unit == "TB":
            return f"{size:.1f} {unit}"


def hint_label(text):
    """A caption that stays decorative: it never dictates the window's width."""
    label = QLabel(text)
    label.setObjectName("hint")
    label.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)
    return label


class ClipDelegate(QStyledItemDelegate):
    """Paints each row: thumbnail/badge on the left, two lines of text right."""

    ROW_H = 58
    THUMB = 42
    PAD = 10
    BADGE = {"text": "#3f6fd1", "files": "#c98a2b", "image": "#7a4fd1",
             "directory": "#2a8c80"}
    LETTER = {"text": "T", "files": "F", "image": "I", "directory": "D"}

    def sizeHint(self, option, index):
        return QSize(option.rect.width(), self.ROW_H)

    def paint(self, painter, option, index):
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)

        rect = option.rect
        if option.state & QStyle.StateFlag.State_Selected:
            painter.fillRect(rect, QColor("#33405a"))
        elif option.state & QStyle.StateFlag.State_MouseOver:
            painter.fillRect(rect, QColor("#242a36"))

        data = index.data(Qt.ItemDataRole.UserRole) or {}
        pm = index.data(Qt.ItemDataRole.UserRole + 1)
        kind = data.get("kind", "text")

        ty = rect.top() + (rect.height() - self.THUMB) // 2
        thumb_rect = QRect(rect.left() + self.PAD, ty, self.THUMB, self.THUMB)

        if isinstance(pm, QPixmap) and not pm.isNull():
            scaled = pm.scaled(
                self.THUMB, self.THUMB,
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation,
            )
            dx = thumb_rect.left() + (self.THUMB - scaled.width()) // 2
            dy = thumb_rect.top() + (self.THUMB - scaled.height()) // 2
            painter.drawPixmap(dx, dy, scaled)
        else:
            painter.setBrush(QColor(self.BADGE.get(kind, "#3f6fd1")))
            painter.setPen(Qt.PenStyle.NoPen)
            painter.drawRoundedRect(thumb_rect, 8, 8)
            painter.setPen(QColor("white"))
            f = QFont(); f.setBold(True); f.setPointSize(13)
            painter.setFont(f)
            painter.drawText(thumb_rect, Qt.AlignmentFlag.AlignCenter,
                             self.LETTER.get(kind, "T"))

        text_left = thumb_rect.right() + self.PAD
        text_w = rect.right() - text_left - self.PAD

        painter.setPen(QColor("#e8eaed"))
        pf = QFont(); pf.setPointSize(10)
        painter.setFont(pf)
        primary = QFontMetrics(pf).elidedText(
            data.get("primary", ""), Qt.TextElideMode.ElideRight, text_w
        )
        painter.drawText(
            QRect(text_left, rect.top() + 9, text_w, 20),
            Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, primary,
        )

        meta = data.get("meta", "")
        if data.get("pinned"):
            meta = "\U0001F4CC  " + meta
        painter.setPen(QColor("#8a909c"))
        mf = QFont(); mf.setPointSize(8)
        painter.setFont(mf)
        meta = QFontMetrics(mf).elidedText(
            meta, Qt.TextElideMode.ElideRight, text_w
        )
        painter.drawText(
            QRect(text_left, rect.top() + 30, text_w, 18),
            Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, meta,
        )
        painter.restore()


# =============================================================================
#  Notepad list formatting  (plain text in, plain text out)
# =============================================================================
#
# The pad stores plain text, so a "list" is just a marker typed at the start of
# each line. That keeps notes readable everywhere they're pasted, and it means
# every helper below is an ordinary string function.

NUMBER_ITEM = re.compile(r"^(\s*)(\d+)([.)])(\s+)")  # indent, count, dot, gap

LIST_MARKERS = {
    "bullet": re.compile(r"^(\s*)[•\-\*]\s+"),
    "number": NUMBER_ITEM,
    "todo":   re.compile(r"^(\s*)\[[ xX]\]\s+"),
}
ANY_MARKER = re.compile(r"^(\s*)(?:[•\-\*]|\d+[.)]|\[[ xX]\])\s+")
DONE_BOX = re.compile(r"^(\s*)\[([ xX])\](\s+)")


def _strip_marker(line):
    return ANY_MARKER.sub(r"\1", line, count=1)


def _marker(style, number):
    if style == "number":
        return f"{number}. "
    return "[ ] " if style == "todo" else "• "


def relist(lines, style):
    """Turn ``lines`` into a list of ``style`` — or back into plain lines.

    One menu entry both makes and unmakes a list: when every filled line
    already carries the requested marker the markers come off, otherwise they
    go on (replacing markers of another style, so bullets become numbers).
    Blank lines keep their spacing, unless the whole selection is blank —
    that's someone clearing space to start a fresh list.
    """
    filled = [line for line in lines if line.strip()]
    if filled and all(LIST_MARKERS[style].match(line) for line in filled):
        return [_strip_marker(line) for line in lines]

    out, number = [], 0
    for line in lines:
        if filled and not line.strip():
            out.append(line)
            continue
        body = _strip_marker(line)
        indent = body[:len(body) - len(body.lstrip())]
        number += 1
        out.append(indent + _marker(style, number) + body[len(indent):])
    return out


def wanted_numbers(lines):
    """The count each of ``lines`` should carry, or ``None`` where it isn't numbered.

    A run counts 1, 2, 3… from wherever it starts, so deleting or inserting an
    item in the middle no longer leaves a gap. Blank lines are only a gap in a
    list and don't end it; any other unnumbered line does. Indented items keep
    a count of their own, which restarts each time the list steps back out.
    """
    wanted, counters = [], {}
    for line in lines:
        match = NUMBER_ITEM.match(line)
        if not line.strip():
            wanted.append(None)
            continue
        if not match:
            counters.clear()
            wanted.append(None)
            continue
        indent = len(match.group(1))
        for deeper in [width for width in counters if width > indent]:
            del counters[deeper]
        counters[indent] = counters.get(indent, 0) + 1
        wanted.append(counters[indent])
    return wanted


def renumber(lines):
    """``lines`` with every numbered run counting from one again."""
    out = []
    for line, want in zip(lines, wanted_numbers(lines)):
        match = NUMBER_ITEM.match(line) if want else None
        if match and match.group(2) != str(want):
            line = f"{match.group(1)}{want}{line[match.end(2):]}"
        out.append(line)
    return out


def inherited_marker(line):
    """The marker a new line should start with after Enter on ``line``."""
    match = ANY_MARKER.match(line)
    if not match:
        return ""
    indent = match.group(1)
    body = line[len(indent):match.end()]
    counted = re.match(r"(\d+)([.)])", body)
    if counted:
        return f"{indent}{int(counted.group(1)) + 1}{counted.group(2)} "
    return f"{indent}[ ] " if body.startswith("[") else f"{indent}{body[0]} "


def toggle_done(line):
    """Flip a checklist line between ``[ ]`` and ``[x]``; leave others alone."""
    match = DONE_BOX.match(line)
    if not match:
        return line
    box = "x" if match.group(2) == " " else " "
    return f"{match.group(1)}[{box}]{match.group(3)}{line[match.end():]}"


# =============================================================================
#  Notepad text styles  (headings, sizes and highlights)
# =============================================================================
#
# A note stays plain text until someone styles it; only then is it stored as
# HTML, behind NOTE_RICH_PREFIX. Sizes are kept as pixel sizes because that is
# how Qt records the pad's own 12px body text, but menus speak Word's points.

SIZE_PROPS = (QTextFormat.Property.FontPixelSize, QTextFormat.Property.FontPointSize)
HIGHLIGHT_PROPS = (QTextFormat.Property.BackgroundBrush,
                   QTextFormat.Property.ForegroundBrush)


def pt_to_px(points):
    return round(points * 4 / 3)


def px_to_pt(pixels):
    return round(pixels * 3 / 4)


def styled_format(fmt):
    """Whether one run of text carries a size, weight or highlight of its own."""
    size = fmt.property(QTextFormat.Property.FontPixelSize)
    return (fmt.background().style() != Qt.BrushStyle.NoBrush
            or fmt.fontWeight() > QFont.Weight.Normal.value
            or fmt.hasProperty(QTextFormat.Property.FontPointSize)
            or (size is not None and size != NOTE_BODY_PX))


def note_is_rich(doc):
    """Whether ``doc`` holds anything plain text would lose."""
    block = doc.begin()
    while block.isValid():
        if block.blockFormat().headingLevel() or any(
                styled_format(part.format) for part in block.textFormats()):
            return True
        block = block.next()
    return False


class NoteEdit(QTextEdit):
    """One note's editor: styled text, but only plain text gets pasted in.

    ``stored()`` is what goes into the settings table; it is only rebuilt once
    the document has changed, so loading a styled note and saving it again
    never produces a different string (which sync would read as an edit).
    """

    def __init__(self, parent=None):
        super().__init__(parent)
        self._stored = ""

    def load(self, stored):
        if stored.startswith(NOTE_RICH_PREFIX):
            self.setHtml(stored[len(NOTE_RICH_PREFIX):])
        else:
            self.setPlainText(stored)
        self._stored = stored
        self.document().setModified(False)

    def stored(self):
        doc = self.document()
        if doc.isModified():
            self._stored = (NOTE_RICH_PREFIX + doc.toHtml() if note_is_rich(doc)
                            else doc.toPlainText())
            doc.setModified(False)
        return self._stored

    def insertFromMimeData(self, source):
        # Clips carry other apps' fonts and colours; the pad's styles are its own.
        if source.hasText():
            self.insertPlainText(source.text())


# =============================================================================
#  Notepad tabs  (independent notes, each with its own title, colour and slot)
# =============================================================================
#
# A note lives in a *slot*: a small integer that never changes and that names
# its rows in the settings table. What the strip shows is a separate *order* -
# the slots left to right - so dragging a tab, adding one or closing one only
# rewrites that list and never moves anybody's text between keys.

HEX_COLOR = re.compile(r"^#[0-9a-fA-F]{6}$")


def note_key(base, slot):
    """The settings key for one note's slot.

    Slot 0 keeps the key the old single-note pad used, so an existing note
    simply turns up on the first tab instead of being left behind.
    """
    return base if slot == 0 else f"{base}_{slot + 1}"


def default_note_title(position):
    """Tabs are narrow, so an unnamed note is just its place in the strip."""
    return str(position + 1)


def default_note_color(slot):
    """Keyed to the slot, so a note keeps its colour when it's dragged."""
    return NOTE_COLORS[slot % len(NOTE_COLORS)][1]


def clean_note_title(raw, position):
    """One trimmed line, capped; nothing left means "back to the default"."""
    return raw_note_title(raw) or default_note_title(position)


def raw_note_title(raw):
    """A title as it is stored: trimmed and capped, or empty for "unnamed"."""
    return " ".join(str(raw or "").split())[:NOTE_TITLE_MAX]


def clean_note_color(raw, slot):
    """Only ``#rrggbb`` gets in: the settings table is editable by hand."""
    colour = str(raw or "").strip()
    return colour if HEX_COLOR.match(colour) else default_note_color(slot)


def clean_note_order(raw, limit=NOTE_MAX_COUNT):
    """The stored strip order, filtered down to sane, unique slot numbers.

    The settings table is hand-editable and survives downgrades, so anything
    unreadable falls back to the tabs a fresh pad would have shown.
    """
    try:
        slots = json.loads(raw)
    except (TypeError, ValueError):
        slots = None
    if not isinstance(slots, list):
        return list(range(NOTE_COUNT))
    order = []
    for slot in slots:
        if isinstance(slot, int) and not isinstance(slot, bool)                 and 0 <= slot < 1000 and slot not in order:
            order.append(slot)
    return order[:limit] or list(range(NOTE_COUNT))


def free_note_slot(taken):
    """The lowest slot nobody is using, so closed notes' keys get reused."""
    slot = 0
    while slot in taken:
        slot += 1
    return slot


def clean_notepad_width(raw):
    """A remembered pad width, clamped to what the window can actually show."""
    try:
        width = int(float(raw))
    except (TypeError, ValueError):
        return NOTEPAD_WIDTH
    return max(NOTEPAD_MIN_WIDTH, min(NOTEPAD_MAX_WIDTH, width))


def clean_window_size(raw, default, least, most):
    """A remembered window width or height, clamped to ``least..most``."""
    try:
        size = int(float(raw))
    except (TypeError, ValueError):
        return default
    return max(least, min(most, size))


def dragged_span(low, high, direction, travel, least, most, bound_low, bound_high):
    """One axis of an edge drag: move an end of ``low..high`` (inclusive) by ``travel``.

    ``direction`` picks the end: -1 moves ``low``, 1 moves ``high``, 0 neither.
    The moving end stops at the screen's bounds and the length stays within
    ``least..most``; the other end never moves.
    """
    if direction < 0:
        low = max(bound_low, low + travel)
        low = high + 1 - max(least, min(most, high + 1 - low))
    elif direction > 0:
        high = min(bound_high, high + travel)
        high = low - 1 + max(least, min(most, high + 1 - low))
    return low, high


def mix(colour, other, weight):
    """``colour`` blended ``weight`` of the way over ``other``, as ``#rrggbb``."""
    a, b = QColor(colour), QColor(other)
    channels = [round(x * weight + y * (1 - weight)) for x, y in (
        (a.red(), b.red()), (a.green(), b.green()), (a.blue(), b.blue())
    )]
    return QColor(*channels).name()


def swatch(colour, size=12):
    """A filled square icon, for the colour entries in a tab's menu."""
    pixmap = QPixmap(size, size)
    pixmap.fill(QColor(colour))
    return QIcon(pixmap)


def note_tab_style(colour, active):
    """One tab's stylesheet: its colour underlines it, brighter when open."""
    underline = colour if active else mix(colour, "#1b1f27", 0.45)
    return (
        "QToolButton#noteTab { border:none; padding:4px 2px 5px 2px;"
        "  border-top-left-radius:6px; border-top-right-radius:6px;"
        f"  font-size:11px; border-bottom:2px solid {underline};"
        f"  background:{'#2a2f3a' if active else 'transparent'};"
        f"  color:{'#e8eaed' if active else '#7d838f'};"
        f"  font-weight:{'600' if active else '400'}; }}"
        "QToolButton#noteTab:hover { background:#232834; color:#e8eaed; }"
    )


def note_editor_style(colour):
    """One note's editor, tinted so the note you're typing in is obvious."""
    border = mix(colour, "#3a414f", 0.30)
    selection = mix(colour, "#1b1f27", 0.40)
    return (
        f"QTextEdit#notes {{ border:1px solid {border};"
        f"  selection-background-color:{selection}; }}"
        f"QTextEdit#notes:focus {{ border:1px solid {colour}; }}"
    )


class NoteTab(QToolButton):
    """One tab above the notepad.

    Click switches note, double-click renames, middle-click closes, and
    dragging sideways reorders the strip - the tab is moved under the cursor
    as you go, so there is nothing to drop and nothing to undo if you stop.
    """

    rename_requested = Signal()
    close_requested = Signal()
    drag_moved = Signal(QPoint)
    drag_finished = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("noteTab")
        self.setCheckable(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)  # typing stays in the note
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.setMinimumWidth(NOTE_TAB_MIN_WIDTH)  # narrower, and the strip scrolls
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self._caption = ""
        self._press = None
        self._dragging = False

    # ---- caption -----------------------------------------------------------

    def setCaption(self, text):
        """Set the title, shortened with an ellipsis if the tab is too narrow."""
        self._caption = text
        super().setText(self._fitted(text))

    def caption(self):
        return self._caption

    def _fitted(self, text):
        room = self.width() - 8
        if room <= 0:  # not laid out yet: nothing to measure against
            return text
        metrics = QFontMetrics(self.font())
        if metrics.horizontalAdvance(text) <= room:
            return text
        return metrics.elidedText(text, Qt.TextElideMode.ElideRight, max(room, 12))

    def resizeEvent(self, event):
        super().resizeEvent(event)
        super().setText(self._fitted(self._caption))

    # ---- mouse -------------------------------------------------------------

    def mouseDoubleClickEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.rename_requested.emit()
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.MiddleButton:
            self.close_requested.emit()
            event.accept()
            return
        if event.button() == Qt.MouseButton.LeftButton:
            self._press = event.globalPosition().toPoint()
            self._dragging = False
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._press is not None and event.buttons() & Qt.MouseButton.LeftButton:
            here = event.globalPosition().toPoint()
            if not self._dragging:
                travelled = (here - self._press).manhattanLength()
                self._dragging = travelled >= QApplication.startDragDistance()
            if self._dragging:
                self.drag_moved.emit(here)
                event.accept()
                return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        dragged = self._dragging
        self._press, self._dragging = None, False
        super().mouseReleaseEvent(event)  # a release on the tab still selects it
        if dragged:
            self.drag_finished.emit()


class NoteTabStrip(QScrollArea):
    """The row of tabs: the wheel cycles notes, and it scrolls once they overflow.

    Tabs share the pad's width until they hit ``NOTE_TAB_MIN_WIDTH``; past that
    the strip slides instead, and switching note scrolls the new tab into view.
    """

    cycle_requested = Signal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("noteTabs")
        self.setWidgetResizable(True)
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.strip = QWidget()
        self.strip.setObjectName("noteTabsInner")
        self.setWidget(self.strip)
        self._keep_visible = None

    def keep_visible(self, tab):
        """Scroll ``tab`` into view, and keep it there as the pad is resized."""
        self._keep_visible = tab
        self.ensureWidgetVisible(tab, 0, 0)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if self._keep_visible is not None:
            self.ensureWidgetVisible(self._keep_visible, 0, 0)

    def wheelEvent(self, event):
        step = event.angleDelta().y()
        if step:
            self.cycle_requested.emit(-1 if step > 0 else 1)
            event.accept()
            return
        super().wheelEvent(event)


class WindowDragHandle(QLabel):
    """A dedicated move handle, so dragging never steals text or tab gestures."""

    def __init__(self, parent=None):
        super().__init__("⠿  Drag to move", parent)
        self.setObjectName("windowDrag")
        self.setCursor(Qt.CursorShape.OpenHandCursor)
        self.setToolTip("Drag to move the window in any mode")
        self._offset = None

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._offset = event.globalPosition().toPoint() - self.window().pos()
            self.setCursor(Qt.CursorShape.ClosedHandCursor)
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._offset is not None and event.buttons() & Qt.MouseButton.LeftButton:
            self.window().move(event.globalPosition().toPoint() - self._offset)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton and self._offset is not None:
            self._offset = None
            self.setCursor(Qt.CursorShape.OpenHandCursor)
            event.accept()
            return
        super().mouseReleaseEvent(event)


class WindowEdgeGrip(QWidget):
    """An invisible strip along one side or corner of the frameless window.

    Dragging it resizes the window from that side while the opposite side
    stays put, as a normal window border would. ``side`` is ``(dx, dy)``:
    -1 for the left/top, 1 for the right/bottom, 0 for neither.
    """

    drag_started = Signal()
    dragged = Signal(QPoint)   # cursor travel since the grip was grabbed
    drag_finished = Signal()

    def __init__(self, dx, dy, parent):
        super().__init__(parent)
        self.side = (dx, dy)
        if dx and dy:
            shape = (Qt.CursorShape.SizeFDiagCursor if dx == dy
                     else Qt.CursorShape.SizeBDiagCursor)
        else:
            shape = Qt.CursorShape.SizeHorCursor if dx else Qt.CursorShape.SizeVerCursor
        self.setCursor(shape)
        self._origin = None

    def place(self):
        """Hug this grip's side of the window; called whenever the window resizes."""
        dx, dy = self.side
        thickness = WINDOW_CORNER if dx and dy else WINDOW_EDGE
        window = self.parentWidget()
        x, width = self._span(dx, window.width(), thickness)
        y, height = self._span(dy, window.height(), thickness)
        self.setGeometry(x, y, width, height)

    @staticmethod
    def _span(direction, length, thickness):
        """Start and size along one axis: against an end, or between the corners."""
        if direction < 0:
            return 0, thickness
        if direction > 0:
            return length - thickness, thickness
        return WINDOW_CORNER, max(0, length - 2 * WINDOW_CORNER)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._origin = event.globalPosition().toPoint()
            self.drag_started.emit()
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._origin is not None:
            self.dragged.emit(event.globalPosition().toPoint() - self._origin)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._origin is not None and event.button() == Qt.MouseButton.LeftButton:
            self._origin = None
            self.drag_finished.emit()
            event.accept()
            return
        super().mouseReleaseEvent(event)


class NoteResizeGrip(QWidget):
    """The grip down the pad's left edge; dragging it sets the pad's width.

    The window grows leftwards as the pad widens, so the grip stays under the
    cursor instead of sliding away from it. Double-click returns to the default.
    """

    drag_started = Signal()
    dragged = Signal(int)      # pixels moved since the grip was grabbed
    drag_finished = Signal()
    reset_requested = Signal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("noteGrip")
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setFixedWidth(NOTE_GRIP_WIDTH)
        self.setCursor(Qt.CursorShape.SizeHorCursor)
        self.setToolTip("Drag to resize the notepad  (double-click to reset)")
        self._origin = None

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._origin = event.globalPosition().toPoint().x()
            self.drag_started.emit()
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._origin is not None:
            self.dragged.emit(event.globalPosition().toPoint().x() - self._origin)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._origin is not None and event.button() == Qt.MouseButton.LeftButton:
            self._origin = None
            self.drag_finished.emit()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def mouseDoubleClickEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._origin = None
            self.reset_requested.emit()
            event.accept()
            return
        super().mouseDoubleClickEvent(event)


class NoteTitleEdit(QLineEdit):
    """Inline rename box: Enter or clicking away commits, Esc leaves it alone."""

    committed = Signal(str)
    cancelled = Signal()

    def __init__(self, text, parent):
        super().__init__(text, parent)
        self.setObjectName("noteRename")
        self.setMaxLength(NOTE_TITLE_MAX)
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._done = False
        self.returnPressed.connect(self.commit)

    def commit(self):
        self._finish(self.committed, self.text())

    def _finish(self, signal, *args):
        if self._done:  # losing focus follows Enter/Esc; only finish once
            return
        self._done = True
        signal.emit(*args)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self._finish(self.cancelled)  # the popup itself stays open
            event.accept()
            return
        super().keyPressEvent(event)

    def focusOutEvent(self, event):
        super().focusOutEvent(event)
        self.commit()


class NoteSyncJournal:
    """Immutable, content-addressed note revisions. No clocks or shared writes.

    A deletion is a revision too. Parent links distinguish an offline edit from
    a stale copy, and concurrent edits produce deterministic recovery notes.
    Clipboard data and machine-specific preferences never enter this journal.
    """

    MAX_FILE_BYTES = 8 * 1024 * 1024
    MAX_TOTAL_BYTES = 128 * 1024 * 1024
    MAX_EVENTS = 25000

    @staticmethod
    def encode(value):
        return json.dumps(value, sort_keys=True, ensure_ascii=False,
                          separators=(",", ":")).encode("utf-8")

    @classmethod
    def revision(cls, note, parents, data):
        event = {"schema": 1, "note": note, "parents": sorted(parents), "data": data}
        event["id"] = hashlib.sha256(cls.encode(event)).hexdigest()
        return event

    @classmethod
    def validate(cls, event):
        if not isinstance(event, dict) or set(event) != {"schema", "id", "note", "parents", "data"}:
            raise ValueError("Unrecognized note revision; the original files were kept.")
        if event["schema"] != 1 or not re.fullmatch(r"[0-9a-f]{32}", str(event["note"])):
            raise ValueError("Unsupported note revision.")
        parents = event["parents"]
        if (not isinstance(parents, list) or len(parents) > cls.MAX_EVENTS
                or any(not isinstance(p, str) or not re.fullmatch(r"[0-9a-f]{64}", p) for p in parents)
                or len(parents) != len(set(parents))):
            raise ValueError("Invalid note revision history.")
        data = event["data"]
        if data is not None:
            if (not isinstance(data, dict) or set(data) != {"text", "title", "color", "position"}
                    or not all(isinstance(data.get(k), str) for k in ("text", "title", "color"))
                    or not HEX_COLOR.fullmatch(data["color"])
                    or type(data["position"]) is not int or not 0 <= data["position"] < 1000
                    or len(data["title"]) > NOTE_TITLE_MAX):
                raise ValueError("Invalid note content; the original files were kept.")
        if cls.revision(event["note"], parents, data) != event:
            raise ValueError("A note revision is damaged; the original files were kept.")
        return event

    @classmethod
    def heads(cls, events):
        groups, superseded = {}, set()
        for key, event in events.items():
            if key != event["id"]:
                raise ValueError("Invalid revision identifier.")
            for parent in event["parents"]:
                if parent not in events:
                    raise ValueError("Waiting for the desktop app to download the rest of the notes.")
                if events[parent]["note"] != event["note"]:
                    raise ValueError("Invalid note ancestry.")
                superseded.add(parent)
            groups.setdefault(event["note"], []).append(key)
        return {note: sorted(k for k in keys if k not in superseded)
                for note, keys in groups.items()}

    @classmethod
    def reconcile(cls, original):
        """Merge independently edited notes; retain both contents on a conflict."""
        events = dict(original)
        for note, heads in cls.heads(events).items():
            if len(heads) <= 1:
                continue
            live = [events[key] for key in heads if events[key]["data"] is not None]
            # An edit concurrent with a deletion wins, preserving the edited note.
            winner = live[0]["data"] if live else None
            contents = set()
            for event in live:
                data = event["data"]
                content = cls.encode({k: v for k, v in data.items() if k != "position"})
                if content in contents:
                    continue
                contents.add(content)
                if len(contents) == 1:
                    continue
                # Every PC derives the same ID, so retrying cannot duplicate a copy.
                copy_id = hashlib.sha256(("conflict:" + event["id"]).encode()).hexdigest()[:32]
                copy_data = dict(data)
                copy_data["title"] = (data["title"] or "Note")[:5] + " (copy)"
                copy_event = cls.revision(copy_id, [], copy_data)
                events.setdefault(copy_event["id"], copy_event)
            merged = cls.revision(note, heads, winner)
            events[merged["id"]] = merged
        notes = {}
        for note, heads in cls.heads(events).items():
            if len(heads) != 1:
                raise ValueError("The note history could not be merged safely.")
            data = events[heads[0]]["data"]
            if data is not None:
                notes[note] = data
        if len(notes) >= 1000:
            raise ValueError("Too many synced notes to display safely.")
        return events, notes

    @classmethod
    def exchange(cls, folder, local, cancelled, cache):
        """Runs only on a worker thread. Atomic files; never share the SQLite DB."""
        if not os.path.isdir(folder):
            raise OSError("The selected folder is unavailable. Reconnect the drive or choose another folder.")
        destination = os.path.join(folder, NOTE_SYNC_FOLDER, "revisions")
        os.makedirs(destination, exist_ok=True)
        events = dict(local)
        present, total = set(), 0
        with os.scandir(destination) as entries:
            for entry in entries:
                if cancelled.is_set():
                    return None
                if not entry.name.endswith(".json"):
                    continue  # unfinished atomic writes are never imported
                if not re.fullmatch(r"[0-9a-f]{64}\.json", entry.name):
                    raise ValueError("An unexpected revision file needs review in the sync folder.")
                stat = entry.stat()
                total += stat.st_size
                if (stat.st_size > cls.MAX_FILE_BYTES or total > cls.MAX_TOTAL_BYTES
                        or len(present) >= cls.MAX_EVENTS):
                    raise ValueError("The sync history is too large. Choose a new folder to start a fresh history.")
                stamp = (stat.st_size, stat.st_mtime_ns)
                cached = cache.get(entry.name)
                if cached and cached[0] == stamp:
                    event = cached[1]
                else:
                    with open(entry.path, "rb") as source:
                        raw = source.read(cls.MAX_FILE_BYTES + 1)
                    if len(raw) > cls.MAX_FILE_BYTES:
                        raise ValueError("A note revision is too large.")
                    event = cls.validate(json.loads(raw))
                    cache[entry.name] = (stamp, event)
                if entry.name != event["id"] + ".json":
                    raise ValueError("A revision filename does not match its content.")
                events[event["id"]] = event
                present.add(event["id"])
        cls.heads(events)  # wait for complete histories before applying or publishing
        outgoing = {key: cls.encode(event) for key, event in local.items() if key not in present}
        if len(events) > cls.MAX_EVENTS or total + sum(map(len, outgoing.values())) > cls.MAX_TOTAL_BYTES:
            raise ValueError("The sync history is too large. Choose a new folder to start a fresh history.")
        for key, event in local.items():
            if cancelled.is_set():
                return None
            if key in present:
                continue
            raw = outgoing[key]
            if len(raw) > cls.MAX_FILE_BYTES:
                raise ValueError("A note is too large to sync; it is still saved locally.")
            fd, temporary = tempfile.mkstemp(prefix=".pyclip-", suffix=".tmp", dir=destination)
            try:
                with os.fdopen(fd, "wb") as target:
                    target.write(raw)
                    target.flush()
                    os.fsync(target.fileno())
                if cancelled.is_set():
                    return None
                os.replace(temporary, os.path.join(destination, key + ".json"))
            finally:
                if os.path.exists(temporary):
                    os.unlink(temporary)
        return events


class NoteSyncController(QObject):
    completed = Signal(int, object, str)
    status_changed = Signal(str)

    def __init__(self, window):
        super().__init__(window)
        self.window, self.db = window, window.db
        self.events, self.baseline, self.config = {}, {}, {"provider": "local", "folder": ""}
        self.status = "Local only"
        self.busy = False
        self.generation = 0
        self.cancelled = threading.Event()
        self.cache = {}
        self.pending = None
        self.stopped = False
        self.load_error = False
        self.initialized = False
        try:
            config = json.loads(self.db.get_setting(NOTE_SYNC_CONFIG_KEY, "{}"))
            if (not isinstance(config, dict)
                    or config.get("provider", "local") not in ("local", "google", "dropbox", "folder")
                    or not isinstance(config.get("folder", ""), str)):
                raise ValueError("Invalid sync configuration.")
            self.config.update(config)
            state = json.loads(self.db.get_setting(NOTE_SYNC_STATE_KEY, "{}"))
            self.events = state.get("events", {})
            self.baseline = state.get("baseline", {})
            self.initialized = bool(state)
            for event in self.events.values():
                NoteSyncJournal.validate(event)
            NoteSyncJournal.heads(self.events)
            if not isinstance(self.baseline, dict):
                raise ValueError("Invalid local sync state.")
            for note, data in self.baseline.items():
                if data is None:
                    raise ValueError("Invalid local note snapshot.")
                NoteSyncJournal.validate(NoteSyncJournal.revision(note, [], data))
        except (ValueError, TypeError, AttributeError):
            self.load_error = True
            self.set_status("Local sync history needs repair; notes are saved locally")
        self.timer = QTimer(self)
        self.timer.setInterval(NOTE_SYNC_INTERVAL_MS)
        self.timer.timeout.connect(self.sync_now)
        self.debounce = QTimer(self)
        self.debounce.setSingleShot(True)
        self.debounce.setInterval(1200)
        self.debounce.timeout.connect(self.sync_now)
        self.apply_timer = QTimer(self)
        self.apply_timer.setSingleShot(True)
        self.apply_timer.setInterval(1000)
        self.apply_timer.timeout.connect(self.apply_pending)
        self.completed.connect(self.receive)
        if self.enabled:
            self.timer.start()
            self.debounce.start()

    @property
    def enabled(self):
        return self.config.get("provider") in ("google", "dropbox", "folder") and bool(self.config.get("folder"))

    def set_status(self, text):
        self.status = text
        self.status_changed.emit(text)

    def capture(self):
        """Capture on the GUI thread; the worker never touches widgets or SQLite."""
        if self.load_error:
            return
        current = self.window._note_snapshot()
        if not self.initialized:
            self.baseline = {}
            # Do not add five unused starter tabs when joining an existing folder.
            seed = self.window._notes_to_seed(current)
        else:
            seed = current
        heads = NoteSyncJournal.heads(self.events)
        updated = dict(self.events)
        for note in set(seed) | set(self.baseline):
            data = seed.get(note)
            if data == self.baseline.get(note):
                continue
            if data is None and note not in heads:
                continue
            event = NoteSyncJournal.revision(note, heads.get(note, []), data)
            updated[event["id"]] = event
        if updated != self.events or current != self.baseline or not self.initialized:
            # Do not advance the in-memory base unless the disk commit succeeds.
            self.db.set_setting(NOTE_SYNC_STATE_KEY, json.dumps(
                {"events": updated, "baseline": current}, ensure_ascii=False))
            self.events, self.baseline = updated, current
            self.initialized = True

    def changed(self):
        if self.enabled and not self.stopped:
            self.debounce.start()

    def configure(self, provider, folder):
        if not self.window.save_notes():
            raise sqlite3.OperationalError("The current note could not be saved locally.")
        if self.initialized and not self.load_error:
            self.capture()
        if provider == "local" and not folder:
            folder = self.config.get("folder", "")
        config = {"provider": provider, "folder": folder}
        # A different folder starts with just the current notes, not old/deleted history.
        different = (provider != "local" and os.path.normcase(folder) != os.path.normcase(self.config.get("folder", "")))
        if different and not self.load_error:
            current = self.window._note_snapshot()
            events = {}
            for note, data in self.window._notes_to_seed(current).items():
                event = NoteSyncJournal.revision(note, [], data)
                events[event["id"]] = event
            state = json.dumps({"events": events, "baseline": current}, ensure_ascii=False)
        else:
            state = None
        with self.db.conn:
            self.db.conn.execute("INSERT OR REPLACE INTO settings VALUES (?, ?)",
                                 (NOTE_SYNC_CONFIG_KEY, json.dumps(config)))
            if state is not None:
                self.db.conn.execute("INSERT OR REPLACE INTO settings VALUES (?, ?)",
                                     (NOTE_SYNC_STATE_KEY, state))
        if state is not None:
            self.events, self.baseline, self.initialized = events, current, True
        self.cancelled.set()
        self.cancelled = threading.Event()
        self.generation += 1
        self.config = config
        self.cache = {}
        self.pending = None
        self.timer.stop()
        self.debounce.stop()
        self.apply_timer.stop()
        if self.enabled:
            self.set_status("Saved locally · waiting for folder")
            self.timer.start()
            self.debounce.start()
        else:
            self.set_status("Local only")

    def sync_now(self):
        if self.stopped or self.load_error or not self.enabled:
            return
        if self.busy or self.pending is not None:
            return
        try:
            if not self.window.save_notes():
                raise sqlite3.OperationalError("The current note could not be saved locally.")
            self.capture()
        except (sqlite3.Error, ValueError):
            self.set_status("Could not save sync history · retrying")
            return
        self.busy = True
        generation, cancelled = self.generation, self.cancelled
        folder, events, cache = self.config["folder"], dict(self.events), self.cache
        self.set_status("Updating sync folder…")

        def work():
            result, error = None, ""
            try:
                result = NoteSyncJournal.exchange(folder, events, cancelled, cache)
            except (OSError, ValueError, TypeError, RecursionError) as exc:
                error = str(exc)
            try:
                # Also release busy after cancellation / an in-flight folder change.
                self.completed.emit(generation, result, error)
            except RuntimeError:
                pass  # the owning window was destroyed during application shutdown

        threading.Thread(target=work, name="PyClipNoteSync", daemon=True).start()

    def receive(self, generation, events, error):
        self.busy = False
        if self.stopped or generation != self.generation or not self.enabled:
            return
        if error:
            self.set_status("Saved locally · " + error)
            return
        if events is None:
            return
        self.pending = events
        self.apply_pending()

    def apply_pending(self):
        if self.pending is None or self.stopped:
            return
        # Wait for a typing pause / rename dialog rather than replacing an editor mid-edit.
        if (self.window._note_timer.isActive() or self.window._menu_open
                or isinstance(QApplication.focusWidget(), NoteTitleEdit)
                or QApplication.activeModalWidget() is not None
                or QApplication.mouseButtons() != Qt.MouseButton.NoButton):
            self.apply_timer.start()
            return
        try:
            if not self.window.save_notes():
                raise sqlite3.OperationalError("The current note could not be saved locally.")
            self.capture()  # includes edits made while the folder worker was running
            events, notes = NoteSyncJournal.reconcile({**self.pending, **self.events})
            if notes:
                self.window._apply_synced_notes(notes, events)
                self.baseline = self.window._note_snapshot()
            else:
                # All remote notes were deleted: retain one empty local scratch pad.
                if self.events or self.pending:
                    self.window._apply_synced_notes({}, events)
                    self.baseline = self.window._note_snapshot()
            self.events = events
            unpublished = bool(set(events) - set(self.pending))
            self.pending = None
            if unpublished:
                self.set_status("Saved locally · updating recent changes")
                self.debounce.start()
            else:
                self.set_status("Folder updated " + time.strftime("%H:%M") + " · cloud sync by desktop app")
        except (sqlite3.Error, ValueError) as exc:
            self.pending = None
            self.set_status("Saved locally · " + str(exc))

    def stop(self):
        saved = self.window.save_notes()
        if saved and self.initialized and not self.load_error:
            try:
                self.capture()
            except (sqlite3.Error, ValueError):
                logger.exception("Could not save local note sync state at shutdown")
        self.stopped = True
        self.cancelled.set()
        self.timer.stop()
        self.debounce.stop()
        self.apply_timer.stop()


class NoteSyncDialog(QDialog):
    def __init__(self, controller, parent):
        super().__init__(parent)
        self.controller = controller
        self.setWindowTitle("Note sync")
        self.setMinimumWidth(470)
        self.setStyleSheet("""
            QDialog { background:#1b1f27; }
            QLabel { color:#d4d9e2; }
            QPushButton, QComboBox { background:#2a2f3a; color:#e8eaed;
                border:1px solid #465061; border-radius:5px; padding:7px 10px; }
            QPushButton:hover, QComboBox:hover { border-color:#4c8bf5; }
            QPushButton:disabled, QLineEdit:disabled { color:#7d838f; }
            QComboBox QAbstractItemView { background:#2a2f3a; color:#e8eaed;
                selection-background-color:#33405a; }
        """)
        box = QVBoxLayout(self)
        intro = QLabel("Notes always save on this PC first. Choose an optional synced folder to share them across your PCs.")
        intro.setWordWrap(True)
        box.addWidget(intro)
        self.provider = QComboBox()
        for title, key in (("Local only (default)", "local"), ("Google Drive folder", "google"),
                           ("Dropbox folder", "dropbox"), ("Other synced folder", "folder")):
            self.provider.addItem(title, key)
        self.provider.setCurrentIndex(max(0, self.provider.findData(controller.config.get("provider"))))
        box.addWidget(self.provider)
        self.help = QLabel()
        self.help.setWordWrap(True)
        box.addWidget(self.help)
        self.setup = QPushButton("Desktop app setup")
        self.setup.clicked.connect(self.open_setup)
        box.addWidget(self.setup)
        row = QHBoxLayout()
        self.folder = QLineEdit(controller.config.get("folder", ""))
        self.folder.setPlaceholderText("Choose a folder in your signed-in desktop app")
        self.browse = QPushButton("Choose folder…")
        self.browse.clicked.connect(self.choose_folder)
        row.addWidget(self.folder, 1)
        row.addWidget(self.browse)
        box.addLayout(row)
        details = QLabel("PyClip creates a ‘PyClip Notes’ subfolder. Select the same folder on each PC and keep it available offline. Only notes, titles, colours and tab order are shared. Conflicting edits are kept as separate copies.")
        details.setWordWrap(True)
        box.addWidget(details)
        self.status = QLabel(controller.status)
        self.status.setWordWrap(True)
        controller.status_changed.connect(self.status.setText)
        box.addWidget(self.status)
        actions = QHBoxLayout()
        self.sync = QPushButton("Sync now")
        self.sync.setEnabled(controller.enabled)
        self.sync.clicked.connect(controller.sync_now)
        actions.addWidget(self.sync)
        actions.addStretch()
        box.addLayout(actions)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.save)
        buttons.rejected.connect(self.reject)
        box.addWidget(buttons)
        self.provider.currentIndexChanged.connect(self.update_provider)
        self.update_provider()

    def update_provider(self, *_):
        provider = self.provider.currentData()
        self.folder.setEnabled(provider != "local")
        self.browse.setEnabled(provider != "local")
        self.setup.setVisible(provider in ("google", "dropbox"))
        self.help.setText({
            "local": "Notes stay on this PC. Turning sync off keeps your local notes and existing cloud files.",
            "google": "Sign in to Google Drive for desktop, then choose a folder from that account. This syncs PyClip notes, not Google Keep.",
            "dropbox": "Sign in to the Dropbox desktop app, then choose a folder from that account.",
            "folder": "Choose a folder managed by your sync app or a shared drive.",
        }[provider])

    def open_setup(self):
        url = ("https://support.google.com/drive/answer/10838124" if self.provider.currentData() == "google"
               else "https://www.dropbox.com/desktop")
        QDesktopServices.openUrl(QUrl(url))

    def choose_folder(self):
        selected = QFileDialog.getExistingDirectory(self, "Choose your synced notes folder", self.folder.text())
        if selected:
            self.folder.setText(selected)

    def save(self):
        provider, folder = self.provider.currentData(), self.folder.text().strip()
        if provider != "local" and not os.path.isabs(folder):
            self.status.setText("Choose an absolute folder path before enabling sync.")
            return
        try:
            self.controller.configure(provider, os.path.normpath(folder) if folder else "")
        except (sqlite3.Error, ValueError) as exc:
            self.status.setText("Could not save sync settings: " + str(exc))
            return
        self.accept()


class HistoryWindow(QWidget):
    paste_requested = Signal(list)  # list of clip ids (display order)
    copy_requested = Signal(list)
    directory_copy_requested = Signal(str)

    BASE_WIDTH = 440
    BASE_HEIGHT = 560
    COLUMN_GAP = 8

    # Ctrl+Shift+8/7/9 as in Word and Docs. Windows reports the shifted key on
    # some layouts and the digit on others, so both spellings are accepted.
    LIST_KEYS = {
        "bullet": (Qt.Key.Key_8, Qt.Key.Key_Asterisk),
        "number": (Qt.Key.Key_7, Qt.Key.Key_Ampersand),
        "todo":   (Qt.Key.Key_9, Qt.Key.Key_ParenLeft),
    }
    # Ctrl+Alt+digit, as in Word: Normal, then Heading 1-3
    HEADING_KEYS = {Qt.Key.Key_0: 0, Qt.Key.Key_1: 1, Qt.Key.Key_2: 2, Qt.Key.Key_3: 3}

    def __init__(self, db):
        super().__init__()
        self.db = db
        self.prev_hwnd = 0
        self._menu_open = False
        self._ignore_deactivate = False
        self._notes_open = False
        self._notepad_pinned = False  # notepad-only, always-on-top mode
        self._notepad_width = NOTEPAD_WIDTH
        self._resize_origin = None
        self._edge_origin = None      # window geometry when an edge was grabbed
        self._edge_grips = []
        self._dir_open = False        # the folder panel (DIR or FAV) is showing
        self._dir_fav = False         # ... and it is listing favourites only

        self.setObjectName("root")
        self.setWindowTitle("PyClip")
        self.setWindowFlags(
            Qt.WindowType.FramelessWindowHint
            | Qt.WindowType.Tool
            | Qt.WindowType.WindowStaysOnTopHint
        )
        # The clip list's width is what the window is with the pad closed.
        desktop = QGuiApplication.primaryScreen().availableVirtualGeometry()
        self._history_width = clean_window_size(
            db.get_setting(HISTORY_WIDTH_KEY, ""), self.BASE_WIDTH,
            HISTORY_MIN_WIDTH, desktop.width())
        self.resize(self._history_width, clean_window_size(
            db.get_setting(WINDOW_HEIGHT_KEY, ""), self.BASE_HEIGHT,
            WINDOW_MIN_HEIGHT, desktop.height()))
        self._build_ui()
        self._build_edge_grips()
        self._apply_style()
        # Let the tab row span the search row so the pad lines up with the list.
        self.search.ensurePolished()
        row_height = self.search.sizeHint().height()
        self._tabs_row.setFixedHeight(row_height)
        self._note_add.setFixedHeight(row_height)
        self._dir_tab.setFixedHeight(row_height)
        self._fav_tab.setFixedHeight(row_height)
        self._restore_notepad()
        self.note_sync = NoteSyncController(self)
        self.note_sync.status_changed.connect(self._sync_status_changed)
        self._sync_status_changed(self.note_sync.status)

    def _build_ui(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(10, 10, 10, 8)
        layout.setSpacing(6)

        self._drag_handle = WindowDragHandle()
        layout.addWidget(self._drag_handle)

        columns = QHBoxLayout()
        columns.setSpacing(self.COLUMN_GAP)
        layout.addLayout(columns, 1)

        self.history_panel = QWidget()
        history = QVBoxLayout(self.history_panel)
        history.setContentsMargins(0, 0, 0, 0)
        history.setSpacing(8)
        columns.addWidget(self.history_panel)

        top = QHBoxLayout()
        top.setSpacing(6)
        history.addLayout(top)

        self.search = QLineEdit()
        self.search.setPlaceholderText("Search clipboard…   (Esc to close)")
        self.search.textChanged.connect(self.reload)
        self.search.installEventFilter(self)
        top.addWidget(self.search)

        self.notes_toggle = QToolButton()
        self.notes_toggle.setObjectName("notesToggle")
        self.notes_toggle.setToolButtonStyle(
            Qt.ToolButtonStyle.ToolButtonTextOnly
        )
        self.notes_toggle.setCheckable(True)
        self.notes_toggle.setToolTip("Notepad  (Ctrl+N)")
        self.notes_toggle.setCursor(Qt.CursorShape.PointingHandCursor)
        self.notes_toggle.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.notes_toggle.clicked.connect(self._toggle_notepad)
        top.addWidget(self.notes_toggle)

        self.list = QListWidget()
        self.list.setItemDelegate(ClipDelegate(self.list))
        self.list.setMouseTracking(True)
        self.list.setUniformItemSizes(True)
        self.list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.list.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.list.itemActivated.connect(self._paste_selected)
        self.list.installEventFilter(self)
        self.list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.list.customContextMenuRequested.connect(self._context_menu)
        history.addWidget(self.list)

        storage = QHBoxLayout()
        self.storage_label = hint_label("")
        storage.addWidget(self.storage_label, 1)
        self.cleanup_button = QToolButton()
        self.cleanup_button.setObjectName("dirAction")
        self.cleanup_button.setText("Clean ≥10 MB")
        self.cleanup_button.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.cleanup_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self.cleanup_button.setToolTip(
            "Remove saved clipboard entries of 10 MB or more, largest first.\n"
            + ("Pinned entries are kept.\n" if CLEANUP_KEEP_PINNED else
               "Includes pinned clipboard entries.\n")
            + "Original files, notes and DIR locations are kept."
        )
        self.cleanup_button.clicked.connect(self._clean_large_clips)
        storage.addWidget(self.cleanup_button)
        history.addLayout(storage)

        self.hint = hint_label(
            "Enter paste · Ctrl+C copy · Del remove · Shift/Ctrl-click many"
        )
        history.addWidget(self.hint)

        self.notepad = self._build_notepad()
        columns.addWidget(self.notepad)

    def _build_edge_grips(self):
        """Resize handles around the frameless window, inside its margins.

        Built after the rest of the UI so they sit on top of it.
        """
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                if not (dx or dy):
                    continue
                grip = WindowEdgeGrip(dx, dy, self)
                grip.drag_started.connect(self._edge_grabbed)
                grip.dragged.connect(lambda delta, g=grip: self._edge_dragged(g.side, delta))
                grip.drag_finished.connect(self._edge_released)
                self._edge_grips.append(grip)

    def _build_notepad(self):
        """A tabbed scratch pad beside the history, persisted the same way.

        The tabs themselves are built by :meth:`_restore_notepad`, which is what
        knows how many notes there are and in what order they were left.
        """
        self._note_timer = QTimer(self)
        self._note_timer.setSingleShot(True)
        self._note_timer.setInterval(NOTE_SAVE_DELAY_MS)
        self._note_timer.timeout.connect(self.save_notes)

        self._active_note = 0
        self._renumbering = False  # our own rewrite must not re-trigger itself
        self._note_slots = []     # settings slot behind each tab, in strip order
        self._note_ids = []       # portable identity, independent of local slot numbers
        self._note_titles = []    # as stored: empty means "use the position"
        self._note_colors = []
        self._saved_notes = []
        self._note_tabs = []
        self._note_edits = []

        panel = QWidget()
        panel.setObjectName("notepad")

        shell = QHBoxLayout(panel)
        shell.setContentsMargins(0, 0, 0, 0)
        shell.setSpacing(0)

        self._note_grip = NoteResizeGrip()
        self._note_grip.drag_started.connect(self._grip_grabbed)
        self._note_grip.dragged.connect(self._grip_dragged)
        self._note_grip.drag_finished.connect(self._grip_released)
        self._note_grip.reset_requested.connect(
            lambda: self._set_notepad_width(NOTEPAD_WIDTH, remember=True))
        shell.addWidget(self._note_grip)

        box = QVBoxLayout()
        box.setContentsMargins(0, 0, 0, 0)
        box.setSpacing(6)
        shell.addLayout(box)

        self._tabs_row = NoteTabStrip()
        self._tabs_row.cycle_requested.connect(self._cycle_note)
        tabs_layout = QHBoxLayout(self._tabs_row.strip)
        tabs_layout.setContentsMargins(0, 0, 0, 0)
        tabs_layout.setSpacing(2)

        self._note_add = QToolButton()
        self._note_add.setObjectName("noteAdd")
        self._note_add.setText("+")
        self._note_add.setCursor(Qt.CursorShape.PointingHandCursor)
        self._note_add.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self._note_add.setToolTip("New note  (Ctrl+T)")
        self._note_add.clicked.connect(self._add_note)

        self._dir_tab = QToolButton()
        self._dir_tab.setObjectName("noteTab")
        self._dir_tab.setText("DIR")
        self._dir_tab.setCheckable(True)
        self._dir_tab.setFixedWidth(40)
        self._dir_tab.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self._dir_tab.setCursor(Qt.CursorShape.PointingHandCursor)
        self._dir_tab.setToolTip("Search previously copied folder locations")
        self._dir_tab.clicked.connect(lambda: self._show_directories(favorites=False))

        self._fav_tab = QToolButton()
        self._fav_tab.setObjectName("noteTab")
        self._fav_tab.setText("FAV")
        self._fav_tab.setCheckable(True)
        self._fav_tab.setFixedWidth(40)
        self._fav_tab.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self._fav_tab.setCursor(Qt.CursorShape.PointingHandCursor)
        self._fav_tab.setToolTip("Favourite folders  (right-click a folder in DIR to add one)")
        self._fav_tab.clicked.connect(lambda: self._show_directories(favorites=True))

        self._pin_check = QCheckBox()
        self._pin_check.setObjectName("pinNotepad")
        self._pin_check.setCursor(Qt.CursorShape.PointingHandCursor)
        self._pin_check.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self._pin_check.setToolTip(
            "Notepad only, always on top\n(hides the clipboard list)")
        self._pin_check.toggled.connect(self._set_notepad_pinned)

        # The button sits outside the strip so it stays put once tabs overflow.
        tabs_bar = QHBoxLayout()
        tabs_bar.setContentsMargins(0, 0, 0, 0)
        tabs_bar.setSpacing(2)
        tabs_bar.addWidget(self._tabs_row, 1)
        tabs_bar.addWidget(self._dir_tab)
        tabs_bar.addWidget(self._fav_tab)
        tabs_bar.addWidget(self._pin_check)
        tabs_bar.addWidget(self._note_add)
        box.addLayout(tabs_bar)

        self._notes_stack = QStackedWidget()
        self.directory_panel = self._build_directory_panel()
        self._notes_stack.addWidget(self.directory_panel)
        box.addWidget(self._notes_stack)

        self._panel_hint = hint_label("")
        self._panel_keys = hint_label("")
        box.addWidget(self._panel_hint)
        box.addWidget(self._panel_keys)
        self._sync_button = QToolButton()
        self._sync_button.setText("Notes: Local only")
        self._sync_button.setStyleSheet("QToolButton { border:none; color:#9aa5b5; padding:2px; text-align:left; }")
        self._sync_button.setCursor(Qt.CursorShape.PointingHandCursor)
        self._sync_button.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self._sync_button.clicked.connect(self.show_note_sync)
        box.addWidget(self._sync_button)
        panel.setFixedWidth(self._notepad_width + NOTE_GRIP_WIDTH)
        return panel

    def _apply_style(self):
        self.setStyleSheet(
            """
            QWidget#root { background:#1b1f27; border:1px solid #3a414f; }
            QWidget { color:#e8eaed; font-family:'Segoe UI'; }
            QLineEdit { background:#2a2f3a; border:1px solid #3a414f;
                        border-radius:8px; padding:8px 10px; font-size:13px; }
            QLineEdit:focus { border:1px solid #4c8bf5; }
            QLineEdit#noteRename { padding:2px 4px; font-size:11px; border-radius:4px; }
            QListWidget { background:#1b1f27; border:none; outline:none; }
            QListWidget::item { border-bottom:1px solid #232834; }
            QLabel#hint { color:#6f7682; font-size:11px; padding-left:2px; }
            QLabel#windowDrag { color:#8a909c; font-size:11px; padding:4px 6px;
                               background:#242a36; border-radius:4px; }
            QLabel#windowDrag:hover { color:#e8eaed; background:#33405a; }
            QToolButton#notesToggle { background:#2a2f3a; border:1px solid #3a414f;
                                      border-radius:8px; padding:8px 9px;
                                      font-size:12px; color:#b9bfcb; }
            QToolButton#notesToggle:hover { border:1px solid #4c8bf5; color:#e8eaed; }
            QToolButton#notesToggle:checked { background:#33405a; color:#e8eaed; }
            QToolButton#noteAdd { background:transparent; border:none; color:#7d838f;
                                  font-size:15px; padding:0 6px 2px 6px;
                                  border-radius:6px; }
            QToolButton#noteAdd:hover { background:#232834; color:#e8eaed; }
            QToolButton#noteAdd:disabled { color:#454b57; background:transparent; }
            QToolButton#dirAction { background:#2a2f3a; border:1px solid #3a414f;
                                   border-radius:5px; padding:5px 8px; }
            QToolButton#dirAction:hover { border:1px solid #4c8bf5; }
            QToolButton#dirAction:disabled { color:#6f7682; }
            QScrollArea#noteTabs { background:transparent; border:none; }
            QWidget#noteTabsInner { background:transparent; }
            QWidget#noteGrip { background:#2a2f3a; margin:2px 3px; border-radius:1px; }
            QWidget#noteGrip:hover { background:#4c8bf5; }
            QCheckBox#pinNotepad { spacing:0; }
            QCheckBox#pinNotepad::indicator { width:13px; height:13px;
                border:1px solid #3a414f; border-radius:3px; background:#2a2f3a; }
            QCheckBox#pinNotepad::indicator:hover { border:1px solid #4c8bf5; }
            QCheckBox#pinNotepad::indicator:checked { background:#4c8bf5;
                border:1px solid #4c8bf5; }
            QTextEdit#notes { background:#2a2f3a; border:1px solid #3a414f;
                              border-radius:8px; padding:6px; font-size:12px;
                              selection-background-color:#33405a; }
            QTextEdit#notes:focus { border:1px solid #4c8bf5; }
            QMenu { background:#2a2f3a; border:1px solid #3a414f; padding:4px; }
            QMenu::item { padding:6px 22px; border-radius:4px; }
            QMenu::item:selected { background:#33405a; }
            QScrollBar:vertical { background:transparent; width:10px; margin:0; }
            QScrollBar::handle:vertical { background:#3a414f; border-radius:5px;
                                          min-height:30px; }
            QScrollBar::add-line, QScrollBar::sub-line { height:0; }
            """
        )

    def reload(self, *_):
        search = self.search.text().strip() or None
        self.list.clear()
        for clip in self.db.get_clips(search, include_content=False):
            item = QListWidgetItem()
            pm = None
            if clip["kind"] == "image" and clip["data"] and os.path.exists(clip["data"]):
                pm = load_thumbnail(clip["data"])
            size = clip_size_bytes(clip)
            item.setData(Qt.ItemDataRole.UserRole, {
                "id": clip["id"],
                "kind": clip["kind"],
                "primary": clip["preview"] or "",
                "meta": (f'{clip["kind"].capitalize()} · {format_size(size)}'
                         f' · {humanize(clip["created_at"])}'),
                "pinned": clip["pinned"],
            })
            size_basis = {
                "text": "Saved text (UTF-8)",
                "image": "Saved image (PNG)",
                "files": "Saved file references (not the files' contents)",
            }.get(clip["kind"], "Saved clipboard content")
            item.setToolTip(
                f"{size_basis}: {size:,} bytes" if size is not None
                else "Saved clipboard content: size unavailable"
            )
            item.setData(Qt.ItemDataRole.UserRole + 1, pm)
            self.list.addItem(item)
        if self.list.count():
            self.list.setCurrentRow(0)
        if self._dir_open:
            self._reload_directories()
        self._refresh_storage()

    def _refresh_storage(self):
        entries = self.db.storage_entries()
        total = sum(entry["size_bytes"] for entry in entries)
        self.storage_label.setText(f"History: {format_size(total)} / 500 MB")
        details = (f"Saved clipboard content: {total:,} bytes\n"
                   "Automatic cleanup removes the largest entries above 500 MB.\n"
                   "Counts text, saved PNG images and file references; excludes previews, "
                   "database overhead, notes and DIR locations.")
        if CLEANUP_KEEP_PINNED and total > HISTORY_MAX_BYTES:
            self.storage_label.setText(f"History: {format_size(total)} · pinned over limit")
            details += "\nPinned entries prevent further automatic cleanup."
        self.storage_label.setToolTip(details)
        self.cleanup_button.setEnabled(any(
            entry["size_bytes"] >= LARGE_CLIP_BYTES
            and not (CLEANUP_KEEP_PINNED and entry["pinned"])
            for entry in entries
        ))

    def _clean_large_clips(self, *_):
        result = self.db.clean_large_clips()
        self.reload()
        count = len(result["removed_ids"])
        self.cleanup_button.setToolTip(
            f"Removed {count} clipboard entries ({format_size(result['removed_bytes'])}).\n"
            "Clean ≥10 MB removes saved entries of 10 MB or more.\n"
            "Original files, notes and DIR locations are kept."
        )

    # ---- directory history ------------------------------------------------

    def _build_directory_panel(self):
        panel = QWidget()
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(6)
        self.dir_search = QLineEdit()
        self.dir_search.setPlaceholderText("Search folders or paths…")
        self.dir_search.setClearButtonEnabled(True)
        self.dir_search.textChanged.connect(self._reload_directories)
        self.dir_search.installEventFilter(self)
        layout.addWidget(self.dir_search)

        self.dir_list = QListWidget()
        self.dir_list.setItemDelegate(ClipDelegate(self.dir_list))
        self.dir_list.setUniformItemSizes(True)
        self.dir_list.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.dir_list.itemDoubleClicked.connect(self._copy_directory)
        self.dir_list.itemSelectionChanged.connect(self._directory_selection_changed)
        self.dir_list.installEventFilter(self)
        self.dir_list.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.dir_list.customContextMenuRequested.connect(self._directory_menu)
        layout.addWidget(self.dir_list, 1)

        self.dir_empty = QLabel()
        self.dir_empty.setWordWrap(True)
        self.dir_empty.setObjectName("hint")
        self.dir_empty.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)
        layout.addWidget(self.dir_empty)

        actions = QHBoxLayout()
        self.dir_open_button = QToolButton()
        self.dir_open_button.setText("Open")
        self.dir_open_button.setToolTip("Open the selected folder in Explorer (Enter)")
        self.dir_open_button.clicked.connect(self._open_directory)
        self.dir_copy_button = QToolButton()
        self.dir_copy_button.setText("Copy path")
        self.dir_copy_button.setToolTip("Copy the selected folder path (double-click or Ctrl+C)")
        self.dir_copy_button.clicked.connect(self._copy_directory)
        for button in (self.dir_open_button, self.dir_copy_button):
            button.setObjectName("dirAction")
            button.setCursor(Qt.CursorShape.PointingHandCursor)
            button.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            button.setEnabled(False)
            actions.addWidget(button)
        actions.addStretch()
        layout.addLayout(actions)
        self.dir_status = hint_label("")
        layout.addWidget(self.dir_status)
        return panel

    def _show_directories(self, favorites=False):
        """DIR and FAV share one panel; FAV just lists the pinned folders."""
        self.save_notes()
        self._dir_open = True
        self._dir_fav = favorites
        self._notes_stack.setCurrentWidget(self.directory_panel)
        self._refresh_note_tabs()
        self._remember(DIR_OPEN_KEY, "fav" if favorites else "1")
        self.dir_search.setPlaceholderText(
            "Search favourite folders…" if favorites else "Search folders or paths…")
        self._reload_directories()
        self.dir_search.setFocus()

    def _selected_directory(self):
        item = self.dir_list.currentItem()
        return (item.data(Qt.ItemDataRole.UserRole) or {}).get("path") if item else None

    def _directory_selection_changed(self):
        enabled = bool(self._selected_directory())
        self.dir_open_button.setEnabled(enabled)
        self.dir_copy_button.setEnabled(enabled)

    def _reload_directories(self, *_):
        selected = self._selected_directory()
        self.dir_list.clear()
        search = self.dir_search.text()
        if self._dir_fav:
            rows = [(row["path"], f'Added: {humanize(row["added_at"])}', True)
                    for row in self.db.get_favorites(search)]
        else:
            favorites = self.db.favorite_keys()
            rows = [(row["path"], f'Last used: {humanize(row["used_at"])}',
                     os.path.normcase(row["path"]) in favorites)
                    for row in self.db.get_directories(search)]
        for path, when, favorite in rows:
            name = os.path.basename(path) or path
            item = QListWidgetItem()
            item.setData(Qt.ItemDataRole.UserRole, {
                "kind": "directory", "path": path, "favorite": favorite,
                # the star marks favourites in DIR; in FAV every row is one
                "primary": f"★ {name}" if favorite and not self._dir_fav else name,
                "meta": path,
            })
            item.setToolTip(f"{path}\n{when}")
            self.dir_list.addItem(item)
            if path == selected:
                self.dir_list.setCurrentItem(item)
        if self.dir_list.count() and self.dir_list.currentRow() < 0:
            self.dir_list.setCurrentRow(0)
        self._directory_selection_changed()
        self.dir_empty.setVisible(not self.dir_list.count())
        if search.strip():
            self.dir_empty.setText("No matching folders.")
        elif self._dir_fav:
            self.dir_empty.setText(
                "No favourites yet. Right-click a folder in DIR and choose Add to Favourites.")
        else:
            self.dir_empty.setText(
                "Copy a folder, a file, or a full path to add its location here.")
        count = self.dir_list.count()
        self.dir_status.setText(
            f"{count} favourite{'' if count == 1 else 's'} · in the order added"
            if self._dir_fav else f"{count} folders · most recent first")
        self.dir_status.setToolTip("")

    def _open_directory(self, *_):
        path = self._selected_directory()
        if not path:
            return
        if not os.path.isdir(path):
            self.dir_status.setText("Folder unavailable. It may have moved or be offline.")
            self.dir_status.setToolTip(f"Folder unavailable. It may have moved or be offline.\n{path}")
            return
        if QDesktopServices.openUrl(QUrl.fromLocalFile(path)):
            self.db.remember_directories([path])
            self._reload_directories()
        else:
            self.dir_status.setText("Could not open this folder.")

    def _copy_directory(self, *_):
        path = self._selected_directory()
        if path:
            self.db.remember_directories([path])
            self.directory_copy_requested.emit(path)
            self._reload_directories()
            self.dir_status.setText("Folder path copied")

    def _directory_menu(self, pos):
        item = self.dir_list.itemAt(pos)
        if not item:
            return
        self.dir_list.setCurrentItem(item)
        self._menu_open = True
        menu = QMenu(self)
        if (item.data(Qt.ItemDataRole.UserRole) or {}).get("favorite"):
            menu.addAction("Remove from Favourites", self._unfavorite_directory)
        else:
            menu.addAction("Add to Favourites", self._favorite_directory)
        menu.addSeparator()
        menu.addAction("Open folder", self._open_directory)
        menu.addAction("Copy path", self._copy_directory)
        if not self._dir_fav:
            menu.addSeparator()
            menu.addAction("Remove from DIR", self._forget_directory)
        try:
            menu.exec(self.dir_list.mapToGlobal(pos))
        finally:
            self._menu_open = False

    def _forget_directory(self):
        """Delete: in FAV that unpins the folder, in DIR it drops it from history."""
        if self._dir_fav:
            self._unfavorite_directory()
            return
        path = self._selected_directory()
        if path:
            self.db.forget_directory(path)
            self._reload_directories()

    def _favorite_directory(self):
        path = self._selected_directory()
        if path:
            self.db.add_favorite(path)
            self._reload_directories()
            self.dir_status.setText("Added to Favourites")

    def _unfavorite_directory(self):
        path = self._selected_directory()
        if path:
            self.db.remove_favorite(path)
            self._reload_directories()
            self.dir_status.setText("Removed from Favourites")

    # ---- notepad -----------------------------------------------------------

    def _sync_status_changed(self, status):
        self._sync_button.setText("Notes: " + status)
        self._sync_button.setToolTip(status + "\nClick to configure note sync")

    def show_note_sync(self):
        self.save_notes()
        self._menu_open = True
        dialog = NoteSyncDialog(self.note_sync, self)
        try:
            dialog.exec()
        finally:
            self._menu_open = False
            dialog.deleteLater()

    def _note_snapshot(self):
        return {note: {"text": self._note_edits[i].stored(),
                       "title": self._note_titles[i], "color": self._note_colors[i],
                       "position": i} for i, note in enumerate(self._note_ids)}

    def _notes_to_seed(self, current):
        slots = dict(zip(self._note_ids, self._note_slots))
        return {key: data for key, data in current.items() if data["text"] or data["title"]
                or data["color"].lower() != default_note_color(slots[key]).lower()}

    def _apply_synced_notes(self, notes, events):
        """Commit imports and sync history together; keep untouched editors/undo."""
        before = self._note_snapshot()
        ordered = sorted(notes, key=lambda key: (notes[key]["position"], key))
        if not ordered:
            # A tombstone must not leave the notepad without an editable tab.
            old_id = next(iter(before))
            if (len(before) == 1 and not before[old_id]["text"] and not before[old_id]["title"]
                    and not any(event["note"] == old_id for event in events.values())):
                note, notes = old_id, before
            else:
                note = uuid.uuid4().hex
                notes = {note: {"text": "", "title": "", "color": default_note_color(0), "position": 0}}
            ordered = [note]
        normalized = {key: {**notes[key], "position": i} for i, key in enumerate(ordered)}
        if before == normalized and self.note_sync.events == events:
            return  # steady-state polling must not rewrite the database or undo stacks
        old_slots = dict(zip(self._note_ids, self._note_slots))
        slots, taken = {}, {old_slots[key] for key in ordered if key in old_slots}
        for key in ordered:
            slot = old_slots.get(key)
            if slot is None:
                slot = free_note_slot(taken)
                taken.add(slot)
            slots[key] = slot
        active = self._note_ids[self._active_note]
        old_active = before[active]
        # When the active version becomes a conflict copy, follow its contents.
        if normalized.get(active, {}).get("text") != old_active["text"]:
            active = next((key for key in ordered if normalized[key]["text"] == old_active["text"]), active)
        if active not in ordered:
            active = ordered[0]
        values = {
            NOTE_ORDER_KEY: json.dumps([slots[key] for key in ordered]),
            NOTE_TAB_KEY: str(slots[active]),
            NOTE_SYNC_STATE_KEY: json.dumps({"events": events, "baseline": normalized}, ensure_ascii=False),
        }
        for key in ordered:
            for base, field in ((NOTE_TEXT_KEY, "text"), (NOTE_TITLE_KEY, "title"), (NOTE_COLOR_KEY, "color")):
                values[note_key(base, slots[key])] = normalized[key][field]
            values[note_key(NOTE_ID_KEY, slots[key])] = key
        with self.db.conn:
            for key in set(old_slots) - set(ordered):
                for base in (NOTE_TEXT_KEY, NOTE_TITLE_KEY, NOTE_COLOR_KEY, NOTE_ID_KEY):
                    self.db.conn.execute("DELETE FROM settings WHERE key = ?", (note_key(base, old_slots[key]),))
            self.db.conn.executemany("INSERT OR REPLACE INTO settings VALUES (?, ?)", values.items())
        if before == normalized:
            return
        dir_open, dir_fav = self._dir_open, self._dir_fav
        arrays = (self._note_ids, self._note_slots, self._note_titles, self._note_colors,
                  self._saved_notes, self._note_tabs, self._note_edits)
        for i in reversed(range(len(self._note_ids))):
            if self._note_ids[i] in normalized:
                continue
            tab, edit = self._note_tabs[i], self._note_edits[i]
            self._tabs_row.strip.layout().removeWidget(tab)
            self._notes_stack.removeWidget(edit)
            edit.removeEventFilter(self)
            tab.setParent(None)
            edit.setParent(None)
            tab.deleteLater()
            edit.deleteLater()
            for row in arrays:
                row.pop(i)
        for key in ordered:
            if key not in self._note_ids:
                self._create_note(slots[key])
        indices = [self._note_ids.index(key) for key in ordered]
        for row in arrays:
            row[:] = [row[i] for i in indices]
        for i, key in enumerate(ordered):
            data, edit = normalized[key], self._note_edits[i]
            if edit.stored() != data["text"]:
                cursor = edit.textCursor()
                position, anchor = cursor.position(), cursor.anchor()
                scroll = edit.verticalScrollBar().value()
                edit.blockSignals(True)
                edit.load(data["text"])
                end = edit.document().characterCount() - 1
                cursor = edit.textCursor()
                cursor.setPosition(min(anchor, end))
                cursor.setPosition(min(position, end), QTextCursor.MoveMode.KeepAnchor)
                edit.setTextCursor(cursor)
                edit.verticalScrollBar().setValue(scroll)
                edit.blockSignals(False)
            self._saved_notes[i] = data["text"]
            self._note_titles[i], self._note_colors[i] = data["title"], data["color"]
            self._tabs_row.strip.layout().insertWidget(i, self._note_tabs[i])
        self._show_note(ordered.index(active))
        if dir_open:
            self._dir_open, self._dir_fav = True, dir_fav
            self._notes_stack.setCurrentWidget(self.directory_panel)
            self._refresh_note_tabs()

    def _restore_notepad(self):
        """Rebuild the strip the way it was left: same notes, same order, same width."""
        dir_open = self.db.get_setting(DIR_OPEN_KEY)  # "1" = DIR, "fav" = FAV
        limit = 999 if self.db.get_setting(NOTE_SYNC_STATE_KEY) else NOTE_MAX_COUNT
        for slot in clean_note_order(self.db.get_setting(NOTE_ORDER_KEY, ""), limit):
            self._create_note(slot)

        try:
            active = self._note_slots.index(int(self.db.get_setting(NOTE_TAB_KEY, "0")))
        except ValueError:
            active = 0
        self._show_note(active)

        self._set_notepad_width(
            clean_notepad_width(self.db.get_setting(NOTE_WIDTH_KEY, "")))
        self._set_notepad_visible(self.db.get_setting(NOTE_OPEN_KEY, "0") == "1")
        if self.db.get_setting(NOTE_PINNED_KEY, "0") == "1":
            self._set_notepad_pinned(True)
        if dir_open in ("1", "fav"):
            self._show_directories(favorites=dir_open == "fav")

    def _create_note(self, slot, position=None):
        """Add one note - its stored text, tab and editor - to the strip.

        Widgets are wired by identity rather than by index: dragging a tab
        renumbers every note after it, and a stale index would switch, rename
        or close the wrong one.
        """
        position = len(self._note_tabs) if position is None else position
        # Normalised up front: every later state is renumbered, so an undo that
        # landed on a crooked list would be renumbered straight back again.
        text = self.db.get_setting(note_key(NOTE_TEXT_KEY, slot), "")
        if not text.startswith(NOTE_RICH_PREFIX):  # styled notes renumber as they're edited
            text = "\n".join(renumber(text.split("\n")))

        tab = NoteTab(self._tabs_row.strip)
        tab.clicked.connect(lambda _checked=False, t=tab: self._switch_note(self._index_of(t)))
        tab.rename_requested.connect(lambda t=tab: self._start_rename(self._index_of(t)))
        tab.close_requested.connect(lambda t=tab: self._close_note(self._index_of(t)))
        tab.customContextMenuRequested.connect(
            lambda pos, t=tab: self._note_tab_menu(self._index_of(t), pos))
        tab.drag_moved.connect(lambda where, t=tab: self._drag_note(t, where))

        edit = NoteEdit()
        edit.setObjectName("notes")
        edit.setPlaceholderText("Jot something down…")
        edit.setTabChangesFocus(True)
        edit.installEventFilter(self)
        edit.load(text)
        edit.textChanged.connect(self._renumber_notes)
        edit.textChanged.connect(self._note_timer_start)
        edit.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        edit.customContextMenuRequested.connect(self._notes_menu)

        self._note_slots.insert(position, slot)
        note_id = self.db.get_setting(note_key(NOTE_ID_KEY, slot))
        if not re.fullmatch(r"[0-9a-f]{32}", note_id) or note_id in self._note_ids:
            note_id = uuid.uuid4().hex
            self._remember(note_key(NOTE_ID_KEY, slot), note_id)
        self._note_ids.insert(position, note_id)
        self._note_titles.insert(position, raw_note_title(
            self.db.get_setting(note_key(NOTE_TITLE_KEY, slot), "")))
        self._note_colors.insert(position, clean_note_color(
            self.db.get_setting(note_key(NOTE_COLOR_KEY, slot), ""), slot))
        self._saved_notes.insert(position, text)
        self._note_tabs.insert(position, tab)
        self._note_edits.insert(position, edit)
        self._tabs_row.strip.layout().insertWidget(position, tab)
        self._notes_stack.addWidget(edit)  # the stack's own order never matters
        return position

    def _index_of(self, tab):
        return self._note_tabs.index(tab)

    def _refresh_note_tabs(self):
        """Repaint every tab's caption/colour and tint every note's editor."""
        for i, tab in enumerate(self._note_tabs):
            active = i == self._active_note and not self._dir_open
            caption = clean_note_title(self._note_titles[i], i)
            tab.setCaption(caption)
            tab.setToolTip(caption)
            tab.setChecked(active)
            tab.setStyleSheet(note_tab_style(self._note_colors[i], active))
        for i, edit in enumerate(self._note_edits):
            edit.setStyleSheet(note_editor_style(self._note_colors[i]))
        self._note_add.setEnabled(len(self._note_tabs) < NOTE_MAX_COUNT)
        dir_active = self._dir_open and not self._dir_fav
        fav_active = self._dir_open and self._dir_fav
        self._dir_tab.setChecked(dir_active)
        self._dir_tab.setStyleSheet(note_tab_style("#2ab5a5", dir_active))
        self._fav_tab.setChecked(fav_active)
        self._fav_tab.setStyleSheet(note_tab_style("#d9a521", fav_active))
        self._panel_hint.setText("Favourite folders" if fav_active else
                                 "Folders from clipboard history" if dir_active else
                                 "Drag tabs to reorder · double-click to rename")
        self._panel_keys.setText("Double-click/Ctrl+C copies · Enter opens · right-click for more"
                                 if self._dir_open else
                                 "Ctrl+T adds · Ctrl+W closes · right-click for more")

    def _show_note(self, index):
        """Put note ``index`` on screen, without touching what was saved."""
        index = max(0, min(index, len(self._note_edits) - 1))
        self._dir_open = False
        self._remember(DIR_OPEN_KEY, "0")
        self._active_note = index
        self.notes = self._note_edits[index]
        self._notes_stack.setCurrentWidget(self.notes)
        self._refresh_note_tabs()
        self._tabs_row.keep_visible(self._note_tabs[index])

    def _switch_note(self, index):
        if index == self._active_note and not self._dir_open:
            return
        self.save_notes()  # flush the note we're leaving before switching away
        self._show_note(index)
        self._remember(NOTE_TAB_KEY, str(self._note_slots[self._active_note]))
        self.notes.setFocus()

    def _cycle_note(self, delta):
        if self._dir_open:
            self._switch_note(0 if delta > 0 else len(self._note_edits) - 1)
            return
        self._switch_note((self._active_note + delta) % len(self._note_edits))

    # ---- adding, closing and reordering tabs -------------------------------

    def _save_note_order(self):
        self._remember(NOTE_ORDER_KEY, json.dumps(self._note_slots))

    def _add_note(self):
        """Open a fresh note at the end of the strip and switch to it."""
        if len(self._note_tabs) >= NOTE_MAX_COUNT:
            return
        position = self._create_note(free_note_slot(self._note_slots))
        self._save_note_order()
        self.save_notes()
        self._show_note(position)
        self._remember(NOTE_TAB_KEY, str(self._note_slots[position]))
        self.notes.setFocus()

    def _close_note(self, index):
        """Drop a note for good, once whoever asked has confirmed losing it."""
        if len(self._note_tabs) <= NOTE_MIN_COUNT or not 0 <= index < len(self._note_tabs):
            return
        self.save_notes()
        if self._note_edits[index].toPlainText().strip() and not self._confirm_close(index):
            return

        slot = self._note_slots.pop(index)
        tab = self._note_tabs.pop(index)
        edit = self._note_edits.pop(index)
        del self._note_titles[index], self._note_colors[index], self._saved_notes[index]
        del self._note_ids[index]

        self._tabs_row.strip.layout().removeWidget(tab)
        tab.setParent(None)
        tab.deleteLater()
        self._notes_stack.removeWidget(edit)
        edit.removeEventFilter(self)
        edit.setParent(None)
        edit.deleteLater()

        for base in (NOTE_TEXT_KEY, NOTE_TITLE_KEY, NOTE_COLOR_KEY, NOTE_ID_KEY):
            self._forget(note_key(base, slot))
        self._save_note_order()

        self._show_note(self._active_note - 1 if self._active_note > index
                        else self._active_note)  # _show_note clamps past the end
        self._remember(NOTE_TAB_KEY, str(self._note_slots[self._active_note]))
        self.notes.setFocus()

    def _confirm_close(self, index):
        """Ask before throwing away a note that still has something in it."""
        title = clean_note_title(self._note_titles[index], index)
        ask = QMessageBox(self)
        ask.setWindowTitle("Close note")
        ask.setIcon(QMessageBox.Icon.Warning)
        ask.setText(f"Delete the note “{title}” and everything in it?")
        ask.setInformativeText("This cannot be undone.")
        ask.setStandardButtons(
            QMessageBox.StandardButton.Cancel | QMessageBox.StandardButton.Yes)
        ask.setDefaultButton(QMessageBox.StandardButton.Cancel)
        ask.setStyleSheet(
            "QWidget { background:#1b1f27; color:#e8eaed; font-size:12px; }"
            "QPushButton { background:#2a2f3a; border:1px solid #3a414f;"
            "  border-radius:6px; padding:5px 16px; min-width:64px; }"
            "QPushButton:hover { border:1px solid #4c8bf5; }"
        )

        self._menu_open = True  # the dialog deactivates us; don't read that as "close"
        try:
            return ask.exec() == QMessageBox.StandardButton.Yes
        finally:
            self._menu_open = False

    def _drag_note(self, tab, where):
        """A tab is being dragged: keep it under the cursor as the strip reflows."""
        source = self._index_of(tab)
        target = self._tab_index_at(where)
        if target is not None and target != source:
            self._move_note(source, target)

    def _tab_index_at(self, where):
        """Which slot in the strip the global point ``where`` falls in."""
        if not self._note_tabs:
            return None
        x = self._tabs_row.strip.mapFromGlobal(where).x()
        for i, tab in enumerate(self._note_tabs):
            if x < tab.geometry().center().x():
                return i
        return len(self._note_tabs) - 1

    def _move_note(self, source, target):
        """Move one tab along the strip, carrying its note and its colour."""
        if source == target:
            return
        for row in (self._note_slots, self._note_ids, self._note_titles, self._note_colors,
                    self._saved_notes, self._note_tabs, self._note_edits):
            row.insert(target, row.pop(source))
        layout = self._tabs_row.strip.layout()
        layout.insertWidget(target, layout.takeAt(source).widget())

        if self._active_note == source:
            self._active_note = target
        elif source < self._active_note <= target:
            self._active_note -= 1
        elif target <= self._active_note < source:
            self._active_note += 1

        self._refresh_note_tabs()
        self._save_note_order()

    # ---- one tab -----------------------------------------------------------

    def _note_tab_menu(self, index, pos):
        """Right-click on a tab: rename, recolour, or close it."""
        tab = self._note_tabs[index]
        self._menu_open = True
        menu = QMenu(self)
        menu.addAction("Rename…", lambda: self._start_rename(index))
        menu.addSeparator()
        current = self._note_colors[index].lower()
        for name, colour in NOTE_COLORS:
            action = menu.addAction(swatch(colour), name,
                                     lambda c=colour: self._set_note_color(index, c))
            action.setCheckable(True)
            action.setChecked(colour.lower() == current)
        menu.addSeparator()
        new = menu.addAction("New note", self._add_note)
        new.setEnabled(len(self._note_tabs) < NOTE_MAX_COUNT)
        close = menu.addAction("Close note", lambda: self._close_note(index))
        close.setEnabled(len(self._note_tabs) > NOTE_MIN_COUNT)
        menu.exec(tab.mapToGlobal(pos))
        self._menu_open = False

    def _set_note_color(self, index, colour):
        self._note_colors[index] = colour
        self._remember(note_key(NOTE_COLOR_KEY, self._note_slots[index]), colour)
        self._refresh_note_tabs()

    def _start_rename(self, index):
        """Swap a tab's button for an inline edit box, in place."""
        tab = self._note_tabs[index]
        edit = NoteTitleEdit(self._note_titles[index], tab.parentWidget())
        edit.setStyleSheet(
            f"QLineEdit#noteRename {{ border:1px solid {self._note_colors[index]}; }}"
        )
        edit.setGeometry(tab.geometry())
        edit.committed.connect(
            lambda text, t=tab, e=edit: self._commit_rename(self._index_of(t), text, e))
        edit.cancelled.connect(
            lambda t=tab, e=edit: self._end_rename(self._index_of(t), e))
        tab.hide()
        edit.show()
        edit.setFocus()
        edit.selectAll()

    def _commit_rename(self, index, text, edit):
        title = raw_note_title(text)
        self._note_titles[index] = title
        self._remember(note_key(NOTE_TITLE_KEY, self._note_slots[index]), title)
        self._end_rename(index, edit)

    def _end_rename(self, index, edit):
        self._note_tabs[index].show()
        edit.deleteLater()
        self._refresh_note_tabs()
        if index == self._active_note:
            self.notes.setFocus()

    # ---- how wide the pad is -----------------------------------------------

    def _set_notepad_width(self, width, remember=False, anchor_x=None):
        """Resize the pad, growing the window rather than squeezing the history."""
        width = max(NOTEPAD_MIN_WIDTH, min(NOTEPAD_MAX_WIDTH, int(width)))
        changed = width != self._notepad_width
        self._notepad_width = width
        self.notepad.setFixedWidth(width + NOTE_GRIP_WIDTH)
        if self._notes_open:
            self.layout().activate()  # release the previous minimum before shrinking
            self.resize(self._open_width(), self.height())
            if anchor_x is not None:      # a drag says where the window should sit
                self._place_near(QPoint(anchor_x, self.y()))
            elif self.isVisible():        # otherwise just don't spill off the screen
                self._place_near(self.pos())
        if remember and changed:
            self._remember(NOTE_WIDTH_KEY, str(width))

    def _open_width(self):
        if self._notepad_pinned:
            margins = self.layout().contentsMargins()
            return margins.left() + margins.right() + NOTE_GRIP_WIDTH + self._notepad_width
        return (self._history_width + self.COLUMN_GAP
                + NOTE_GRIP_WIDTH + self._notepad_width)

    def _grip_grabbed(self):
        self._resize_origin = (self._notepad_width, self.x())

    def _grip_dragged(self, delta):
        if self._resize_origin is None:
            return
        start_width, start_x = self._resize_origin
        width = max(NOTEPAD_MIN_WIDTH, min(NOTEPAD_MAX_WIDTH, start_width - delta))
        # Anchor the window's right edge so the grip stays under the cursor.
        self._set_notepad_width(width, anchor_x=start_x - (width - start_width))

    def _grip_released(self):
        self._resize_origin = None
        self._remember(NOTE_WIDTH_KEY, str(self._notepad_width))

    # ---- resizing from the window's edges ----------------------------------

    def _fixed_width(self):
        """The part of the window an edge drag leaves alone: everything beside
        the clip list, or beside the pad when it is pinned on its own."""
        if self._notepad_pinned:
            return self._open_width() - self._notepad_width
        if self._notes_open:
            return self._open_width() - self._history_width
        return 0

    def _edge_grabbed(self):
        self._edge_origin = self.geometry()

    def _edge_dragged(self, side, delta):
        """Resize from the grabbed side; the opposite side stays where it was.

        Extra width goes to the clip list - the pad keeps the width its own
        grip gave it - unless the pad is pinned alone, when it is the pad's.
        """
        if self._edge_origin is None:
            return
        start, (dx, dy) = self._edge_origin, side
        screen = self.screen().availableGeometry()
        fixed = self._fixed_width()
        if self._notepad_pinned:
            least_w = fixed + NOTEPAD_MIN_WIDTH
            most_w = min(screen.width(), fixed + NOTEPAD_MAX_WIDTH)
        else:
            least_w = max(fixed + HISTORY_MIN_WIDTH, self.minimumSizeHint().width())
            most_w = screen.width()
        least_h = max(WINDOW_MIN_HEIGHT, self.minimumSizeHint().height())

        left, right = dragged_span(start.left(), start.right(), dx, delta.x(),
                                   least_w, most_w, screen.left(), screen.right())
        top, bottom = dragged_span(start.top(), start.bottom(), dy, delta.y(),
                                   least_h, screen.height(), screen.top(), screen.bottom())
        width = right - left + 1
        if self._notepad_pinned:
            self._notepad_width = width - fixed
            self.notepad.setFixedWidth(self._notepad_width + NOTE_GRIP_WIDTH)
            self.layout().activate()  # release the pad's old minimum before shrinking
        else:
            self._history_width = width - fixed
        self.setGeometry(left, top, width, bottom - top + 1)

    def _edge_released(self):
        self._edge_origin = None
        self._remember(WINDOW_HEIGHT_KEY, str(self.height()))
        if self._notepad_pinned:
            self._remember(NOTE_WIDTH_KEY, str(self._notepad_width))
        else:
            self._remember(HISTORY_WIDTH_KEY, str(self._history_width))

    def resizeEvent(self, event):
        super().resizeEvent(event)
        for grip in self._edge_grips:
            grip.place()

    def _set_notepad_visible(self, visible):
        self._notes_open = bool(visible)
        if not visible and self._notepad_pinned:
            self._set_notepad_pinned(False)  # nothing to pin once the pad is gone
        self.notepad.setVisible(visible)
        self.notes_toggle.blockSignals(True)
        self.notes_toggle.setChecked(visible)
        self.notes_toggle.blockSignals(False)
        self.notes_toggle.setText("Notes ‹" if visible else "Notes ›")

        if not self._notepad_pinned:
            self.layout().activate()  # drop the hidden pad from the minimum width
            self.resize(self._open_width() if visible else self._history_width, self.height())
            if self.isVisible():  # a wider window must not spill off the screen edge
                self._place_near(self.pos())
        self._remember(NOTE_OPEN_KEY, "1" if visible else "0")

    def _toggle_notepad(self, *_):
        visible = not self._notes_open
        self._set_notepad_visible(visible)
        (self.dir_search if visible and self._dir_open else
         self.notes if visible else self.search).setFocus()

    def _set_notepad_pinned(self, pinned):
        """Notepad-only mode: hide the clip list and stay up when the popup
        loses focus, so the pad behaves like a small always-on-top notepad."""
        pinned = bool(pinned)
        self._notepad_pinned = pinned
        self._pin_check.blockSignals(True)
        self._pin_check.setChecked(pinned)
        self._pin_check.blockSignals(False)

        if pinned and not self._notes_open:
            self._set_notepad_visible(True)
        self.history_panel.setVisible(not pinned)
        self.notes_toggle.setEnabled(not pinned)
        self.layout().activate()  # settle the layout before sizing off of it

        if pinned:
            margins = self.layout().contentsMargins()
            width = margins.left() + margins.right() + self._notepad_width + NOTE_GRIP_WIDTH
        else:
            width = self._open_width() if self._notes_open else self._history_width
        self.resize(width, self.height())
        if self.isVisible():
            self._place_near(self.pos())
        self._remember(NOTE_PINNED_KEY, "1" if pinned else "0")

    def _note_timer_start(self):
        self._note_timer.start()

    def save_notes(self):
        """Write the active note out; called on a typing pause, tab switch,
        hide, and quit."""
        self._note_timer.stop()
        idx = self._active_note
        slot = self._note_slots[idx]
        text = self.notes.stored()
        if text == self._saved_notes[idx]:
            return True
        if not self._remember(note_key(NOTE_TEXT_KEY, slot), text):
            return False
        self._saved_notes[idx] = text
        return True

    # ---- notepad formatting ------------------------------------------------

    def _notes_menu(self, pos):
        """Right-click in the pad: the usual editing menu plus text and list formatting."""
        if not self.notes.textCursor().hasSelection():
            # Nothing selected: styles land on the word that was right-clicked.
            self.notes.setTextCursor(self.notes.cursorForPosition(pos))
        menu = self.notes.createStandardContextMenu()
        menu.addSeparator()

        highlight = menu.addMenu("Highlight")
        current = self.notes.textCursor().charFormat().background()
        for label, colour in NOTE_HIGHLIGHTS:
            action = highlight.addAction(swatch(colour), label,
                                         lambda c=colour: self._highlight(c))
            action.setCheckable(True)
            action.setChecked(current.style() != Qt.BrushStyle.NoBrush
                              and current.color().name() == colour)
        highlight.addSeparator()
        highlight.addAction("No highlight", lambda: self._highlight(None))

        style = menu.addMenu("Text style")
        level = self.notes.textCursor().blockFormat().headingLevel()
        for number, label in enumerate(("Normal", "Heading 1", "Heading 2", "Heading 3")):
            action = style.addAction(label, lambda n=number: self._set_heading(n))
            action.setShortcut(QKeySequence(f"Ctrl+Alt+{number}"))
            action.setCheckable(True)
            action.setChecked(number == level)

        sizes = menu.addMenu("Font size")
        here = self._font_size()
        default = sizes.addAction("Default", lambda: self._set_font_size(None))
        default.setCheckable(True)
        default.setChecked(here is None)
        sizes.addSeparator()
        for points in NOTE_FONT_SIZES:
            action = sizes.addAction(str(points), lambda p=points: self._set_font_size(p))
            action.setCheckable(True)
            action.setChecked(here == points)
        sizes.addSeparator()
        sizes.addAction("Bigger", lambda: self._step_font_size(1)).setShortcut(
            QKeySequence("Ctrl+]"))
        sizes.addAction("Smaller", lambda: self._step_font_size(-1)).setShortcut(
            QKeySequence("Ctrl+["))
        menu.addSeparator()
        for label, keys, style in (
            ("Bullet list", "Ctrl+Shift+8", "bullet"),
            ("Numbered list", "Ctrl+Shift+7", "number"),
            ("Checklist", "Ctrl+Shift+9", "todo"),
        ):
            action = menu.addAction(label, lambda s=style: self._apply_list(s))
            action.setShortcut(QKeySequence(keys))
        done = menu.addAction("Toggle done", self._toggle_done)
        done.setShortcut(QKeySequence("Ctrl+Shift+X"))
        done.setEnabled(any(DONE_BOX.match(line) for line in self._note_lines()))
        menu.addSeparator()
        stamp = menu.addAction("Insert date && time", self._insert_timestamp)
        stamp.setShortcut(QKeySequence("F5"))

        self._menu_open = True  # a popup deactivates us; don't read that as "close"
        menu.exec(self.notes.mapToGlobal(pos))
        self._menu_open = False
        self.notes.setFocus()  # the menu took the caret; hand it back

    def _note_blocks(self):
        """Block numbers the notepad cursor or selection touches."""
        cursor = self.notes.textCursor()
        doc = self.notes.document()
        first = doc.findBlock(cursor.selectionStart())
        last = doc.findBlock(cursor.selectionEnd())
        if (cursor.hasSelection()
                and last.blockNumber() != first.blockNumber()
                and cursor.selectionEnd() == last.position()):
            last = last.previous()  # a selection stopping at a line start excludes it
        return range(first.blockNumber(), last.blockNumber() + 1)

    def _note_lines(self, blocks=None):
        doc = self.notes.document()
        return [doc.findBlockByNumber(n).text()
                for n in (self._note_blocks() if blocks is None else blocks)]

    def _rewrite_notes(self, blocks, lines):
        """Swap whole lines in place, as a single undo step."""
        doc = self.notes.document()
        edit = QTextCursor(doc)
        edit.beginEditBlock()
        for number, text in zip(blocks, lines):
            block = doc.findBlockByNumber(number)  # earlier edits move later blocks
            if block.text() == text:
                continue
            edit.setPosition(block.position())
            edit.setPosition(block.position() + block.length() - 1,
                             QTextCursor.MoveMode.KeepAnchor)
            edit.insertText(text)
        edit.endEditBlock()

    def _apply_list(self, style):
        blocks = self._note_blocks()
        self._rewrite_notes(blocks, relist(self._note_lines(blocks), style))

    def _renumber_notes(self):
        """Keep every numbered run counting 1, 2, 3… as lines come and go.

        Only the digits are replaced, so a caret sitting further along the line
        rides the edit rather than being dragged back to the margin, and the
        rewrite joins the edit that caused it: one keystroke, one undo.
        """
        if self._renumbering:
            return
        doc = self.notes.document()
        lines = [doc.findBlockByNumber(n).text() for n in range(doc.blockCount())]
        stale = [(number, want) for number, want in enumerate(wanted_numbers(lines))
                 if want and NUMBER_ITEM.match(lines[number]).group(2) != str(want)]
        if not stale:
            return

        self._renumbering = True
        try:
            edit = QTextCursor(doc)
            edit.joinPreviousEditBlock()
            for number, want in stale:
                block = doc.findBlockByNumber(number)  # earlier edits shift later blocks
                match = NUMBER_ITEM.match(block.text())
                edit.setPosition(block.position() + match.start(2))
                edit.setPosition(block.position() + match.end(2),
                                 QTextCursor.MoveMode.KeepAnchor)
                edit.insertText(str(want))
            edit.endEditBlock()
        finally:
            self._renumbering = False

    def _toggle_done(self):
        lines = [toggle_done(line) for line in self._note_lines()]
        self._rewrite_notes(self._note_blocks(), lines)

    def _insert_timestamp(self):
        self.notes.insertPlainText(time.strftime(NOTE_STAMP_FORMAT))

    # ---- notepad text styles -----------------------------------------------

    def _styled_range(self):
        """A cursor over the selection, else over the word at the caret."""
        cursor = self.notes.textCursor()
        if not cursor.hasSelection():
            cursor.select(QTextCursor.SelectionType.WordUnderCursor)
        return cursor

    def _strip_format(self, cursor, props):
        """Remove ``props`` from every character ``cursor`` selects."""
        doc = self.notes.document()
        start, end = cursor.selectionStart(), cursor.selectionEnd()
        runs, block = [], doc.findBlock(start)
        while block.isValid() and block.position() <= end:
            for part in block.textFormats():
                low = max(start, block.position() + part.start)
                high = min(end, block.position() + part.start + part.length)
                if low < high:
                    runs.append((low, high, QTextCharFormat(part.format)))  # outlive the list
            block = block.next()
        # Collected first: restyling a run splits and merges the ones around it.
        for low, high, fmt in runs:
            for prop in props:
                fmt.clearProperty(prop)
            run = QTextCursor(doc)
            run.setPosition(low)
            run.setPosition(high, QTextCursor.MoveMode.KeepAnchor)
            run.setCharFormat(fmt)

    def _restyle(self, props=(), merge=None):
        """Clear ``props`` then merge ``merge`` into the selection (or the word
        at the caret), as one undo step. With neither, it styles what's typed next."""
        cursor = self._styled_range()
        if not cursor.hasSelection():
            fmt = self.notes.currentCharFormat()
            for prop in props:
                fmt.clearProperty(prop)
            if merge is not None:
                fmt.merge(merge)
            self.notes.setCurrentCharFormat(fmt)
            return
        cursor.beginEditBlock()
        self._strip_format(cursor, props)
        if merge is not None:
            cursor.mergeCharFormat(merge)
        cursor.endEditBlock()

    def _highlight(self, colour):
        """Mark text red, yellow or green like a highlighter; ``None`` rubs it out."""
        if colour is None:
            self._restyle(HIGHLIGHT_PROPS)
            return
        fmt = QTextCharFormat()
        fmt.setBackground(QColor(colour))
        fmt.setForeground(QColor(NOTE_HIGHLIGHT_INK))
        self._restyle(merge=fmt)

    def _font_size(self):
        """The size at the caret in points, or ``None`` for the pad's default."""
        fmt = self.notes.textCursor().charFormat()
        if fmt.hasProperty(QTextFormat.Property.FontPointSize):
            return round(fmt.fontPointSize())
        pixels = fmt.property(QTextFormat.Property.FontPixelSize)
        return None if pixels in (None, NOTE_BODY_PX) else px_to_pt(pixels)

    def _set_font_size(self, points):
        fmt = None
        if points is not None:
            fmt = QTextCharFormat()
            fmt.setProperty(QTextFormat.Property.FontPixelSize, pt_to_px(points))
        self._restyle(SIZE_PROPS, fmt)

    def _step_font_size(self, step):
        """Word's Ctrl+] / Ctrl+[: one size up or down the size list."""
        here = self._font_size() or px_to_pt(NOTE_BODY_PX)
        if step > 0:
            bigger = [p for p in NOTE_FONT_SIZES if p > here]
            self._set_font_size(bigger[0] if bigger else NOTE_FONT_SIZES[-1])
        else:
            smaller = [p for p in NOTE_FONT_SIZES if p < here]
            self._set_font_size(smaller[-1] if smaller else NOTE_FONT_SIZES[0])

    def _set_heading(self, level):
        """Heading 1-3, or back to Normal, for every line the cursor touches."""
        doc = self.notes.document()
        blocks = self._note_blocks()
        heading = None
        if level:
            heading = QTextCharFormat()
            heading.setProperty(QTextFormat.Property.FontPixelSize,
                                pt_to_px(NOTE_HEADING_PT[level]))
            heading.setFontWeight(QFont.Weight.Bold)
        edit = QTextCursor(doc)
        edit.beginEditBlock()
        for number in blocks:
            block = doc.findBlockByNumber(number)
            edit.setPosition(block.position())
            fmt = block.blockFormat()
            fmt.setHeadingLevel(level)
            edit.setBlockFormat(fmt)
            # The block's own char format is what an emptied line types in.
            empty = block.charFormat()
            for prop in (*SIZE_PROPS, QTextFormat.Property.FontWeight):
                empty.clearProperty(prop)
            if heading is not None:
                empty.merge(heading)
            edit.setBlockCharFormat(empty)
            edit.setPosition(block.position() + block.length() - 1,
                             QTextCursor.MoveMode.KeepAnchor)
            self._strip_format(edit, (*SIZE_PROPS, QTextFormat.Property.FontWeight))
            if heading is not None:
                edit.mergeCharFormat(heading)
        edit.endEditBlock()
        caret = self.notes.textCursor()
        if not caret.hasSelection():  # with one, this would restyle the selection
            self.notes.setCurrentCharFormat(caret.charFormat())  # keep typing in the new style

    def _leave_heading(self):
        """Enter at the end of a heading starts a Normal line, as in Word.

        Returns whether the key was handled.
        """
        cursor = self.notes.textCursor()
        if (cursor.hasSelection() or not cursor.blockFormat().headingLevel()
                or not cursor.atBlockEnd()):
            return False
        cursor.insertBlock(QTextBlockFormat(), QTextCharFormat())
        self.notes.setTextCursor(cursor)
        self.notes.setCurrentCharFormat(QTextCharFormat())
        return True

    def _continue_list(self):
        """Enter carries the marker to the next line; on an empty one, ends the list.

        Returns whether the key was handled.
        """
        cursor = self.notes.textCursor()
        if cursor.hasSelection():
            return False
        block = cursor.block()
        line = block.text()
        match = ANY_MARKER.match(line)
        if not match or cursor.positionInBlock() < match.end():
            return False
        if line[match.end():].strip():
            cursor.insertText("\n" + inherited_marker(line))
        else:  # an empty bullet means "I'm done listing", not "give me another"
            cursor.setPosition(block.position())
            cursor.setPosition(block.position() + block.length() - 1,
                               QTextCursor.MoveMode.KeepAnchor)
            cursor.insertText(match.group(1))
        self.notes.setTextCursor(cursor)
        return True

    def _remember(self, key, value):
        try:
            self.db.set_setting(key, value)
            if hasattr(self, "note_sync") and (key == NOTE_ORDER_KEY or any(
                    key == base or key.startswith(base + "_")
                    for base in (NOTE_TEXT_KEY, NOTE_TITLE_KEY, NOTE_COLOR_KEY))):
                self.note_sync.changed()
            return True
        except sqlite3.Error:
            logger.exception("Could not save setting %s", key)
            return False

    def _forget(self, key):
        try:
            self.db.delete_setting(key)
        except sqlite3.Error:
            logger.exception("Could not delete setting %s", key)

    # ---- showing and placing -----------------------------------------------

    def _place_near(self, pos):
        """Move the window to ``pos``, kept fully inside that screen's work area."""
        screen = QGuiApplication.screenAt(pos) or QGuiApplication.primaryScreen()
        geo = screen.availableGeometry()
        x = min(max(pos.x(), geo.left()), max(geo.left(), geo.right() - self.width()))
        y = min(max(pos.y(), geo.top()), max(geo.top(), geo.bottom() - self.height()))
        self.move(x, y)

    def show_popup(self):
        # Repeated hotkey presses while open must not replace the paste target
        # with PyClip's own native window handle.
        if not self.isVisible():
            self.prev_hwnd = get_foreground_window()
        self.search.blockSignals(True)
        self.search.clear()
        self.search.blockSignals(False)
        self.reload()
        self._place_near(self.pos() if self._notepad_pinned else QCursor.pos())

        self._ignore_deactivate = True
        self.show()
        self.raise_()
        force_foreground(int(self.winId()))
        self.activateWindow()
        (self.dir_search if self._notes_open and self._dir_open else
         self.notes if self._notepad_pinned else self.search).setFocus()
        QTimer.singleShot(250, lambda: setattr(self, "_ignore_deactivate", False))

    def _selected_ids(self):
        """Ids of selected rows, in top-to-bottom display order."""
        ids = []
        for row in range(self.list.count()):
            item = self.list.item(row)
            if item.isSelected():
                data = item.data(Qt.ItemDataRole.UserRole) or {}
                if "id" in data:
                    ids.append(data["id"])
        return ids

    def _paste_selected(self, *_):
        ids = self._selected_ids()
        if ids:
            self.paste_requested.emit(ids)

    def _copy_selected(self):
        ids = self._selected_ids()
        if ids:
            self.copy_requested.emit(ids)

    def _delete_selected(self):
        self._delete_ids(self._selected_ids())

    def _delete_ids(self, ids):
        if not ids:
            return
        for clip_id in ids:
            self.db.delete(clip_id)
        self.reload()
        self.search.setFocus()

    def _context_menu(self, pos):
        item = self.list.itemAt(pos)
        if not item:
            return
        if not item.isSelected():  # right-click outside selection -> pick that row
            self.list.clearSelection()
            item.setSelected(True)
            self.list.setCurrentItem(item)
        ids = self._selected_ids()
        if not ids:
            return
        n = len(ids)
        suffix = f"  ({n})" if n > 1 else ""

        self._menu_open = True
        menu = QMenu(self)
        menu.addAction("Paste" + suffix, lambda: self.paste_requested.emit(ids))
        menu.addAction("Copy to clipboard" + suffix,
                       lambda: self.copy_requested.emit(ids))
        if n == 1:
            data = item.data(Qt.ItemDataRole.UserRole) or {}
            menu.addAction("Unpin" if data.get("pinned") else "Pin",
                           lambda: self._do(self.db.toggle_pin, ids[0]))
        menu.addSeparator()
        menu.addAction("Delete" + suffix, lambda: self._delete_ids(ids))
        menu.exec(self.list.mapToGlobal(pos))
        self._menu_open = False

    def _do(self, fn, clip_id):
        fn(clip_id)
        self.reload()
        self.search.setFocus()

    def eventFilter(self, obj, event):
        if (event.type() == QEvent.Type.KeyPress
                and obj in (self.search, self.list, self.dir_search, self.dir_list,
                            *self._note_edits)):
            key = event.key()
            ctrl = bool(event.modifiers() & Qt.KeyboardModifier.ControlModifier)

            # shared shortcuts (work from the search box, the list, or the notepad)
            if key == Qt.Key.Key_Escape:
                self.hide()
                return True
            if ctrl and key == Qt.Key.Key_N:
                self._toggle_notepad()
                return True

            if obj in (self.dir_search, self.dir_list):
                shift = bool(event.modifiers() & Qt.KeyboardModifier.ShiftModifier)
                if ctrl and key in (Qt.Key.Key_Tab, Qt.Key.Key_Backtab):
                    self._cycle_note(-1 if shift else 1)
                    return True
                if ctrl and key == Qt.Key.Key_T:
                    self._add_note()
                    return True
                if ctrl and key == Qt.Key.Key_W:
                    return True  # DIR is a permanent tab, not a deletable note.
                if ctrl and key == Qt.Key.Key_C:
                    # Preserve normal copying of selected search text.
                    if obj is self.dir_search and self.dir_search.hasSelectedText():
                        return super().eventFilter(obj, event)
                    self._copy_directory()
                    return True
                if key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                    self._open_directory()
                    return True
                if obj is self.dir_search and key in (
                        Qt.Key.Key_Up, Qt.Key.Key_Down,
                        Qt.Key.Key_PageUp, Qt.Key.Key_PageDown):
                    self._move(key, self.dir_list)
                    return True
                if obj is self.dir_list and key == Qt.Key.Key_Delete:
                    self._forget_directory()
                    return True
                return super().eventFilter(obj, event)

            # the notepad is an editor: only its formatting keys are ours
            if obj in self._note_edits:
                shift = bool(event.modifiers() & Qt.KeyboardModifier.ShiftModifier)
                if ctrl and key in (Qt.Key.Key_Tab, Qt.Key.Key_Backtab):
                    self._cycle_note(-1 if shift else 1)
                    return True
                if ctrl and key == Qt.Key.Key_T:
                    self._add_note()
                    return True
                if ctrl and key == Qt.Key.Key_W:
                    self._close_note(self._active_note)
                    return True
                if ctrl and shift:
                    for style, keys in self.LIST_KEYS.items():
                        if key in keys:
                            self._apply_list(style)
                            return True
                    if key == Qt.Key.Key_X:
                        self._toggle_done()
                        return True
                alt = bool(event.modifiers() & Qt.KeyboardModifier.AltModifier)
                if ctrl and alt and not shift and key in self.HEADING_KEYS:
                    self._set_heading(self.HEADING_KEYS[key])
                    return True
                if ctrl and not alt and key in (Qt.Key.Key_BracketRight, Qt.Key.Key_BracketLeft):
                    self._step_font_size(1 if key == Qt.Key.Key_BracketRight else -1)
                    return True
                if key == Qt.Key.Key_F5:
                    self._insert_timestamp()
                    return True
                if (key in (Qt.Key.Key_Return, Qt.Key.Key_Enter) and not ctrl and not shift
                        and (self._continue_list() or self._leave_heading())):
                    return True
                return super().eventFilter(obj, event)

            if key == Qt.Key.Key_Delete:
                self._delete_selected()
                return True
            if ctrl and key == Qt.Key.Key_C:
                self._copy_selected()
                return True

            # search box only: drive the list without leaving the search field
            if obj is self.search:
                if key in (Qt.Key.Key_Down, Qt.Key.Key_Up,
                           Qt.Key.Key_PageDown, Qt.Key.Key_PageUp):
                    self._move(key)
                    return True
                if key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                    self._paste_selected()
                    return True
        return super().eventFilter(obj, event)

    def _move(self, key, target=None):
        target = self.list if target is None else target
        n = target.count()
        if not n:
            return
        row = target.currentRow()
        if key == Qt.Key.Key_Down:
            row = min(row + 1, n - 1)
        elif key == Qt.Key.Key_Up:
            row = max(row - 1, 0)
        elif key == Qt.Key.Key_PageDown:
            row = min(row + 8, n - 1)
        elif key == Qt.Key.Key_PageUp:
            row = max(row - 8, 0)
        target.setCurrentRow(row)

    def event(self, e):
        if (e.type() == QEvent.Type.WindowDeactivate
                and not self._menu_open and not self._ignore_deactivate
                and not self._notepad_pinned):
            self.hide()
        return super().event(e)

    def hideEvent(self, event):
        self.save_notes()  # never let a debounce timer outlive the popup
        if self.dir_search.text():
            # The folder filter lasts only as long as the popup is on screen;
            # clearing rebuilds the unfiltered list ready for the next visit.
            self.dir_search.clear()
        super().hideEvent(event)


# =============================================================================
#  Turning a multi-selection into clipboard content
# =============================================================================

def _clip_paths(clip):
    try:
        paths = json.loads(clip["data"])
    except (TypeError, ValueError):
        return []
    if not isinstance(paths, list):
        return []
    return [path for path in paths if isinstance(path, str) and path]


def combine_clips(clips):
    """Decide what a (possibly multi-row) selection puts on the clipboard.

    Returns ``(mode, payload)``:
      * ``('single', clip)`` — one item, copied with full fidelity
      * ``('files', [paths])`` — every item is files; merged into one drop list
      * ``('text', str)`` — text/file items joined with newlines
      * ``(None, None)`` — nothing usable

    Images can't be merged into combined text, so they're skipped when mixed
    with other kinds; a selection of only images falls back to the first one.
    """
    clips = [c for c in clips if c]
    if not clips:
        return (None, None)
    if len(clips) == 1:
        return ("single", clips[0])
    if all(c["kind"] == "files" for c in clips):
        paths = []
        for c in clips:
            paths += _clip_paths(c)
        return ("files", paths)
    parts = []
    for c in clips:
        if c["kind"] == "text":
            parts.append(c["text"] or "")
        elif c["kind"] == "files":
            parts += _clip_paths(c)
    if parts:
        return ("text", "\n".join(parts))
    return ("single", clips[0])  # all images -> just the first


# =============================================================================
#  Tray icon + app wiring
# =============================================================================

def make_icon():
    """Build the tray icon (a little clipboard) entirely in code."""
    pm = QPixmap(64, 64)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor("#4c8bf5"))
    p.drawRoundedRect(12, 10, 40, 48, 6, 6)
    p.setBrush(QColor("#dfe6f3"))
    p.drawRoundedRect(24, 5, 16, 11, 3, 3)
    p.setPen(QPen(QColor("white"), 3))
    for y in (28, 36, 44):
        p.drawLine(21, y, 43, y)
    p.end()
    return QIcon(pm)


def main():
    install_exception_logging()
    logger.info("Starting PyClip %s (Python %s, frozen=%s)",
                APP_VERSION, sys.version.split()[0], bool(getattr(sys, "frozen", False)))

    _ensure_startup_flag()

    instance = SingleInstance()
    if instance.already_running:
        if STARTUP_FLAG not in sys.argv or "--show" in sys.argv:
            instance.request_activation()
            logger.info("Asked the running PyClip instance to show its window")
        else:
            logger.info("A PyClip instance is already running; duplicate startup stopped")
        instance.close()
        return 0

    app = SafeApplication(sys.argv)
    app.setApplicationName("PyClip")
    app.setApplicationVersion(APP_VERSION)
    app.setQuitOnLastWindowClosed(False)  # keep running in the tray
    QImageReader.setAllocationLimit(192)

    try:
        db = Database()
    except (OSError, sqlite3.Error) as exc:
        logger.critical("Could not open clipboard history", exc_info=True)
        QMessageBox.critical(
            None, "PyClip couldn't start",
            f"The clipboard history could not be opened.\n\n{exc}\n\n"
            f"Details were written to:\n{LOG_PATH}",
        )
        instance.close()
        return 1
    monitor = ClipboardMonitor(db)
    window = HistoryWindow(db)
    activation_timer = QTimer(window)
    activation_timer.setInterval(200)

    def activate_existing():
        if instance.take_activation():
            logger.info("Showing PyClip after another manual launch")
            window.show_popup()

    activation_timer.timeout.connect(activate_existing)
    activation_timer.start()
    icon = make_icon()

    def on_clip_added():
        db.enforce_limit(HISTORY_LIMIT)
        if window.isVisible():
            window.reload()

    monitor.clip_added.connect(on_clip_added)

    def _apply_single(cb, clip):
        if clip["kind"] == "text":
            cb.setText(clip["text"] or "")
            return True
        elif clip["kind"] == "image":
            reader = QImageReader(clip["data"] or "")
            reader.setAutoTransform(True)
            img = reader.read()
            if not img.isNull():
                cb.setImage(img)
                return True
            logger.warning("Could not restore image clip: %s (%s)",
                           clip["data"], reader.errorString())
        elif clip["kind"] == "files":
            paths = _clip_paths(clip)
            if not paths:
                return False
            mime = QMimeData()
            mime.setUrls([QUrl.fromLocalFile(p) for p in paths])
            cb.setMimeData(mime)
            return True
        return False

    def set_clipboard_for_ids(ids):
        try:
            mode, payload = combine_clips([db.get_one(i) for i in ids])
            if mode is None:
                return False
            cb = app.clipboard()
            monitor.set_internal(True)
            try:
                if mode == "single":
                    return _apply_single(cb, payload)
                if mode == "files":
                    if not payload:
                        return False
                    mime = QMimeData()
                    mime.setUrls([QUrl.fromLocalFile(p) for p in payload])
                    cb.setMimeData(mime)
                    return True
                if mode == "text":
                    cb.setText(payload)
                    return True
            finally:
                monitor.set_internal(False)
        except Exception:
            logger.exception("Could not restore selected clipboard item(s)")
        return False

    def do_paste(ids):
        if not ids:
            return
        if not set_clipboard_for_ids(ids):
            return
        hwnd = window.prev_hwnd
        window.hide()
        if hwnd:
            force_foreground(hwnd)
            QTimer.singleShot(PASTE_DELAY_MS, send_paste)

    def do_copy(ids):
        if ids:
            set_clipboard_for_ids(ids)
        window.hide()

    window.paste_requested.connect(do_paste)
    window.copy_requested.connect(do_copy)

    def copy_directory_path(path):
        monitor.set_internal(True)
        try:
            QApplication.clipboard().setText(path)
        finally:
            monitor.set_internal(False)

    window.directory_copy_requested.connect(copy_directory_path)

    tray = QSystemTrayIcon(icon)
    tray.setToolTip("PyClip - Clipboard Manager  (Ctrl+Shift+Alt+V)")

    menu = QMenu()
    menu.addAction("Open clipboard history", window.show_popup)
    menu.addAction("Note sync…", window.show_note_sync)
    menu.addSeparator()

    startup_action = menu.addAction("Start with Windows")
    startup_action.setCheckable(True)
    startup_action.setChecked(is_startup_enabled())

    def toggle_startup(checked):
        try:
            set_startup(checked)
        except OSError as exc:
            startup_action.blockSignals(True)
            startup_action.setChecked(is_startup_enabled())  # revert on failure
            startup_action.blockSignals(False)
            logger.exception("Could not change startup setting")
            tray.showMessage("PyClip", f"Couldn't change startup setting: {exc}", icon)

    startup_action.toggled.connect(toggle_startup)

    def clear_all():
        db.clear(keep_pinned=True)
        if window.isVisible():
            window.reload()

    menu.addAction("Clear history (keep pinned)", clear_all)
    menu.addAction("Clean large clipboard items (10 MB+)", window._clean_large_clips)
    menu.addSeparator()

    def quit_app():
        tray.hide()
        app.quit()

    menu.addAction("Quit PyClip", quit_app)
    tray.setContextMenu(menu)

    def on_tray(reason):
        if reason in (QSystemTrayIcon.ActivationReason.Trigger,
                      QSystemTrayIcon.ActivationReason.DoubleClick):
            window.show_popup()

    tray.activated.connect(on_tray)
    tray.show()

    hotkey = GlobalHotkey(MOD_CONTROL | MOD_SHIFT | MOD_ALT | MOD_NOREPEAT, ord("V"))
    hotkey.activated.connect(window.show_popup)

    cleaned_up = False

    def cleanup():
        nonlocal cleaned_up
        if cleaned_up:
            return
        cleaned_up = True
        activation_timer.stop()
        hotkey.unregister()
        window.save_notes()
        window.note_sync.stop()
        db.close()
        instance.close()
        logger.info("PyClip stopped cleanly")

    app.aboutToQuit.connect(cleanup)

    at_startup = STARTUP_FLAG in sys.argv
    logger.info("PyClip ready (hotkey registered=%s, pinned=%s, at startup=%s)",
                hotkey.registered, window._notepad_pinned, at_startup)
    # Double-clicks open the window; Windows login launches stay in the tray.
    if not at_startup or "--show" in sys.argv:
        QTimer.singleShot(0, window.show_popup)

    if hotkey.registered:
        tray.showMessage("PyClip is running",
                         "Press Ctrl+Shift+Alt+V to open clipboard history.", icon)
    else:
        tray.showMessage("PyClip is running",
                         "Ctrl+Shift+Alt+V was unavailable - use the tray icon to open.",
                         icon)

    try:
        return app.exec()
    finally:
        cleanup()


if __name__ == "__main__":
    sys.exit(main())
