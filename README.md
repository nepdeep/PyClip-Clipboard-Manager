PyClip

PyClip is a lightweight clipboard manager for Windows. It runs in the system tray and keeps a searchable history of copied text, images, and files, so you can quickly reuse something you copied earlier without having to find and copy it again.

Typical use case

PyClip is useful when you regularly move between documents, emails, code, screenshots, file paths, or other applications and need access to more than just the most recent clipboard item.

Press Ctrl + Shift + Alt + V (or click the tray icon) to open the clipboard history, search for an item, and paste it back into the application you were using.

The app also includes:

Pinning for frequently reused clipboard items

Multi-item selection

A Reuse tab for favourite clipboard items

A small tabbed notepad for temporary notes

A directory history for quickly reopening or copying previously used folder locations

Local clipboard storage with automatic cleanup

Run

pythonw pyclip.pyw

Use python pyclip.pyw instead if you want to see console/log output.

Opening `pyclip.pyw` shows the window. Opening it again brings the running copy forward. Automatic Windows login launches stay in the tray.

Drag the middle divider to redistribute space between clipboard history and notes without moving either outer window edge. Moving it right widens clipboard history and narrows notes; moving it left does the reverse. Drag an outer window edge to resize the window itself. Both section widths are remembered. Double-click the divider to reset the clipboard width within the current window; in notes-only mode, it resizes and resets notes instead.

Right-click one or more clipboard items and choose **Add to Reuse** to save text, images, or file references in the **Reuse** tab. Search that tab, press Enter or double-click to paste, or use Ctrl+C to copy. **Remove from Reuse** (or Delete while in its list) removes the favourite without deleting the clipboard entry. Reuse items stay saved during history pruning, storage cleanup, and **Clear history (keep pinned and Reuse)**. Explicitly deleting an item from clipboard history still deletes it from Reuse too. Reuse replaces the former FAV folder tab; DIR continues to show copied folder locations.

Note sync (optional)

Local-only storage is the default. To share PyClip notes between PCs:

1. Install and sign in to Google Drive for desktop or the Dropbox desktop app.
2. Open **Note sync…** from PyClip's tray menu, or click the status at the bottom of the notepad.
3. Choose **Google Drive folder** or **Dropbox folder**, select a folder in that signed-in account, and save. An **Other synced folder** option also supports another sync client or a shared drive.
4. On each other PC, select the same cloud folder in PyClip. The local folder paths can differ. Keep the folder available offline and let the desktop app finish downloading existing files.

PyClip creates a `PyClip Notes/revisions` subfolder. Notes save locally after a short typing pause. Folder updates run in the background after edits, and PyClip checks for changes every 15 seconds while it is running, including when hidden in the tray. Offline edits are retried automatically. **Sync now** runs an immediate check. “Folder updated” confirms the local folder exchange; Google Drive or Dropbox controls when cloud uploads and downloads finish.

Recovery runs automatically during the regular 15-second checks; no **Sync now** click is needed. Numbered revision copies such as `hash (1).json` and `hash(1).json`, copies with device/conflict suffixes, and changes in filename letter case are checked and merged by their content ID, so they do not interrupt sync or create extra notes. If only a renamed copy is present, PyClip restores the standard filename while keeping the copy. Missing folders and incomplete downloads are retried automatically. Damaged files or filenames whose hash does not match their contents still stop imports to protect your notes, and PyClip retries in case the desktop app replaces them with complete files.

Each note tab has a **Local only** checkbox below the editor and the same option in its right-click menu. Checked tabs show a lock and keep their current contents in this computer's local notes database. If the tab was shared, PyClip saves and verifies its shared revision files under `%APPDATA%\PyClip\local-note-revisions`, then removes those files from the shared folder. Other updated PyClip computers remove the shared tab on their next successful sync. A permanent, content-free removal record in `PyClip Notes/local-only` prevents an offline computer from uploading the old revisions again. Keep these records in place.

If the drive is unavailable or a local save fails, the status shows **shared copy removal pending** and retries automatically. Pending moves survive restarts and changes of sync folder; shared originals are kept until the local archive is verified. Closing the local tab does not cancel an unfinished move. Unchecking **Local only** explicitly shares the current contents again as a new shared tab. The global **Local only** mode stops ordinary note syncing, while previously requested per-tab moves still finish. Files already copied elsewhere, cloud trash/history, and older PyClip versions are outside this removal mechanism; run the updated app on every PC.

Notes, titles, colours, and tab order are shared. Clipboard history, images, DIR/FAV entries, and window preferences stay on the current PC. Existing notes from another PC are merged with your notes. Unused starter tabs are omitted when first connecting. Concurrent edits to the same note retain both versions, with a `(copy)` title on the extra version. Sync can import more than the normal 12-tab creation limit so that recovery notes are never dropped.

Choose **Local only** in the note-sync settings to stop ordinary syncing and keep your current notes. This global setting leaves existing cloud files in place, apart from explicit per-tab local moves. Reconnect the same folder to resume, or choose a different folder to start a new revision history containing your shareable notes. Shared revision files retain earlier note contents and deletion records so an offline PC cannot restore a stale version. Treat the folder as private note storage; do not edit or remove individual revision files. They are a PyClip sync format, not standalone text documents or Google Keep notes.

Sign-in is handled by the desktop sync app. PyClip does not request or store Google/Dropbox credentials. Google Keep integration and direct in-app account sign-in are not included.

Sync regression test: `python tests/note_sync_test.py` (isolated temporary profiles; no cloud account required).

Per-tab privacy regression test: `python tests/note_privacy_test.py` (isolated PCs; checks verified local moves, removal on other PCs, stale uploads, failed saves, offline retries, restarts, folder changes, pending sync cancellation, and sharing again).
