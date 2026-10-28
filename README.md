PyClip

PyClip is a lightweight clipboard manager for Windows. It runs in the system tray and keeps a searchable history of copied text, images, and files, so you can quickly reuse something you copied earlier without having to find and copy it again.

Typical use case

PyClip is useful when you regularly move between documents, emails, code, screenshots, file paths, or other applications and need access to more than just the most recent clipboard item.

Press Ctrl + Shift + Alt + V (or click the tray icon) to open the clipboard history, search for an item, and paste it back into the application you were using.

The app also includes:

Pinning for frequently reused clipboard items

Multi-item selection

A small tabbed notepad for temporary notes

A directory history for quickly reopening or copying previously used folder locations

Local clipboard storage with automatic cleanup

Run

pythonw pyclip.pyw

Use python pyclip.pyw instead if you want to see console/log output.

Opening `pyclip.pyw` shows the window. Opening it again brings the running copy forward. Automatic Windows login launches stay in the tray.

Note sync (optional)

Local-only storage is the default. To share PyClip notes between PCs:

1. Install and sign in to Google Drive for desktop or the Dropbox desktop app.
2. Open **Note sync…** from PyClip's tray menu, or click the status at the bottom of the notepad.
3. Choose **Google Drive folder** or **Dropbox folder**, select a folder in that signed-in account, and save. An **Other synced folder** option also supports another sync client or a shared drive.
4. On each other PC, select the same cloud folder in PyClip. The local folder paths can differ. Keep the folder available offline and let the desktop app finish downloading existing files.

PyClip creates a `PyClip Notes/revisions` subfolder. Notes save locally after a short typing pause. Folder updates run in the background after edits, and PyClip checks for changes every 15 seconds while it is running, including when hidden in the tray. Offline edits are retried automatically. **Sync now** runs an immediate check. “Folder updated” confirms the local folder exchange; Google Drive or Dropbox controls when cloud uploads and downloads finish.

Notes, titles, colours, and tab order are shared. Clipboard history, images, DIR/FAV entries, and window preferences stay on the current PC. Existing notes from another PC are merged with your notes. Unused starter tabs are omitted when first connecting. Concurrent edits to the same note retain both versions, with a `(copy)` title on the extra version. Sync can import more than the normal 12-tab creation limit so that recovery notes are never dropped.

Choose **Local only** to stop syncing and keep your current notes. Existing cloud files remain. Reconnect the same folder to resume, or choose a different folder to start a new revision history containing your current notes. Revision files retain earlier note contents and deletion records so an offline PC cannot restore a stale version. Treat the folder as private note storage; do not edit or remove individual revision files. They are a PyClip sync format, not standalone text documents or Google Keep notes.

Sign-in is handled by the desktop sync app. PyClip does not request or store Google/Dropbox credentials. Google Keep integration and direct in-app account sign-in are not included.

Sync regression test: `python tests/note_sync_test.py` (isolated temporary profiles; no cloud account required).
