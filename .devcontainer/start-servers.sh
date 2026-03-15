#!/usr/bin/env bash
# Start the Vite dev server and CSL check proxy in the background.
# Logs go to editor/vite.log and editor/server.log.
set -euo pipefail

EDITOR_DIR="$(cd "$(dirname "$0")/.." && pwd)/editor"

echo "Starting Vite dev server (port 3000)..."
cd "$EDITOR_DIR"
nohup npm run dev > vite.log 2>&1 &
echo "  PID $! → editor/vite.log"

echo "Starting CSL check proxy (port 4170)..."
nohup npm run server > server.log 2>&1 &
echo "  PID $! → editor/server.log"
