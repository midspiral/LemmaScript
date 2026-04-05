#!/usr/bin/env bash
# Regenerate and verify LemmaScript artifacts.
# Usage: ./check.sh <lean|dafny> [file.ts ...]
# If no files given, reads from LemmaScript-files.txt in the working directory.
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LSC="npx tsx $SCRIPT_DIR/src/lsc.ts"

backend="$1"; shift

FILES=()
if [ $# -gt 0 ]; then
  FILES=("$@")
else
  if [ ! -f "LemmaScript-files.txt" ]; then
    echo "No files given and no LemmaScript-files.txt found."
    exit 1
  fi
  while IFS= read -r line || [ -n "$line" ]; do
    [ -n "$line" ] && FILES+=("$line")
  done < LemmaScript-files.txt
fi

case "$backend" in
  lean)
    for f in "${FILES[@]}"; do $LSC gen "$f"; done
    lake build
    ;;
  dafny)
    for f in "${FILES[@]}"; do $LSC check --backend=dafny "$f"; done
    ;;
  *)
    echo "Usage: check.sh <lean|dafny> [file.ts ...]"
    exit 1
    ;;
esac
