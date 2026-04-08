#!/usr/bin/env bash
# Regenerate and verify LemmaScript artifacts.
# Usage: ./check.sh <lean|dafny> [file.ts ...]
# If no files given, reads from LemmaScript-files.txt in the working directory.
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LSC="npx --prefix $SCRIPT_DIR tsx $SCRIPT_DIR/src/lsc.ts"

backend="${1:-all}"; shift 2>/dev/null || true

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

check_lean() {
  for f in "${FILES[@]}"; do $LSC gen --backend=lean "$f"; done
  lake build
}

check_dafny() {
  for f in "${FILES[@]}"; do $LSC check --backend=dafny "$f"; done
}

case "$backend" in
  lean)   check_lean ;;
  dafny)  check_dafny ;;
  all)    check_lean; check_dafny ;;
  *)
    echo "Usage: check.sh [lean|dafny] [file.ts ...]"
    exit 1
    ;;
esac
