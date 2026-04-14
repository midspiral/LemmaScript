#!/usr/bin/env bash
# Regenerate and verify LemmaScript artifacts.
# Usage: ./check.sh <lean|dafny|dafny-slow> [file.ts ...]
#
# LemmaScript-files.txt format:  filepath [timeout_in_seconds] [extra dafny flags...]
# No timeout = use Dafny default.
#
# dafny:      verify files with timeout <= 60, gen-check the rest
# dafny-slow: verify all files with their specified timeout
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LSC="npx --prefix $SCRIPT_DIR tsx $SCRIPT_DIR/src/lsc.ts"
CI_LIMIT=60

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
  for entry in "${FILES[@]}"; do
    local f="${entry%% *}"
    $LSC gen --backend=lean "$f"
  done
  lake build
}

parse_entry() {
  # Sets: E_FILE, E_TIMEOUT, E_FLAGS
  local entry="$1"
  read -r E_FILE E_TIMEOUT E_FLAGS <<< "$entry"
  if ! [ "$E_TIMEOUT" -gt 0 ] 2>/dev/null; then
    E_FLAGS="$E_TIMEOUT $E_FLAGS"
    E_TIMEOUT=""
  fi
  E_FLAGS="${E_FLAGS# }"
}

check_dafny() {
  for entry in "${FILES[@]}"; do
    parse_entry "$entry"
    if [ -n "$E_TIMEOUT" ] && [ "$E_TIMEOUT" -gt "$CI_LIMIT" ] 2>/dev/null; then
      echo "=== $(basename "$E_FILE") (timeout ${E_TIMEOUT}s > ${CI_LIMIT}s, gen-check only) ==="
      $LSC gen-check --backend=dafny "$E_FILE"
    else
      $LSC check --backend=dafny ${E_TIMEOUT:+--time-limit=$E_TIMEOUT} ${E_FLAGS:+--extra-flags="$E_FLAGS"} "$E_FILE"
    fi
  done
}

check_dafny_slow() {
  for entry in "${FILES[@]}"; do
    parse_entry "$entry"
    $LSC check --backend=dafny ${E_TIMEOUT:+--time-limit=$E_TIMEOUT} ${E_FLAGS:+--extra-flags="$E_FLAGS"} "$E_FILE"
  done
}

case "$backend" in
  lean)       check_lean ;;
  dafny)      check_dafny ;;
  dafny-slow) check_dafny_slow ;;
  all)        check_lean; check_dafny ;;
  *)
    echo "Usage: check.sh [lean|dafny|dafny-slow] [file.ts ...]"
    exit 1
    ;;
esac
