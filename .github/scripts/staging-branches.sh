#!/bin/bash
# List the case studies that CI will test on a staging branch.
#
# On a PR from LemmaScript branch <b>, the case-study jobs clone
# <pinned>-<b> in place of the pinned branch when the case-study repo has
# one (see "Clone case study" in .github/workflows/ci.yml). This reports
# which case studies have such a branch.
#
#   .github/scripts/staging-branches.sh            # for the current branch
#   .github/scripts/staging-branches.sh <branch>   # for the given LemmaScript branch
#   .github/scripts/staging-branches.sh --all      # every staging branch, for any LemmaScript branch
#
# With `gh` installed, each line also shows how far the staging branch is
# ahead of and behind its pinned branch.
set -euo pipefail
cd "$(dirname "$0")/../.."

all=false
if [ "${1:-}" = "--all" ]; then
  all=true
else
  branch="${1:-$(git branch --show-current)}"
  if [ -z "$branch" ]; then
    echo "error: not on a branch; pass one explicitly" >&2
    exit 2
  fi
  if [ "$branch" = "main" ]; then
    echo "main always uses the pinned case-study branches."
    exit 0
  fi
fi

# The CI matrices are the source of truth: "<repo> <pinned branch> <backend>".
matrix=$(awk '
  /^  case-studies-dafny:/ { backend = "dafny" }
  /^  case-studies-lean:/  { backend = "lean" }
  /^  [a-z]/ && !/^  case-studies-/ { backend = "" }
  backend && /- repo:/  { repo = $3 }
  backend && /branch:/  { print repo, $2, backend }
' .github/workflows/ci.yml)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# One ls-remote per repository, in parallel.
while read -r repo; do
  ( if heads=$(git ls-remote --heads "https://github.com/$repo.git" 2>/dev/null); then
      echo "$heads" | sed 's#.*refs/heads/##' > "$tmp/$(echo "$repo" | tr / _)"
    else
      echo "$repo" >> "$tmp/unreachable"
    fi ) &
done < <(echo "$matrix" | awk '{ print $1 }' | sort -u)
wait

compare() {  # repo pinned staging
  command -v gh >/dev/null || return 0
  gh api "repos/$1/compare/$2...$3" --jq '"  (+\(.ahead_by) / -\(.behind_by) vs \("'"$2"'"))"' 2>/dev/null || true
}

found=0
# Group the backends of one (repo, pinned) pair onto one line.
while read -r repo pinned backends; do
  heads="$tmp/$(echo "$repo" | tr / _)"
  [ -s "$heads" ] || continue
  if $all; then
    candidates=$(grep "^$pinned-" "$heads" || true)
  else
    candidates=$(grep -Fx "$pinned-$branch" "$heads" || true)
  fi
  for staging in $candidates; do
    found=$((found + 1))
    printf '%-45s %s -> %s  [%s]%s\n' "$repo" "$pinned" "$staging" "$backends" "$(compare "$repo" "$pinned" "$staging")"
  done
done < <(echo "$matrix" | sort -u | awk '
  { key = $1 " " $2; if (key in b) b[key] = b[key] "," $3; else { b[key] = $3; order[++n] = key } }
  END { for (i = 1; i <= n; i++) print order[i], b[order[i]] }')

if [ "$found" -eq 0 ]; then
  if $all; then echo "No staging branches."
  else echo "No case study has a staging branch for '$branch'; CI uses the pinned branches."
  fi
fi
if [ -s "$tmp/unreachable" ]; then
  echo
  echo "Could not list branches (private or unreachable):" >&2
  sed 's/^/  /' "$tmp/unreachable" >&2
fi
