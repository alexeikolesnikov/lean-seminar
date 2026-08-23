#!/usr/bin/env bash
#
# weblink.sh -- turn a file in this repository into a no-install link.
#
# Prints a URL that opens the file in the Lean 4 web editor
# (https://live.lean-lang.org), which runs Lean and Mathlib in a browser tab
# with no account and nothing to install. The link points at the *raw file on
# GitHub*, so it always serves whatever is on the branch -- edit, push, and the
# link you already emailed is current.
#
#   bash scripts/weblink.sh Seminar/Session01_Demo/Demo.lean
#
# Options:
#   -b BRANCH   branch to link to (default: the current branch)
#   -n          do not check that the link resolves (offline use)
#
# Environment:
#   SEMINAR_REPO   owner/name; default is read from `git remote get-url origin`
#   LEAN_WEB       editor base URL; default https://live.lean-lang.org
#
# ---------------------------------------------------------------------------
# IMPORTANT, and worth saying to the room: the web editor serves the *latest*
# Mathlib, not the v4.33.0 this seminar pins. A file that compiles in CI can
# still fail here after an upstream rename. Click the link yourself before you
# send it -- that click is the only check there is.
# ---------------------------------------------------------------------------
set -euo pipefail

BRANCH=""
CHECK=1
while getopts ":b:n" opt; do
  case "$opt" in
    b) BRANCH="$OPTARG" ;;
    n) CHECK=0 ;;
    *) echo "usage: $0 [-b BRANCH] [-n] PATH" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))

if [ $# -ne 1 ]; then
  echo "usage: $0 [-b BRANCH] [-n] PATH" >&2
  exit 2
fi
FILE="$1"

cd "$(git rev-parse --show-toplevel)"

# --- which repository, which branch ---------------------------------------
if [ -z "${SEMINAR_REPO:-}" ]; then
  origin=$(git remote get-url origin 2>/dev/null || true)
  if [ -z "$origin" ]; then
    echo "error: no git remote 'origin'; set SEMINAR_REPO=owner/name" >&2
    exit 1
  fi
  # https://github.com/owner/name.git  or  git@github.com:owner/name.git
  SEMINAR_REPO=$(printf '%s' "$origin" \
    | sed -E 's#^(https://github\.com/|git@github\.com:)##; s#\.git$##')
fi
[ -n "$BRANCH" ] || BRANCH=$(git rev-parse --abbrev-ref HEAD)

# --- the file has to exist, and has to be the file they will see -----------
if [ ! -f "$FILE" ]; then
  echo "error: no such file: $FILE" >&2
  exit 1
fi

if ! git diff --quiet -- "$FILE" 2>/dev/null || ! git diff --quiet --cached -- "$FILE" 2>/dev/null; then
  echo "warning: $FILE has uncommitted changes -- the link will serve the committed version." >&2
fi

if git rev-parse --verify --quiet "origin/${BRANCH}" >/dev/null; then
  if ! git diff --quiet "origin/${BRANCH}" -- "$FILE"; then
    echo "warning: $FILE differs from origin/${BRANCH} -- push before sending the link." >&2
  fi
else
  echo "warning: no origin/${BRANCH} locally; cannot tell whether $FILE is pushed." >&2
fi

# --- build the link --------------------------------------------------------
RAW="https://raw.githubusercontent.com/${SEMINAR_REPO}/${BRANCH}/${FILE}"

urlencode() {
  local s="$1" i c out=""
  for (( i = 0; i < ${#s}; i++ )); do
    c=${s:i:1}
    case "$c" in
      [A-Za-z0-9.~_-]) out+="$c" ;;
      *) printf -v c '%%%02X' "'$c"; out+="$c" ;;
    esac
  done
  printf '%s' "$out"
}

LINK="${LEAN_WEB:-https://live.lean-lang.org}/#url=$(urlencode "$RAW")"

# --- does it actually resolve? --------------------------------------------
if [ "$CHECK" -eq 1 ] && command -v curl >/dev/null 2>&1; then
  code=$(curl -s -o /dev/null -w '%{http_code}' -I "$RAW" || echo 000)
  if [ "$code" != "200" ]; then
    echo "error: $RAW returned HTTP ${code}." >&2
    echo "       Usually this means the branch or the file has not been pushed." >&2
    exit 1
  fi
fi

printf '%s\n' "$LINK"
