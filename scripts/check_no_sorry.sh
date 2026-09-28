#!/usr/bin/env bash
set -euo pipefail
if grep -RIn --include='*.lean' -E '\bsorry\b|\badmit\b' JSP523 JSP523.lean; then
  echo 'Found sorry/admit in Lean sources.' >&2
  exit 1
fi
echo 'No sorry/admit found in Lean sources.'
