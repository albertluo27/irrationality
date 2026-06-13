#!/usr/bin/env bash
set -euo pipefail
if grep -R --line-number --include='*.lean' '\bsorry\b' IrrationalityAr IrrationalityAr.lean; then
  echo
  echo 'Certification blocked: unresolved Lean proof holes remain.' >&2
  exit 1
fi
echo 'No Lean proof holes found.'
