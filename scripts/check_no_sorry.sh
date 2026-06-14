#!/usr/bin/env bash
set -euo pipefail
if grep -R -E --line-number --include='*.lean' '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' IrrationalityAr IrrationalityAr.lean; then
  echo
  echo 'Certification blocked: unresolved Lean proof holes remain.' >&2
  exit 1
fi
echo 'No Lean proof holes found.'
