#!/bin/sh
# Check every proof and fail on errors or on any `sorry`.
set -e
for f in */*.lean; do
  echo "== $f"
  out=$(lean "$f" 2>&1) || { echo "$out"; exit 1; }
  echo "$out" | grep -q "sorry" && { echo "$out"; echo "uses sorry"; exit 1; }
done
echo "all proofs check"
