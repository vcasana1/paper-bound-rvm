#!/bin/sh
# Builds the library, runs Audit.lean and fails if any declaration depends on an axiom other than
# propext, Classical.choice, Quot.sound (or on sorryAx), or if any source contains `sorry`.
set -e
cd "$(dirname "$0")/.."
lake build
lake env lean Audit.lean | tee Audit_output.txt
if grep -q "sorryAx" Audit_output.txt; then echo "FAIL: sorryAx"; exit 1; fi
if grep "depends on axioms" Audit_output.txt | grep -v "\[propext, Classical.choice, Quot.sound\]" | grep -q .; then
  echo "FAIL: unexpected axioms"; exit 1; fi
if grep -rn --include='*.lean' -E "\bsorry\b|^axiom " PaperMath | grep -q .; then
  echo "FAIL: sorry or axiom in sources"; grep -rn --include='*.lean' -E "\bsorry\b|^axiom " PaperMath; exit 1; fi
echo "AUDIT OK"
