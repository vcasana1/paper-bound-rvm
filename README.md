# The Riemann–von Mangoldt clock (`paper-bound-rvm`)

Víctor Casaña-Giner (ORCID [0000-0002-8252-2608](https://orcid.org/0000-0002-8252-2608)).

Article *The Riemann–von Mangoldt clock* (`rvm_clock_envelope`), with the programs of its Appendix A and the
Lean 4 verification of its Appendix B.

```
article/   rvm_clock_envelope_v23.tex (.txt: identical copy), .pdf, _tips.tex (hover tooltips, read by the .tex)
article/code/
           constantes_v5.py      constants of Theorems 1.1, 1.3 and Corollary 1.2 (mpmath), with its output
           yang_smallt_arb.py    Arb certificate of Remark 4.5(ii) (python-flint), with its output
           casanya_method.py     Casaña's method of Section 7.1: x_k for k ≤ 20 against γ_k and τ_k, with its output
           gen_tips.py           generates the tooltips file from the .tex and .aux
           *_py.txt              copies of the .py files
lean/      the Lake project (Lean 4.36.0-rc1, Mathlib v4.36.0-rc1): PaperMath/Common, PaperMath/Papers/RvmClock,
           Audit.lean, Audit_output.txt, HYPOTHESES.md (every hypothesis of the main theorems with its source),
           scripts/audit.sh; see lean/README.md
.github/   CI: builds the Lean library and audits the axioms on every push
```

Compile the article: in `article/`, `pdflatex rvm_clock_envelope_v23` four times (optionally
`python3 -I code/gen_tips.py rvm_clock_envelope_v23` after the second run to regenerate the tooltips file).

Build the proofs: in `lean/`, `lake exe cache get && lake build && lake env lean Audit.lean`, or `sh scripts/audit.sh`.
Every result depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

The canonical, reusable copy of the Lean library is [`vcasana1/PaperMath`](https://github.com/vcasana1/PaperMath);
`lean/` is its snapshot at commit `31b096c` (the article cites commit `97f4e7c`, which differs from it only in
documentation and removed unused files).
