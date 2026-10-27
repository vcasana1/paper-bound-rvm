# PaperMath

Lean 4 formalisations accompanying the articles of Víctor Casaña-Giner
(ORCID [0000-0002-8252-2608](https://orcid.org/0000-0002-8252-2608)).
Lean `4.36.0-rc1`, Mathlib `v4.36.0-rc1` (rev `625d8914199bc567cca9b91f90e8e5afafa5ae51`), fixed by
`lean-toolchain` and `lake-manifest.json`.

No `sorry`, no axioms of our own: every result depends only on `propext`, `Classical.choice`, `Quot.sound`
(checked by `Audit.lean` / `scripts/audit.sh`, run in CI; the output of the last run is `Audit_output.txt`).
What is assumed is stated as explicit hypotheses of the theorems and listed, with sources, in
[`HYPOTHESES.md`](HYPOTHESES.md).

## Layout

```
lakefile.toml, lean-toolchain, lake-manifest.json   the Lake project (library `PaperMath`, root `PaperMath.lean`)
PaperMath/Common/        lemmas reusable across articles (import these from any paper)
PaperMath/Papers/<Name>/ one directory per article; imports Common, never another paper
Audit.lean               #print axioms of every main result
scripts/audit.sh         build + audit, fails on sorry / unexpected axioms
.github/workflows/ci.yml the same, on every push
```

### `Common/`

| Module | Contents |
|---|---|
| `Common.ZetaSeries` | `ζ(s) = ∑ n^{-s}` for real `s > 1` (`zeta_re_eq_tsum`); `ζ(1+s) ≤ 1 + 1/s`; `ζ(2+ε) ≥ π²/6 − εK`, `K ≤ 1.0116398448`; `1 ≤ ζ(s)`; `‖ζ(s)‖ ≤ ζ(Re s)` |
| `Common.ZetaTail` | midpoint rule `x^{-σ} ≤ ∫_{x-1/2}^{x+1/2} t^{-σ}` (via AM–GM); `ζ(σ) ≤ ∑_{n<N} n^{-σ} + (N−1/2)^{1-σ}/(σ−1)`; rational bounds `x^{-(p/r+ε)} ≤ q` from `1 ≤ q₁^r x^p` and `k log 2 + 1 − 2^k/x ≤ log x` (`rpow_neg_add_le`); `ζ(3) ≤ 1.2024` |
| `Common.LogBounds` | two-sided Taylor bounds for `log(1−x)`, `0 ≤ x < 1`, with rational remainder; `log 3` to 10 digits |
| `Common.TrigBounds` | alternating Taylor bounds for `sin x` (`x² ≤ 6`) and `cos x` (`x² ≤ 2`), `arcsin y` from `sin`, rational bounds for `√y`; with `norm_num` they give `arcsin`/`arccos` of rationals to any precision |
| `Common.HingeIntegral` | exact angular integrals for Backlund's method: with `σ = c + R cos θ`, `∫₀^{θ_h} max 0 (σ − a) = (c − a)θ_a + R sin θ_a` and `∫_{θ_h}^π max 0 (1 − σ − a) = (1 − c − a)(π − θ'_a) + R sin θ'_a` (`1/2 ≤ a ≤ 1`), with `θ_a = π/2 + arcsin((c−a)/R)`, `sin θ_a = √(1 − ((a−c)/R)²)`; any piecewise linear profile reduces to these |
| `Common.Zeta23Port` | the generalised Hilbert inequality of Montgomery–Vaughan, `Zeta23.MV.mv_hilbert`, ported from [zeta23](https://github.com/anthropics/formal-math/tree/main/zeta23) (Anthropic, Apache-2.0; see `Common/Zeta23Port/README.md`, `LICENSE`, `NOTICE_zeta23`) |

### `Papers/RvmClock/` — *The Riemann–von Mangoldt clock* (`rvm_clock_envelope`, v22)

Namespaces `RvmClock`, `RvmClock.Profile`, `RvmClock.ZetaLines`, `RvmClock.Backlund`, `RvmClock.Explicit`,
`RvmClock.Thm13`, `RvmClock.ZetaConst`, `RvmClock.ZetaSigS`.

| Article | Lean | File |
|---|---|---|
| Lemma 7.2 (discrete maximal inequality; window form, constant 24 and 36) | `maximal_cube`, `maximal_cube_36` | `Maximal.lean` |
| inequality (7.4), bathtub | `bathtub_right`, `bathtub_left` | `Bathtub.lean` |
| **Theorem 7.3** (sublevel transfer), with `∫ q_f⁴` and `2·24^{1/3}` as in the article; variant with constant 36 | `transfer` (via `transfer_24`), `transfer_36` | `Transfer.lean` |
| (1.10)–(1.12), §7.1, (7.1), (7.2), **Proposition 7.1** (prime-corrected clock) | `abs_PhiM_le`, `abs_Phi_le_sqrt`, `continuousOn_F`, `xClock_pos`, `xClock_lt_succ`, `Sub_subset_two_tau`, `budget_le_two_sqrt`; `casanya_method` (= `xClock`, the name of the method) | `Construction.lean` |
| Theorem 3.9 (Montgomery–Vaughan mean value) | `mean_value` | `MeanValue.lean` |
| Theorem 3.10 (Mertens-type bounds, proved from Chebyshev) | `sum_log_div_le`, `sum_inv_prime_le`, `nth_prime_le_sq` | `Mertens.lean` |
| Lemma 7.5, combinatorial part; abstract ordinates | `sum_cube_le`, `Ordinates.sum_D_le_two_vol` | `Gaps.lean` |
| `ZetaInputs`, Fujii (b) as hypothesis, **Lemma 7.5** | `ZetaInputs.FujiiB`, `ZetaInputs.gaps_third_moment` | `Inputs.lean` |
| fourth moment of prime Dirichlet polynomials (`𝒟₁`, `𝒟₂`) | `prime_fourth_moment` | `PrimeFourth.lean` |
| Euler-phase expansion, `phase_split` | `eulerArg_expand`, `PhiM_expand` | `Phase.lean` |
| Fujii (a) as hypothesis, **Lemma 7.6** | `ZetaInputs.FujiiA`, `fourth_moment` | `Fourth.lean` |
| Theorem 3.1 as hypothesis, **Theorem 1.5**, **Corollary 1.6** | `ZetaInputs.Titchmarsh`, `sublevel`, `casanya_method_sublevel`, `proportion` | `Sublevel.lean` |
| §4.1 explicit profile `𝔢_E`, reflection `𝔢_E^*`, (1.4) | `Profile.gE`, `Profile.eStar`, `eStar_continuous`, `eStar_nonneg` | `Profile.lean` |
| Theorem 3.3 and 3.4 as hypotheses (`ExplicitInputs`), (4.4) on one line, interpolation | `ZetaLines.ExplicitInputs`, `ZetaLines.line_bound`, `ZetaLines.strip` | `ZetaLines.lean` |
| (4.4) on the nine lines, `|Ξ(s)| ≤ 2|Q+s|^{1+𝔢_E(σ)}|Log(Q+s)|` | `ZetaLines.half_three` | `ZetaNodes.lean` |
| **Lemma 4.4** `|ζ(σ+it)| ≤ 2.74 t^{𝔢_E^*(σ)} log t` | `ZetaLines.lemma_4_4` | `ZetaBound.lean` |
| **Proposition 5.1** (Backlund on a disc), Theorem 3.5 as hypotheses | `Backlund.master` | `Backlund.lean` |
| `C₂`, conditions (3.3), `𝓔/(2π) < 0.00055`, final deduction of (1.7), (1.8) | `Explicit.C2_le`, `backlund_conditions`, `E_bound`, `explicit_S`, `explicit_N`, `thm_1_3` | `Explicit.lean` |
| **Theorem 1.3**, (1.7), from the literature; `zc, z2c, zs` free | `Thm13.theorem_1_3` | `Thm13.lean` |
| `log(ζ(c)/ζ(2c)) ≤ 12.62467`, `c = 1.000002` | `ZetaConst.log_zeta_ratio_le` | `ZetaConst.lean` |
| `ζ(σ♯) ≤ 4.595076613723`, `log ζ(σ♯) ≤ 1.52499`, `σ♯ = 1.25000275000025` | `ZetaSigS.zeta_sigS_le`, `ZetaSigS.log_zeta_sigS_le` | `ZetaSigS.lean` |
| **Theorem 1.3** with `ζ(c)`, `ζ(2c)`, `ζ(σ♯)` instantiated and proved | `Thm13.theorem_1_3_zeta` | `Thm13Zeta.lean` |
| `C₁ = (1/(2π𝔡)) ∫₀^π 𝔢_E^*(c + R cos θ) dθ` in closed form (exact piecewise integration) and `C₁ ≤ 0.0978293` | `C1.integral_eStar_eq`, `C1.C1_le` | `C1.lean` |
| **Theorem 1.3** with every numerical input proved | `C1.theorem_1_3_numeric` | `C1.lean` |
| `\|ζ(3+it)\| ≤ 1.21`; `χ(s) = 2(2π)^{s-1}Γ(1-s) sin(πs/2)` and the functional equation `ζ(s) = χ(s) ζ(1-s)` (from Mathlib's `riemannZeta_one_sub`); **Theorem 1.3** with only the literature inputs and Lemma 4.3 as hypotheses | `ZetaFacts.zeta3`, `ZetaFacts.chi`, `ZetaFacts.functional_equation`, `ZetaFacts.theorem_1_3_lit` | `ZetaFacts.lean` |
| `𝔢_B` (Bourgain profile, nodes from the A-process: `pair_j`, `gB_node_j`); `∫₀^π 𝔢_B^*(1+cos θ) dθ` in closed form; **Corollary 1.2**: `0.096816006 ≤ Λ(𝔢_B) ≤ 0.096816007`; **Corollary 1.4(a)**: `2πΛ(𝔢_B) ≤ 0.60832`; Remark 5.2: `Λ(0) = (3√3 − π)/(12π log 2)` | `LambdaB.integral_eBStar_eq`, `LambdaB.LambdaB_le`, `LambdaB.LambdaB_ge`, `LambdaB.two_pi_LambdaB_le`, `LambdaB.Lambda0_eq` | `LambdaB.lean` |

Remaining hypotheses of `theorem_1_3_lit`: the literature inputs of `HYPOTHESES.md` and Lemma 4.3 (`hchi`, now a
statement about the explicit `chi`; it needs Stirling's formula with remainder for the complex Gamma function,
which Mathlib does not have). Pending: the ζ layer of Theorem 1.5 (instantiating
`ZetaInputs` with the zeros of `riemannZeta`, Lemma 4.1, Theorem 3.1); the Selberg–Fujii inputs.

`scripts/constantes_v5.py`, `scripts/constantes_v5_output.txt`: the program of Appendix A of the article (Python 3.13,
mpmath 1.4.1; constants `Λ(𝔢_B)`, `C₁`, `C₂`, `C₃(100)`, crossings with Bellotti–Wong and with Yang's (4.29); the angular
integral both by quadrature and by the closed form (5.3)) and its output. `scripts/casanya_method.py`, `scripts/casanya_method_output.txt`: Casaña's method of Section 7.1 (`x_k`, `k ≤ 20`, against `γ_k` and the clock `τ_k`; illustration). `scripts/yang_smallt_arb.py`,
`scripts/yang_smallt_arb_output.txt`: the Arb certificate of Remark 4.5(ii) (constant `1.87781 ≤ 2` on `3 ≤ t ≤ T_m`, `4 ≤ m ≤ 9`). `scripts/gen_sigs.py`, `scripts/gen_c1.py`, `scripts/gen_lambdaB.py`
generate the rational certificates of `ZetaSigS.lean`, `C1.lean` and `LambdaB.lean` (`gen_lambdaB_output.txt`: its checks).

## Building

```
lake exe cache get   # Mathlib oleans (needs network); otherwise lake builds Mathlib from source
lake build
lake env lean Audit.lean
```
or `sh scripts/audit.sh`, which does the three and fails on `sorry`, `sorryAx` or any non-standard axiom.
Single file: `lake env lean PaperMath/Papers/RvmClock/ZetaSigS.lean` (after its imports are built).

## How to cite

Cite the commit: "V. Casaña-Giner, PaperMath: Lean 4
formalisations, `https://github.com/vcasana1/PaperMath`, commit `<sha>`". The article's Appendix B names the
commit it refers to.
