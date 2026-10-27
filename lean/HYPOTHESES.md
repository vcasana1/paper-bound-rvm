# Hypotheses of the main theorems

For each main theorem: every hypothesis as it is written in Lean, its source in the literature (author, year,
statement, DOI) and whether it is a **literature** input, a **numerical** input (a real number checked by
interval arithmetic outside Lean), or a **proved** fact (formerly a hypothesis, now a theorem of this library).
The numbering of theorems, lemmas and equations is that of the article *The Riemann–von Mangoldt clock*
(`rvm_clock_envelope`, v21). Sources are cited in the version in which the statement was checked (the copy in
the author's library), with the published version when it exists.

Lean guarantees that the conclusions follow from the hypotheses. It does **not** check that a hypothesis is
transcribed correctly from its source, nor that the hypotheses are satisfiable. Those two points are what an
external review has to verify, statement by statement, against the sources below.

## Branch B — Theorem 1.3, `RvmClock.ZetaFacts.theorem_1_3_lit` (`PaperMath/Papers/RvmClock/ZetaFacts.lean`)

Conclusion: for every `T ≥ e`, `|S(T)| ≤ 0.09783 log T + 0.7214 log log T + 10.6`, inequality (1.7).

The parameters are `c = cc = 1.000002`, `R = RR = 1.000005`, `σ♯ = sigS = c + (c − 1/2)²/R`,
`δ♯ = delS = 2c − σ♯ − 1/2`, `𝔡 = dd = log (R/(c − 1/2))` (`Explicit.lean`), and `eStar = 𝔢_E^*` is the reflected
explicit profile of §4.1 (`Profile.lean`). `sp σ t = σ + it`.

| Lean hypothesis | Statement | Source | Kind |
|---|---|---|---|
| `S : ℝ → ℝ` | the function `S(T)`; it enters only through `hdec` and `hplatt` | — | abstract datum |
| `I : ExplicitInputs` (`ZetaLines.lean`) | `I.hpy`: `‖ζ(1/2+it)‖ ≤ 0.618 |t|^{1/6} log|t|` for `3 < |t| ≤ e^105` | Hiary–Patel–Yang 2024, Thm. 1.1, doi:10.1016/j.jnt.2023.09.003 (Theorem 3.3(a)) | literature |
| | `I.py`: `‖ζ(1/2+it)‖ ≤ 66.7 |t|^{27/164}` for `|t| > e^105` | Patel–Yang 2024, Thm. 1.1, doi:10.1016/j.jnt.2024.03.011 (Theorem 3.3(a)) | literature |
| | `I.yang`: `‖ζ(σ_m+it)‖ ≤ 2 |t|^{1/(2^m−2)} log|t|` for `4 ≤ m ≤ 9`, `|t| ≥ 3`, `σ_m = 1 − m/(2^m−2)` | Yang 2024, Thm. 1.1, doi:10.1016/j.jmaa.2024.128124, **with constant 2 instead of 1.546** (Remark 4.5(ii) of the article: Yang's constant on `3 ≤ |t| ≤ T_m` is recomputed as 1.878 ≤ 2) | literature, not literal |
| | `I.patel`: `‖ζ(1+it)‖ ≤ log|t|` for `|t| ≥ 3` | Patel, arXiv:2009.00769v1, Thm. 1.1, doi:10.48550/arXiv.2009.00769 (published: Indag. Math. 33 (2022), doi:10.1016/j.indag.2022.04.007) (Theorem 3.3(c)) | literature |
| | ~~`I.zeta3`~~: `‖ζ(3+it)‖ ≤ 1.21` | `ZetaFacts.zeta3`: `‖ζ(s)‖ ≤ ζ(Re s) = ζ(3) ≤ 1.2024` (`Common.ZetaSeries.norm_zeta_le_zeta_re`, `Common.ZetaTail.zeta_three_le`) | **proved** |
| | `I.small`: `‖Ξ(s)‖ ≤ ‖s‖ + 2‖s‖‖s−1‖` for `1/2 ≤ σ ≤ 3`, `Ξ(s) = (s−1)ζ(s)` | consequence of Titchmarsh 1986, (2.1.4) | literature (consequence, not the formula itself) |
| | `I.pl`: Phragmén–Lindelöf for `Ξ` between two lines, `Q = 10`, `A = B = 2`, equal log powers | Fiori 2026, Cor. 3, doi:10.48550/arXiv.2502.13282 (Theorem 3.4); Rademacher 1959, doi:10.1007/BF01162949. The holomorphy and growth hypotheses on `Ξ` are classical and not checked | literature |
| ~~`chi : ℂ → ℂ`, `hFE`~~ | `ζ(s) = χ(s) ζ(1−s)`, `χ(s) = 2(2π)^{s−1} Γ(1−s) sin(πs/2)` | `ZetaFacts.chi`, `ZetaFacts.functional_equation` (for `Im s ≠ 0`), from Mathlib's `riemannZeta_one_sub` | **proved** (χ is now a definition) |
| `hchi` | `‖ZetaFacts.chi (σ+it)‖ ≤ 1.0070 (t/2π)^{1/2−σ}` for `−0.01 ≤ σ ≤ 1/2`, `t ≥ 98` | Lemma 4.3 of the article (from Stirling with remainder, DLMF §5.11(ii)); needs Stirling's formula with explicit remainder for `Complex.Gamma`, not in Mathlib | article lemma, not in Lean |
| `Z : ℝ → ℕ → ℝ`, `A0 D1 D2 E : ℝ → ℝ` | `Z T n = 𝒵_n(c,R)` at height `T`; `A0 = arg ζ(σ♯+iT)`-term, `D2 = Δ arg((s−1)ζ(s))` from `σ♯` to `1/2`, `D1 = Δ arg(s−1)`, `E T = 𝓔(T,δ♯)` | proof of Proposition 5.1; (3.2) | abstract data |
| `hA` | Theorem 3.5(a): for every even majorant `Ψ ≥ (1/n) log|𝔣_n(c+Re^{iθ})|` there is a subsequence with `limsup 𝒵_{n_m} ≤ log(ζ(c)/(√((c−1)²+T²) ζ(2c))) + (1/π)∫₀^π Ψ` | Bellotti–Wong, arXiv:2412.15470v2, Lemma 2.1 (published: Math. Comp., doi:10.1090/mcom/4133); Bellotti and Wong take it from Hasanalizade–Shen–Wong, Counting zeros of Dedekind zeta functions, Math. Comp. 91 (2022), Prop. 3.5, doi:10.1090/mcom/3665 (attribution of Bellotti–Wong; that paper is not in the author's library) | literature |
| `hB` | Theorem 3.5(b): `|D2| ≤ π 𝒵_n/(2𝔡) + 𝓔(T,δ♯)/2 + 3π/(2n) + π/4` for every `n ≥ 1` | Bellotti–Wong, arXiv:2412.15470v2, Lemma 2.3 (from Hasanalizade–Shen–Wong, Prop. 3.7, as attributed there); `𝓔(T,d)` is `E(0,d,T)` of Bennett–Martin–O'Bryant–Rechnitzer, arXiv:2005.02989v1, Def. 3.3 and Fig. 2 (compared term by term with Bellotti–Wong's formula), doi:10.48550/arXiv.2005.02989 (published: Math. Comp. 90 (2021), doi:10.1090/mcom/3599) | literature |
| `hEc` | Theorem 3.5(c): `𝓔(T,δ♯)/π ≤ (640δ♯ − 112)/(1536(3T−1)) + 2^{−10}` for `T ≥ 100` | Bennett et al., arXiv:2005.02989v1, Lemma 3.4 with `a = 0` (= Bellotti–Wong, Lemma 2.4) | literature |
| `hdec` | `π S(T) = A0 T + D2 T − D1 T` for `T ≥ 100` | decomposition of `π S(T)` used in Bellotti–Wong, §3 (proof of Proposition 5.1) | literature (classical) |
| `hA0` | `|A0 T| ≤ log ζ(σ♯)` | `|arg ζ(σ♯+iT)| ≤ |log ζ(σ♯+iT)| ≤ log ζ(σ♯)` (Euler product, §5 of the article) | literature (classical) |
| `hD1` | `D1 T = arctan((σ♯−1)/T) + arctan(1/(2T))` | elementary (§5 of the article) | literature (elementary) |
| ~~`hC1`~~ | `C₁ = (1/(2π𝔡)) ∫₀^π 𝔢_E^*(c + R cos θ) dθ ≤ 0.0978293` | `RvmClock.C1.C1_le` (`C1.lean`): exact piecewise integration, value `0.0978292318785…`, margin `6.8·10⁻⁸` | **proved** |
| `hplatt` | `|S(T)| ≤ 2.5167` for `e ≤ T ≤ 100` | Bellotti–Wong 2025, (1.2), from Platt 2017, doi:10.1090/mcom/3198 (Theorem 3.6) | literature (computation) |
| ~~`hzc`, `hz2c`, `hzeta`~~ | `0 < ζ(c)`, `0 < ζ(2c)`, `log(ζ(c)/ζ(2c)) ≤ 12.62467` | `RvmClock.ZetaConst` (`ZetaConst.lean`), margin `2.44·10⁻⁶` | **proved** |
| ~~`hzs`~~ | `log ζ(σ♯) ≤ 1.52499` | `RvmClock.ZetaSigS.log_zeta_sigS_le` (`ZetaSigS.lean`), margin `4.6·10⁻⁶` | **proved** |

`RvmClock.Thm13.theorem_1_3` (`Thm13.lean`) is the same theorem with `zc, z2c, zs` free and the five struck-out
lines as hypotheses; `Thm13.theorem_1_3_zeta` (`Thm13Zeta.lean`) instantiates `zc := ζ(c)`, `z2c := ζ(2c)`,
`zs := ζ(σ♯)` (Mathlib's `riemannZeta`, real part) and discharges four of them; `C1.theorem_1_3_numeric`
discharges `hC1` too; `ZetaFacts.theorem_1_3_lit` takes the six remaining fields of `ExplicitInputs` as separate
hypotheses, proves `zeta3` and the functional equation, and leaves the literature inputs and Lemma 4.3.

Intermediate results and their own hypotheses: `RvmClock.ZetaLines.lemma_4_4` (Lemma 4.4, hypotheses `I`,
`hFE`, `hchi`), `RvmClock.Backlund.master` (Proposition 5.1, general `c, R, K, h, Ω`), `RvmClock.Explicit.thm_1_3`
(the final deduction from the assembled bound (5.5)).

## Branch A — Theorem 1.5 and Corollary 1.6, `RvmClock.sublevel`, `RvmClock.proportion` (`Sublevel.lean`)

Data `Z : ZetaInputs` (`Inputs.lean`, extending `Ordinates` of `Gaps.lean`):

| Field | Statement | Meaning | Kind |
|---|---|---|---|
| `Z.γ : ℕ → ℝ`, `Z.mono`, `Z.unbounded` | monotone, unbounded sequence; `Z.N t = #{k : γ_k ≤ t}` | the ordinates `γ_{k+1}` (Lean index `k`), counted with multiplicity | abstract datum |
| `Z.varpi`, `Z.varpi_meas`, `Z.varpi_bound` | measurable, `|ϖ(t)| ≤ 1/t` for `t ≥ 1` | the Stirling remainder of the Riemann–Siegel theta; Lemma 4.1 gives `0.53/t` | abstract datum (Lemma 4.1 pending) |
| `Z.S := N − N₀ − ϖ/π` | definition | formula (1.1) used as the definition of `S` | definition |

| Lean hypothesis | Statement | Source | Kind |
|---|---|---|---|
| `hA : Z.FujiiA` (`Fourth.lean`) | `∃ A U₀, ∀ U ≥ U₀, ∫_U^{2U} |S(t) − (1/π) Im Σ_{p<U^{1/200}} p^{−1/2−it}|⁴ dt ≤ A U` | Fujii 1974, §3, pp. 232–233 (Selberg's expression with `x = T^{a₂/(60k)}`, the bounds `‖B_i‖ ≪ k² H^{1/(2k)}` for its five error terms, Lemma 5 for the primes in `[x³, Y)` with `A = 20/α_F`), doi:10.1090/S0002-9947-1974-0349603-2, with the corrections of Fujii 1981, §5, doi:10.1090/S0002-9947-1981-0621970-5 (Theorem 3.8(a), `k = 2`, `α_F = 1/5`, `H = T = U`, `Y = U^{1/200}`; Fujii's hypotheses `0 < a_i ≤ 1/2`, `q ≤ T^{1/4−a₁}`, `T^{1/2+a₂} ≤ H ≤ T` hold with `q = 1`, `a₂ = α_F`) | literature |
| `hB : Z.FujiiB` (`Inputs.lean`) | `∃ A T₀, ∀ T ≥ T₀, ∀ 0 < h ≤ 1, ∫_T^{2T} (S(t+h) − S(t))⁴ dt ≤ A T log²(2 + h log T)` | Fujii 1974, Main Theorem, p. 225 (`0 < a_i ≤ 1/2`, `T^{1/2+a₂} ≤ H ≤ T`, `0 < h ≤ H − (H/√T)^{1/8}`; the endpoints `a₂ = 1/2`, `H = T` are admitted), restated for `q = 1`, `H = T` in Fujii 1981, §1 (α), with `log(3 + h log T)` (`log(3+x) ≤ (log 3/log 2) log(2+x)`), and §5 (Theorem 3.8(b), `k = 2`, `α_F = 1/2`, `H = T`) | literature |
| `hTi : Z.Titchmarsh` (`Sublevel.lean`) | `S(t) = O(log t)` and `γ_{k+1} − γ_k → 0` | Titchmarsh 1986, §§9.4, 9.12 (Theorem 3.1) | literature (classical) |

Everything else in Branch A is proved without hypotheses: Lemma 7.2 (`maximal_cube_36`), the bathtub
inequalities, Theorem 7.3 (`transfer`, `transfer_36`; see the scope note below), §7.1 and Proposition 7.1
(`Construction.lean`), the Mertens-type bounds (`Mertens.lean`), Theorem 3.9 (`mean_value`, from the
Montgomery–Vaughan inequality `Zeta23.MV.mv_hilbert` ported from zeta23), Lemma 7.5 and Lemma 7.6.

Scope notes:
* `maximal_cube`, `maximal_cube_36` are the *window* form of Lemma 7.2 (maximal function over intervals inside
  the window), which is the form stated in the article and used in Theorem 7.3.
* `transfer_36` assumes, besides measurability of `f`, that `q_f²(q_f+1)²` is integrable on `(a,b]`; in the
  application (`Sublevel.lean`) this is proved, not assumed.
* Lemma 4.4: the intermediate constant of (4.5) is 2.7185 in Lean (2.7167 in the article); the final 2.74 is the same.

## Common

The lemmas of `PaperMath/Common/` have no hypotheses beyond their explicit arguments and depend only on the
standard axioms (`Audit.lean`).

## Corollaries 1.2, 1.4(a), Remark 5.2 — `RvmClock.LambdaB` (`LambdaB.lean`)

No hypotheses. `0.096816006 ≤ Λ(𝔢_B) ≤ 0.096816007` (`LambdaB_le`, `LambdaB_ge`), `2πΛ(𝔢_B) ≤ 0.60832`
(`two_pi_LambdaB_le`), `Λ(0) = (3√3 − π)/(12π log 2)` (`Lambda0_eq`), with `Λ` in the angular form
`(2π log 2)⁻¹ ∫₀^π 𝔢^*(1 + cos θ) dθ`. Not formalised: the passages to the limit of Theorem 1.1 and Corollary 1.2
(they use Bourgain's exponent pair, Theorem 3.7(c), and Lemma 4.3).

## Not formalised (status at v21)

* Theorem 1.1 and the limit in Corollary 1.2 (need Theorem 3.7, Lemma 4.3 and a uniform version of Proposition 5.1
  as `c, R → 1`); Corollary 1.4 (a), (b) and Proposition 6.2 (need the identification of `γ_k` with the zeros of
  `riemannZeta` and Lemma 6.1 in Lean); Lemma 4.1 and Lemma 4.3 (Stirling with explicit remainder for
  `Complex.Gamma`); Remark 7.7.
* The literature inputs listed above.
