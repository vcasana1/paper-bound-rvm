import PaperMath.Common.ZetaTail
import PaperMath.Common.LogBounds
import PaperMath.Papers.RvmClock.Explicit

/-!
# The numerical input `log ζ(σ♯) ≤ 1.52499` of Theorem 1.3

`σ♯ = c + (c - 1/2)²/R = 1.25000275000025 = 5/4 + ε₀`, `ε₀ = 1375007 / 500002500000` (exact), with `c = 1.000002`,
`R = 1.000005` (`RvmClock.Explicit.sigS`). Value: `log ζ(σ♯) = 1.5249835587…`; margin `6.4 · 10⁻⁶`.

Proof, all for Mathlib's `riemannZeta`:
* `ζ(σ♯) ≤ ∑_{n<50} n^{-σ♯} + (49.5)^{1-σ♯}/(σ♯-1)` (midpoint rule, `Common.ZetaTail.zeta_le_partial_add_tail`;
  the error of the tail is `≈ σ♯ · 50^{-σ♯-1}/24 < 8 · 10⁻⁶`);
* each `n^{-σ♯} = n^{-5/4} n^{-ε₀}` is bounded by a 12-digit decimal with `Common.ZetaTail.rpow_neg_add_le`
  (`1 ≤ q₁⁴ n⁵` and `n^{-ε₀} ≤ 1/(1 + ε₀ (k log 2 + 1 - 2^k/n))`, `2^k ≤ n`), every check by `norm_num`;
* the resulting bound is `ζ(σ♯) ≤ 4.595076613723` (true value `4.5950680197…`), and
  `log 4.595076613723 = 3 log 2 + log (1 - x)`, `x = 1 - 4.595076613723/8`, is bounded by the Taylor series with
  remainder (`Common.LogBounds.log_one_sub_le`, 36 terms) and `Real.log_two_lt_d9`.
-/

open Finset Common.ZetaTail Common.LogBounds RvmClock.Explicit

namespace RvmClock.ZetaSigS

/-- `ε₀ = σ♯ - 5/4`, exactly. -/
lemma sigS_eq : sigS = 5 / 4 + (1375007 / 500002500000 : ℝ) := by
  unfold sigS cc RR; norm_num

lemma one_lt_sigS : 1 < sigS := by rw [sigS_eq]; norm_num

lemma sigS_pos : 0 < sigS := by linarith [one_lt_sigS]

/-- One term: `1/n^{σ♯} ≤ q` from the rational data `k, q₁, q`. -/
lemma term (n k : ℕ) (q₁ q : ℝ) (hn : 1 ≤ n) (hk : (2 : ℝ) ^ k ≤ n) (hq₁ : 0 < q₁)
    (h₁ : 1 ≤ q₁ ^ 4 * (n : ℝ) ^ 5)
    (hq : q₁ ≤ q * (1 + 1375007 / 500002500000 * (k * 0.6931471803 + (1 - 2 ^ k / (n : ℝ))))) :
    1 / (n : ℝ) ^ sigS ≤ q := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [one_div, ← Real.rpow_neg (show (0 : ℝ) ≤ n by linarith), sigS_eq]
  exact rpow_neg_add_le 5 4 k (by norm_num) (by norm_num) hn' (by norm_num) hk hq₁ h₁ hq


/-- `∑_{n<50} 1/n^{σ♯} ≤ 3.087083518448` (the terms `n = 0` and `n = 1` are `0` and `1`; the others are the
rational bounds of `term`). -/
lemma partial_sum_le : ∑ n ∈ range 50, 1 / (n : ℝ) ^ sigS ≤ 3.087083518448 := by
  have t0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ sigS = 0 := by
    simp [Real.zero_rpow sigS_pos.ne']
  have t1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ sigS = 1 := by simp
  have t2 := term 2 1 0.420448207627 0.42044740619 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 := term 3 1 0.253278561884 0.253277846926 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 := term 4 2 0.176776695297 0.176776021373 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 := term 5 2 0.133748060996 0.133747477549 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 := term 6 2 0.106490517375 0.106490013787 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 := term 7 2 0.087826878994 0.087826440663 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 := term 8 3 0.074325444688 0.074325019663 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 := term 9 3 0.06415002991 0.064149643472 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 := term 10 3 0.05623413252 0.056233780021 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 := term 11 3 0.049918226071 0.049917903179 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 := term 12 3 0.04477374716 0.044773450083 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 := term 13 3 0.040510799066 0.040510524561 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 := term 14 3 0.036926653855 0.036926399173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 := term 15 3 0.033875516544 0.033875279357 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 := term 16 4 0.03125 0.031249761733 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 := term 17 4 0.028969356501 0.028969130937 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 := term 18 4 0.026971765095 0.026971551206 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 := term 19 4 0.025209138182 0.025208935028 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t20 := term 20 4 0.023643540226 0.023643346951 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t21 := term 21 4 0.022244665607 0.022244481437 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t22 := term 22 4 0.02098802868 0.020987852915 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t23 := term 23 4 0.019853642848 0.019853474857 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t24 := term 24 4 0.018825041742 0.018824880954 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t25 := term 25 4 0.01788854382 0.017888389719 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t26 := term 26 4 0.017032692857 0.017032544976 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t27 := term 27 4 0.016247827321 0.016247685236 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t28 := term 28 4 0.015525745427 0.015525608753 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t29 := term 29 4 0.014859442051 0.014859310437 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t30 := term 30 4 0.014242900214 0.014242773341 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t31 := term 31 4 0.013670924433 0.013670802008 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t32 := term 32 5 0.013139006489 0.013138881266 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t33 := term 33 5 0.012643216511 0.012643094959 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t34 := term 34 5 0.012180114017 0.012179995962 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t35 := term 35 5 0.011746674769 0.011746560047 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t36 := term 36 5 0.011340230291 0.011340118746 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t37 := term 37 5 0.010958417564 0.010958309051 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t38 := term 38 5 0.010599136965 0.010599031346 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t39 := term 39 5 0.010260516929 0.010260414075 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t40 := term 40 5 0.00994088411 0.0099407839 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t41 := term 41 5 0.009638738082 0.0096386404 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t42 := term 42 5 0.009352729784 0.009352634523 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t43 := term 43 5 0.0090816431 0.009081550158 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t44 := term 44 5 0.00882437904 0.00882428832 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t45 := term 45 5 0.008579942114 0.008579853526 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t46 := term 46 5 0.008347428551 0.008347342009 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t47 := term 47 5 0.008126016084 0.008125931506 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t48 := term 48 5 0.007914955059 0.007914872369 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t49 := term 49 5 0.007713560674 0.0077134798 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  linarith

lemma tail_le : (((50 : ℕ) : ℝ) - 1 / 2) ^ (1 - sigS) / (sigS - 1) ≤ 1.507993095275 := by
  have hx : (1 : ℝ) ≤ ((50 : ℕ) : ℝ) - 1 / 2 := by norm_num
  have h := rpow_neg_add_le (x := ((50 : ℕ) : ℝ) - 1 / 2) (a := 1 / 4) (ε := 1375007 / 500002500000)
    (q₁ := 0.377006380455) (q := 0.3770024208) 1 4 5 (by norm_num) (by norm_num) hx (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [sigS_eq, show (1 : ℝ) - (5 / 4 + 1375007 / 500002500000) = -(1 / 4 + 1375007 / 500002500000) by norm_num]
  rw [show (5 / 4 + (1375007 / 500002500000 : ℝ)) - 1 = 1 / 4 + 1375007 / 500002500000 by norm_num]
  calc _ ≤ (0.3770024208 : ℝ) / (1 / 4 + 1375007 / 500002500000) := by gcongr
    _ ≤ _ := by norm_num

/-- `ζ(σ♯) ≤ 4.595076613723`. -/
theorem zeta_sigS_le : (riemannZeta (sigS : ℂ)).re ≤ 4.595076613723 := by
  have h := zeta_le_partial_add_tail one_lt_sigS 50 (by norm_num)
  linarith [partial_sum_le, tail_le]

lemma log_Zd_le : Real.log (4.595076613723 : ℝ) ≤ 1.52499 := by
  have h := log_one_sub_le (x := 1 - 4.595076613723 / 8) (by norm_num) (by norm_num) 36
  have e : Real.log (1 - (1 - 4.595076613723 / 8)) = Real.log 4.595076613723 - 3 * Real.log 2 := by
    rw [show (1 : ℝ) - (1 - 4.595076613723 / 8) = 4.595076613723 / 2 ^ 3 by norm_num,
      log_div_two_pow (by norm_num) 3]; push_cast; ring
  rw [e] at h
  have hs : -(∑ i ∈ range 36, (1 - 4.595076613723 / 8 : ℝ) ^ (i + 1) / (i + 1))
      + (1 - 4.595076613723 / 8 : ℝ) ^ (36 + 1) / (1 - (1 - 4.595076613723 / 8)) ≤ -0.55445611273 := by
    norm_num [Finset.sum_range_succ]
  linarith [Real.log_two_lt_d9]

/-- **Numerical input of Theorem 1.3**: `log ζ(σ♯) ≤ 1.52499`. -/
theorem log_zeta_sigS_le : Real.log (riemannZeta (sigS : ℂ)).re ≤ 1.52499 := by
  have hpos : 0 < (riemannZeta (sigS : ℂ)).re := Common.ZetaSeries.zeta_re_pos one_lt_sigS
  exact le_trans (Real.log_le_log hpos zeta_sigS_le) log_Zd_le

end RvmClock.ZetaSigS
