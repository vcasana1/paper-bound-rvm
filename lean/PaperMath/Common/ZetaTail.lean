import PaperMath.Common.ZetaSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Tails of `∑ n^{-σ}` by the midpoint rule, and rational bounds for `x^{-a}` (reusable)

* `midpoint_rpow`: for `σ > 1` and `x > 1/2`, `x^{-σ} ≤ ∫_{x-1/2}^{x+1/2} t^{-σ} dt
  = ((x-1/2)^{1-σ} - (x+1/2)^{1-σ})/(σ-1)`. The pointwise inequality `2 x^{-σ} ≤ (x-h)^{-σ} + (x+h)^{-σ}`
  is AM–GM: `(x-h)^{-σ}(x+h)^{-σ} = (x²-h²)^{-σ} ≥ (x²)^{-σ}`.
* `zeta_le_partial_add_tail`: `ζ(σ) ≤ ∑_{n<N} n^{-σ} + (N-1/2)^{1-σ}/(σ-1)` for real `σ > 1`, `N ≥ 1`.
  The error of the midpoint rule is `≈ σ N^{-σ-1}/24`, so this gives `ζ(σ)` to about `N^{-σ-1}` with `N` terms.
* `rpow_neg_le_of_pow`: `x^{-p/r} ≤ q` as soon as `1 ≤ q^r x^p` (checked by `norm_num` for rational data).
* `log_ge_of_two_pow_le`: `k log 2 + 1 - 2^k/x ≤ log x` when `2^k ≤ x`.
* `rpow_neg_small_le`: `x^{-ε} ≤ 1/(1 + ε L)` when `L ≤ log x`, `ε ≥ 0`.
* `rpow_neg_add_le`: the three combined, `x^{-(p/r + ε)} ≤ q` from rational data only.
-/

open Finset

namespace Common.ZetaTail

/-! ### The midpoint inequality -/

/-- AM–GM step: `2 x^{-σ} ≤ (x-h)^{-σ} + (x+h)^{-σ}` for `0 ≤ h < x`, `σ ≥ 0`. -/
lemma two_rpow_le {σ x h : ℝ} (hσ : 0 ≤ σ) (hh : 0 ≤ h) (hx : h < x) :
    2 * x ^ (-σ) ≤ (x - h) ^ (-σ) + (x + h) ^ (-σ) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < (x - h) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
  have hb : 0 < (x + h) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
  have hc : 0 < x ^ (-σ) := Real.rpow_pos_of_pos hx0 _
  have hab : x ^ (-σ) * x ^ (-σ) ≤ (x - h) ^ (-σ) * (x + h) ^ (-σ) := by
    rw [← Real.mul_rpow hx0.le hx0.le,
      ← Real.mul_rpow (show (0 : ℝ) ≤ x - h by linarith) (show (0 : ℝ) ≤ x + h by linarith)]
    apply Real.rpow_le_rpow_of_nonpos (mul_pos (by linarith) (by linarith)) (by nlinarith [sq_nonneg h])
      (by linarith)
  set a := (x - h) ^ (-σ)
  set b := (x + h) ^ (-σ)
  set c := x ^ (-σ)
  have h4 : (2 * c) ^ 2 ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h4

lemma continuousOn_shift {σ x : ℝ} (hx : 1 / 2 < x) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ContinuousOn (fun h : ℝ => (x + s * h) ^ (-σ)) (Set.Icc 0 (1 / 2)) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro h hh
  left
  rcases hs with rfl | rfl <;> · have := hh.1; have := hh.2; exact ne_of_gt (by linarith)

/-- `x^{-σ} ≤ ∫_{x-1/2}^{x+1/2} t^{-σ} dt` for `σ ≥ 0`, `x > 1/2`. -/
lemma rpow_le_integral {σ x : ℝ} (hσ : 0 ≤ σ) (hx : 1 / 2 < x) :
    x ^ (-σ) ≤ ∫ t in (x - 1 / 2)..(x + 1 / 2), t ^ (-σ) := by
  have hI1 : IntervalIntegrable (fun h : ℝ => (x + (-1) * h) ^ (-σ)) MeasureTheory.volume 0 (1 / 2) :=
    (continuousOn_shift hx (-1) (Or.inr rfl)).intervalIntegrable_of_Icc (by norm_num)
  have hI2 : IntervalIntegrable (fun h : ℝ => (x + 1 * h) ^ (-σ)) MeasureTheory.volume 0 (1 / 2) :=
    (continuousOn_shift hx 1 (Or.inl rfl)).intervalIntegrable_of_Icc (by norm_num)
  have e1 : ∫ h in (0 : ℝ)..(1 / 2), (x + (-1) * h) ^ (-σ) = ∫ t in (x - 1 / 2)..x, t ^ (-σ) := by
    have := intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ (-σ)) (a := 0) (b := 1 / 2) x
    simp only [sub_zero] at this
    rw [← this]
    congr 1; funext h; congr 1; ring
  have e2 : ∫ h in (0 : ℝ)..(1 / 2), (x + 1 * h) ^ (-σ) = ∫ t in x..(x + 1 / 2), t ^ (-σ) := by
    have := intervalIntegral.integral_comp_add_left (fun t : ℝ => t ^ (-σ)) (a := 0) (b := 1 / 2) x
    simp only [add_zero] at this
    rw [← this]
    congr 1; funext h; congr 1; ring
  have hsplit : ∫ t in (x - 1 / 2)..(x + 1 / 2), t ^ (-σ)
      = (∫ t in (x - 1 / 2)..x, t ^ (-σ)) + ∫ t in x..(x + 1 / 2), t ^ (-σ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
      rw [Set.uIcc_of_le (by linarith)]
      intro h0; linarith [h0.1]
    · apply intervalIntegral.intervalIntegrable_rpow (Or.inr _)
      rw [Set.uIcc_of_le (by linarith)]
      intro h0; linarith [h0.1]
  rw [hsplit, ← e1, ← e2, ← intervalIntegral.integral_add hI1 hI2]
  have hc : x ^ (-σ) = ∫ _ in (0 : ℝ)..(1 / 2), 2 * x ^ (-σ) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hc]
  apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const (hI1.add hI2)
  intro h hh
  have := two_rpow_le hσ hh.1 (show h < x by linarith [hh.2])
  simp only [neg_mul, one_mul]
  rw [show x + -h = x - h by ring]
  exact this

/-- The midpoint inequality in closed form: for `σ > 1`, `x > 1/2`,
`x^{-σ} ≤ ((x-1/2)^{1-σ} - (x+1/2)^{1-σ})/(σ-1)`. -/
theorem midpoint_rpow {σ x : ℝ} (hσ : 1 < σ) (hx : 1 / 2 < x) :
    x ^ (-σ) ≤ ((x - 1 / 2) ^ (1 - σ) - (x + 1 / 2) ^ (1 - σ)) / (σ - 1) := by
  have h := rpow_le_integral (show (0 : ℝ) ≤ σ by linarith) hx
  have hint : ∫ t in (x - 1 / 2)..(x + 1 / 2), t ^ (-σ)
      = ((x + 1 / 2) ^ (-σ + 1) - (x - 1 / 2) ^ (-σ + 1)) / (-σ + 1) := by
    apply integral_rpow
    right
    refine ⟨fun h => by linarith, ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    intro h0
    linarith [h0.1]
  rw [hint] at h
  have e : ((x + 1 / 2) ^ (-σ + 1) - (x - 1 / 2) ^ (-σ + 1)) / (-σ + 1)
      = ((x - 1 / 2) ^ (1 - σ) - (x + 1 / 2) ^ (1 - σ)) / (σ - 1) := by
    rw [show -σ + 1 = 1 - σ by ring]
    have : σ - 1 ≠ 0 := by linarith
    have : 1 - σ ≠ 0 := by linarith
    field_simp
    ring
  rw [e] at h
  exact h

/-! ### Tail of the zeta series -/

/-- `T σ N = (N - 1/2)^{1-σ}/(σ-1)`, the midpoint-rule bound for `∑_{n ≥ N} n^{-σ}`. -/
noncomputable def T (σ : ℝ) (N : ℕ) : ℝ := ((N : ℝ) - 1 / 2) ^ (1 - σ) / (σ - 1)

lemma T_nonneg {σ : ℝ} (hσ : 1 < σ) (N : ℕ) (hN : 1 ≤ N) : 0 ≤ T σ N := by
  unfold T
  apply div_nonneg _ (by linarith)
  apply Real.rpow_nonneg
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

lemma term_le_T_sub {σ : ℝ} (hσ : 1 < σ) (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) ^ σ ≤ T σ n - T σ (n + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := midpoint_rpow hσ (show 1 / 2 < (n : ℝ) by linarith)
  rw [Real.rpow_neg (show (0 : ℝ) ≤ n by linarith)] at h
  unfold T
  push_cast
  rw [show (n : ℝ) + 1 - 1 / 2 = n + 1 / 2 by ring, ← sub_div, one_div]
  exact h

lemma partial_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) (hN : 1 ≤ N) :
    ∀ M, N ≤ M → ∑ n ∈ range M, 1 / (n : ℝ) ^ σ
      ≤ ∑ n ∈ range N, 1 / (n : ℝ) ^ σ + T σ N - T σ M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_range_succ]
    have := term_le_T_sub hσ M (by omega)
    linarith

/-- **Partial sum plus midpoint tail**: for real `σ > 1` and `N ≥ 1`,
`ζ(σ) ≤ ∑_{n<N} n^{-σ} + (N - 1/2)^{1-σ}/(σ-1)`. -/
theorem zeta_le_partial_add_tail {σ : ℝ} (hσ : 1 < σ) (N : ℕ) (hN : 1 ≤ N) :
    (riemannZeta (σ : ℂ)).re
      ≤ ∑ n ∈ range N, 1 / (n : ℝ) ^ σ + ((N : ℝ) - 1 / 2) ^ (1 - σ) / (σ - 1) := by
  rw [Common.ZetaSeries.zeta_re_eq_tsum hσ]
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro M
  rcases le_or_gt N M with hM | hM
  · have := partial_le hσ N hN M hM
    have := T_nonneg hσ M (le_trans hN hM)
    unfold T at *
    linarith
  · have hsub : ∑ n ∈ range M, 1 / (n : ℝ) ^ σ ≤ ∑ n ∈ range N, 1 / (n : ℝ) ^ σ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hM.le)
        (fun _ _ _ => by positivity)
    have := T_nonneg hσ N hN
    unfold T at this
    linarith

/-! ### Rational bounds for real powers -/

/-- `x^{-(p/r)} ≤ q` as soon as `1 ≤ q^r x^p` (with `x, q > 0`, `r ≥ 1`). -/
theorem rpow_neg_le_of_pow {x q : ℝ} (hx : 0 < x) (hq : 0 < q) (p r : ℕ) (hr : 0 < r)
    (h : 1 ≤ q ^ r * x ^ p) : x ^ (-((p : ℝ) / r)) ≤ q := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : (x ^ (-((p : ℝ) / r))) ^ r = (x ^ p)⁻¹ := by
    rw [← Real.rpow_natCast (x ^ (-((p : ℝ) / r))) r, ← Real.rpow_mul hx.le,
      show -((p : ℝ) / r) * r = -(p : ℝ) by field_simp, Real.rpow_neg hx.le, Real.rpow_natCast]
  have h2 : (x ^ p)⁻¹ ≤ q ^ r := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    linarith [mul_comm (q ^ r) (x ^ p)]
  rw [← h1] at h2
  exact (pow_le_pow_iff_left₀ (by positivity) hq.le hr.ne').1 h2

/-- `k log 2 + 1 - 2^k/x ≤ log x` for `2^k ≤ x`. -/
theorem log_ge_of_two_pow_le {x : ℝ} (k : ℕ) (hk : (2 : ℝ) ^ k ≤ x) :
    k * Real.log 2 + (1 - 2 ^ k / x) ≤ Real.log x := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hx : 0 < x := lt_of_lt_of_le h2 hk
  have e : Real.log x = k * Real.log 2 + Real.log (x / 2 ^ k) := by
    rw [Real.log_div hx.ne' h2.ne', Real.log_pow]; ring
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < x / 2 ^ k by positivity)
  rw [inv_div] at h
  linarith

/-- `x^{-ε} ≤ 1/(1 + ε L)` when `L ≤ log x`, `ε ≥ 0` and `0 < 1 + ε L`. -/
theorem rpow_neg_small_le {x ε L : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) (hL : L ≤ Real.log x)
    (hpos : 0 < 1 + ε * L) : x ^ (-ε) ≤ 1 / (1 + ε * L) := by
  rw [Real.rpow_def_of_pos hx, show Real.log x * (-ε) = -(ε * Real.log x) by ring, Real.exp_neg]
  have h1 : 1 + ε * Real.log x ≤ Real.exp (ε * Real.log x) := by
    linarith [Real.add_one_le_exp (ε * Real.log x)]
  have h2 : 1 + ε * L ≤ 1 + ε * Real.log x := by nlinarith
  rw [one_div]
  exact inv_anti₀ hpos (by linarith)

/-- **Workhorse**: a rational upper bound for `x^{-(a + ε)}`, `a = p/r`, from rational data only.
With `L = k · 0.6931471803 + (1 - 2^k/x) ≤ log x` (`Real.log_two_gt_d9`):
`x^{-(a+ε)} = x^{-a} x^{-ε} ≤ q₁ / (1 + ε L) ≤ q`. -/
theorem rpow_neg_add_le {x a ε q₁ q : ℝ} (p r k : ℕ) (ha : a = (p : ℝ) / r) (hr : 0 < r)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hk : (2 : ℝ) ^ k ≤ x) (hq₁ : 0 < q₁) (h₁ : 1 ≤ q₁ ^ r * x ^ p)
    (hq : q₁ ≤ q * (1 + ε * (k * 0.6931471803 + (1 - 2 ^ k / x)))) :
    x ^ (-(a + ε)) ≤ q := by
  have hx0 : 0 < x := by linarith
  set L : ℝ := k * 0.6931471803 + (1 - 2 ^ k / x) with hLdef
  have hL : L ≤ Real.log x := by
    have := log_ge_of_two_pow_le k hk
    have h2 := Real.log_two_gt_d9
    have : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k)
    linarith
  have hL0 : 0 ≤ L := by
    have : 2 ^ k / x ≤ 1 := by rw [div_le_one hx0]; exact hk
    have : (0 : ℝ) ≤ k * 0.6931471803 := by positivity
    linarith
  have hpos : 0 < 1 + ε * L := by positivity
  have hA : x ^ (-a) ≤ q₁ := by rw [ha]; exact rpow_neg_le_of_pow hx0 hq₁ p r hr h₁
  have hB : x ^ (-ε) ≤ 1 / (1 + ε * L) := rpow_neg_small_le hx0 hε hL hpos
  have hsplit : x ^ (-(a + ε)) = x ^ (-a) * x ^ (-ε) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  rw [hsplit]
  calc x ^ (-a) * x ^ (-ε) ≤ q₁ * (1 / (1 + ε * L)) :=
        mul_le_mul hA hB (Real.rpow_nonneg hx0.le _) hq₁.le
    _ = q₁ / (1 + ε * L) := by ring
    _ ≤ q := by rw [div_le_iff₀ hpos]; exact hq

/-- `ζ(3) ≤ 1.2024` (`ζ(3) = 1.2020569…`): four terms and the midpoint tail from `4.5`. -/
theorem zeta_three_le : (riemannZeta ((3 : ℝ) : ℂ)).re ≤ 1.2024 := by
  have h := zeta_le_partial_add_tail (σ := 3) (by norm_num) 5 (by norm_num)
  have e3 : ((3 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
  have hsum : ∑ n ∈ range 5, 1 / (n : ℝ) ^ (3 : ℝ) = 1 + 1 / 8 + 1 / 27 + 1 / 64 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [e3]
    simp only [Real.rpow_natCast]
    norm_num
  have htail : (((5 : ℕ) : ℝ) - 1 / 2) ^ (1 - (3 : ℝ)) / ((3 : ℝ) - 1) = 2 / 81 := by
    rw [show (1 : ℝ) - 3 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (show (0 : ℝ) ≤ ((5 : ℕ) : ℝ) - 1 / 2 by norm_num),
      Real.rpow_natCast]
    norm_num
  rw [hsum, htail] at h
  linarith

end Common.ZetaTail
