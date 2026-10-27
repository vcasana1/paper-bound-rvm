import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Rational bounds for `sin`, `cos`, `arcsin`, `arccos` and square roots (reusable)

* `sin_ge_partial`, `sin_le_partial`: for `0 ≤ x` with `x² ≤ 6`, the partial sums of the Taylor series of
  `sin x` with an even (odd) number of terms are lower (upper) bounds — the series is alternating with
  antitone terms (`Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`).
  With `x` rational, `norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]` evaluates the sums.
* `cos_ge_partial`, `cos_le_partial`: the same for `cos x`, `x² ≤ 2`.
* `le_arcsin_of_sin_le`, `arcsin_le_of_le_sin`: `t ≤ arcsin y` from `sin t ≤ y`, and `arcsin y ≤ t` from
  `y ≤ sin t`, for `|t| ≤ 1.57`; together with the two bounds above they give rational bounds of any
  precision for `arcsin y` (hence `arccos y = π/2 - arcsin y`) with `y` rational.
* `le_sqrt_of_sq`, `sqrt_le_of_sq`: rational bounds for `√y` from `q² ≤ y ≤ q'²`.
-/

open Finset

namespace Common.TrigBounds

/-- `x^{2k+1}/(2k+1)!`. -/
noncomputable def sinTerm (x : ℝ) (k : ℕ) : ℝ := x ^ (2 * k + 1) / (2 * k + 1).factorial

/-- `x^{2k}/(2k)!`. -/
noncomputable def cosTerm (x : ℝ) (k : ℕ) : ℝ := x ^ (2 * k) / (2 * k).factorial

lemma sinTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 6) : Antitone (sinTerm x) := by
  apply antitone_nat_of_succ_le
  intro k
  unfold sinTerm
  have hf : ((2 * (k + 1) + 1).factorial : ℝ)
      = (2 * k + 1).factorial * ((2 * k + 2) * (2 * k + 3)) := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, Nat.factorial_succ,
      show 2 * k + 2 = (2 * k + 1) + 1 by ring, Nat.factorial_succ]
    push_cast; ring
  rw [hf, show x ^ (2 * (k + 1) + 1) = x ^ (2 * k + 1) * x ^ 2 by ring]
  have hP : 0 ≤ x ^ (2 * k + 1) * (2 * k + 1).factorial := by positivity
  have h3 : (6 : ℝ) ≤ (2 * k + 2) * (2 * k + 3) := by
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hF : (0 : ℝ) < (2 * k + 1).factorial := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left (hx.trans h3) hP
  nlinarith [this]

lemma cosTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 2) : Antitone (cosTerm x) := by
  apply antitone_nat_of_succ_le
  intro k
  unfold cosTerm
  have hf : ((2 * (k + 1)).factorial : ℝ) = (2 * k).factorial * ((2 * k + 1) * (2 * k + 2)) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf, show x ^ (2 * (k + 1)) = x ^ (2 * k) * x ^ 2 by ring]
  have hP : 0 ≤ x ^ (2 * k) * (2 * k).factorial := by positivity
  have h3 : (2 : ℝ) ≤ (2 * k + 1) * (2 * k + 2) := by
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left (hx.trans h3) hP
  nlinarith [this]

lemma hasSum_sin' (x : ℝ) : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * sinTerm x i) (Real.sin x) := by
  convert Real.hasSum_sin x using 1
  funext i; unfold sinTerm; ring

lemma hasSum_cos' (x : ℝ) : HasSum (fun i : ℕ => (-1 : ℝ) ^ i * cosTerm x i) (Real.cos x) := by
  convert Real.hasSum_cos x using 1
  funext i; unfold cosTerm; ring

/-- Even partial sums are lower bounds for `sin x` (`0 ≤ x`, `x² ≤ 6`). -/
theorem sin_ge_partial {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 6) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * sinTerm x i ≤ Real.sin x :=
  (sinTerm_antitone hx0 hx).alternating_series_le_tendsto (hasSum_sin' x).tendsto_sum_nat k

/-- Odd partial sums are upper bounds for `sin x` (`0 ≤ x`, `x² ≤ 6`). -/
theorem sin_le_partial {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 6) (k : ℕ) :
    Real.sin x ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * sinTerm x i :=
  (sinTerm_antitone hx0 hx).tendsto_le_alternating_series (hasSum_sin' x).tendsto_sum_nat k

/-- Even partial sums are lower bounds for `cos x` (`0 ≤ x`, `x² ≤ 2`). -/
theorem cos_ge_partial {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 2) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * cosTerm x i ≤ Real.cos x :=
  (cosTerm_antitone hx0 hx).alternating_series_le_tendsto (hasSum_cos' x).tendsto_sum_nat k

/-- Odd partial sums are upper bounds for `cos x` (`0 ≤ x`, `x² ≤ 2`). -/
theorem cos_le_partial {x : ℝ} (hx0 : 0 ≤ x) (hx : x ^ 2 ≤ 2) (k : ℕ) :
    Real.cos x ≤ ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * cosTerm x i :=
  (cosTerm_antitone hx0 hx).tendsto_le_alternating_series (hasSum_cos' x).tendsto_sum_nat k

/-! ### `arcsin` from `sin` -/

lemma abs_le_pi_div_two {t : ℝ} (ht : |t| ≤ 1.57) : -(Real.pi / 2) < t ∧ t < Real.pi / 2 := by
  have := Real.pi_gt_d2
  rw [abs_le] at ht
  constructor <;> linarith

/-- `t ≤ arcsin y` as soon as `sin t ≤ y` (`|t| ≤ 1.57`). -/
theorem le_arcsin_of_sin_le {y t : ℝ} (ht : |t| ≤ 1.57) (h : Real.sin t ≤ y) : t ≤ Real.arcsin y := by
  have hp := abs_le_pi_div_two ht
  exact (Real.le_arcsin_iff_sin_le' ⟨hp.1, hp.2.le⟩).2 h

/-- `arcsin y ≤ t` as soon as `y ≤ sin t` (`|t| ≤ 1.57`). -/
theorem arcsin_le_of_le_sin {y t : ℝ} (ht : |t| ≤ 1.57) (h : y ≤ Real.sin t) : Real.arcsin y ≤ t := by
  have hp := abs_le_pi_div_two ht
  exact (Real.arcsin_le_iff_le_sin' ⟨hp.1.le, hp.2⟩).2 h

/-! ### Square roots -/

theorem le_sqrt_of_sq {q y : ℝ} (h : q ^ 2 ≤ y) : q ≤ Real.sqrt y := Real.le_sqrt_of_sq_le h

theorem sqrt_le_of_sq {q y : ℝ} (hq : 0 ≤ q) (h : y ≤ q ^ 2) : Real.sqrt y ≤ q :=
  (Real.sqrt_le_left hq).2 h

end Common.TrigBounds
