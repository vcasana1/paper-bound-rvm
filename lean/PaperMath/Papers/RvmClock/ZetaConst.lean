import PaperMath.Common.ZetaSeries
import PaperMath.Common.LogBounds

/-!
# The numerical input `log (ζ(c) / ζ(2c)) ≤ 12.62467` of Theorem 1.3

Here `c = 1.000002`. Proof, all for Mathlib's `riemannZeta`:
* `ζ(1+s) ≤ 1 + 1/s` and `ζ(2+ε) ≥ π²/6 - ε K` (`Common.ZetaSeries`);
* rational bounds for `log 2` (Mathlib), `log 5` and `log 1.64493` (Taylor series with remainder,
  `Common.LogBounds`).
Margin: `12.62467 - 12.6246675573 = 2.44 · 10⁻⁶`.
-/

open Finset Common.ZetaSeries Common.LogBounds

namespace RvmClock.ZetaConst

theorem zeta_c_le : (riemannZeta ((1.000002 : ℝ) : ℂ)).re ≤ 500001 := by
  have h := zeta_one_add_le 0.000002 (by norm_num)
  rw [show (1 + 0.000002 : ℝ) = 1.000002 by norm_num] at h
  linarith [show (1 : ℝ) + 1 / 0.000002 = 500001 by norm_num]

theorem zeta_2c_ge : (1.64493 : ℝ) ≤ (riemannZeta ((2.000004 : ℝ) : ℂ)).re := by
  have h := zeta_two_add_ge 0.000004 (by norm_num)
  rw [show (2 + 0.000004 : ℝ) = 2.000004 by norm_num] at h
  have hK := K_le
  have hpi := Real.pi_gt_d20
  have hpi2 : (3.14159265358979323846 : ℝ) ^ 2 < Real.pi ^ 2 := by gcongr
  nlinarith

theorem zeta_c_pos : 0 < (riemannZeta ((1.000002 : ℝ) : ℂ)).re := by
  rw [zeta_re_eq_tsum (by norm_num)]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1.000002 : ℝ)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  have := hf.le_tsum 1 (fun j _ => by positivity)
  simp only [Nat.cast_one, Real.one_rpow, div_one] at this
  linarith

lemma log_five_le : Real.log 5 ≤ 2 * Real.log 2
    + ((∑ i ∈ range 12, (1 / 5 : ℝ) ^ (i + 1) / (i + 1)) + (1 / 5 : ℝ) ^ (12 + 1) / (1 - 1 / 5)) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 5 : ℝ)| < 1 by norm_num) 12
  rw [abs_of_pos (show (0 : ℝ) < 1 / 5 by norm_num)] at h
  have h1 := (abs_le.1 h).1
  have h5 : Real.log (1 - 1 / 5) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 : ℝ) - 1 / 5 = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  rw [h5] at h1
  linarith

lemma log_q_ge : Real.log 2
    - ((∑ i ∈ range 14, (1 - 1.64493 / 2 : ℝ) ^ (i + 1) / (i + 1))
      + (1 - 1.64493 / 2 : ℝ) ^ (14 + 1) / (1 - (1 - 1.64493 / 2))) ≤ Real.log 1.64493 := by
  have hx : |(1 - 1.64493 / 2 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 14
  rw [abs_of_pos (show (0 : ℝ) < 1 - 1.64493 / 2 by norm_num)] at h
  have h1 := (abs_le.1 h).1
  have hq : Real.log (1 - (1 - 1.64493 / 2)) = Real.log 1.64493 - Real.log 2 := by
    rw [show (1 : ℝ) - (1 - 1.64493 / 2) = 1.64493 / 2 by ring,
      Real.log_div (by norm_num) (by norm_num)]
  rw [hq] at h1
  linarith

lemma log_500001_le : Real.log 500001 ≤ 5 * Real.log 2 + 6 * Real.log 5 + 1 / 500000 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500001 / 500000 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at h1
  have h2 : Real.log 500000 = 5 * Real.log 2 + 6 * Real.log 5 := by
    rw [show (500000 : ℝ) = 2 ^ 5 * 5 ^ 6 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]; norm_num
  linarith

/-- **Numerical input of Theorem 1.3**: `log (ζ(c)/ζ(2c)) ≤ 12.62467` for `c = 1.000002`. -/
theorem log_zeta_ratio_le :
    Real.log ((riemannZeta ((1.000002 : ℝ) : ℂ)).re / (riemannZeta ((2.000004 : ℝ) : ℂ)).re)
      ≤ 12.62467 := by
  have hc := zeta_c_le
  have hc0 := zeta_c_pos
  have h2c := zeta_2c_ge
  have h2c0 : (0 : ℝ) < (riemannZeta ((2.000004 : ℝ) : ℂ)).re := by linarith
  have hratio : (riemannZeta ((1.000002 : ℝ) : ℂ)).re / (riemannZeta ((2.000004 : ℝ) : ℂ)).re
      ≤ 500001 / 1.64493 := by
    calc _ ≤ 500001 / (riemannZeta ((2.000004 : ℝ) : ℂ)).re := by gcongr
      _ ≤ 500001 / 1.64493 := by gcongr
  have hlog := Real.log_le_log (div_pos hc0 h2c0) hratio
  rw [Real.log_div (show (500001 : ℝ) ≠ 0 by norm_num) (show (1.64493 : ℝ) ≠ 0 by norm_num)] at hlog
  have a := log_500001_le
  have b := log_five_le
  have c := log_q_ge
  have sb : (∑ i ∈ range 12, (1 / 5 : ℝ) ^ (i + 1) / (i + 1)) + (1 / 5 : ℝ) ^ (12 + 1) / (1 - 1 / 5)
      ≤ 0.223143552261 := by norm_num [Finset.sum_range_succ]
  have sc : (∑ i ∈ range 14, (1 - 1.64493 / 2 : ℝ) ^ (i + 1) / (i + 1))
      + (1 - 1.64493 / 2 : ℝ) ^ (14 + 1) / (1 - (1 - 1.64493 / 2)) ≤ 0.195449350446 := by
    norm_num [Finset.sum_range_succ]
  linarith [Real.log_two_lt_d9, Real.log_two_gt_d9]

end RvmClock.ZetaConst
