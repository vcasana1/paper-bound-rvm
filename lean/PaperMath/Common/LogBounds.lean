import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rational bounds for the real logarithm (reusable)

Two-sided bounds for `log (1 - x)`, `0 ≤ x < 1`, from the Taylor series with remainder
(`Real.abs_log_sub_add_sum_range_le`):
`-(∑_{i<n} x^{i+1}/(i+1)) - x^{n+1}/(1-x) ≤ log (1 - x) ≤ -(∑_{i<n} x^{i+1}/(i+1)) + x^{n+1}/(1-x)`.

With `x` rational the two sides are rational numbers that `norm_num [Finset.sum_range_succ]` evaluates, so
any `log q` with `q` rational can be bounded with any precision by writing `q = 2^a · (1 - x)` and using
`Real.log_two_gt_d9` / `Real.log_two_lt_d9`.
-/

open Finset

namespace Common.LogBounds

lemma log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    Real.log (1 - x) ≤ -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.1 h).2
  linarith

lemma le_log_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.1 h).1
  linarith

/-- `log (a / 2^k) = log a - k log 2`. -/
lemma log_div_two_pow {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.log (a / 2 ^ k) = Real.log a - k * Real.log 2 := by
  rw [Real.log_div ha.ne' (by positivity), Real.log_pow]

/-- Lower bound for `log 3`: `1.0986122881 ≤ log 3`. -/
lemma log_three_gt : (1.0986122881 : ℝ) ≤ Real.log 3 := by
  -- `3 = 2^2 (1 - 1/4)`
  have h := le_log_one_sub (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num) 20
  have e : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 by norm_num, log_div_two_pow (by norm_num) 2]; push_cast; ring
  rw [e] at h
  have hs : -(∑ i ∈ range 20, (1 / 4 : ℝ) ^ (i + 1) / (i + 1)) - (1 / 4 : ℝ) ^ (20 + 1) / (1 - 1 / 4)
      ≥ -0.2876820725 := by norm_num [Finset.sum_range_succ]
  linarith [Real.log_two_gt_d9]

/-- Upper bound for `log 3`: `log 3 ≤ 1.0986122892`. -/
lemma log_three_lt : Real.log 3 ≤ (1.0986122892 : ℝ) := by
  have h := log_one_sub_le (show (0 : ℝ) ≤ 1 / 4 by norm_num) (by norm_num) 20
  have e : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 by norm_num, log_div_two_pow (by norm_num) 2]; push_cast; ring
  rw [e] at h
  have hs : -(∑ i ∈ range 20, (1 / 4 : ℝ) ^ (i + 1) / (i + 1)) + (1 / 4 : ℝ) ^ (20 + 1) / (1 - 1 / 4)
      ≤ -0.2876820724 := by norm_num [Finset.sum_range_succ]
  linarith [Real.log_two_lt_d9]

end Common.LogBounds
