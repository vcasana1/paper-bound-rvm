import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Elementary bounds for `ζ(s)` on the real axis (reusable)

All statements are about Mathlib's `riemannZeta` restricted to real `s > 1`, where it is the real series
`∑ 1/n^s` (`zeta_re_eq_tsum`).

* `zeta_one_add_le`: `ζ(1+s) ≤ 1 + 1/s` for `s > 0`, by the telescoping bound
  `n^{-1-s} ≤ ((n-1)^{-s} - n^{-s})/s`;
* `zeta_two_add_ge`: `ζ(2+ε) ≥ π²/6 - ε K` for `ε ≥ 0`, with `K = log 2/4 + log 3/9 + (log 3 + 1)/3 ≥ ∑ log n/n²`
  (`n^{-ε} ≥ 1 - ε log n`, telescoping with `(log x + 1)/x` for `x ≥ 4`), and `K ≤ 1.0116398448`;
* `one_le_zeta_re`, `zeta_re_pos`: `1 ≤ ζ(s)` for real `s > 1`.

Originally part of `RvmClock.ZetaConst` (article "The Riemann–von Mangoldt clock", Theorem 1.3); moved here
unchanged so that other papers can use it.
-/

open Finset

namespace Common.ZetaSeries

/-- For real `s > 1`, `ζ(s)` is the real series `∑ 1/n^s`. -/
lemma zeta_re_eq_tsum {s : ℝ} (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)]
  have : (fun n : ℕ => 1 / (n : ℂ) ^ (s : ℂ)) = fun n : ℕ => ((1 / (n : ℝ) ^ s : ℝ) : ℂ) := by
    funext n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
  rw [this, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-! ### Upper bound `ζ(1+s) ≤ 1 + 1/s` -/

lemma tele (s x : ℝ) (hs : 0 < s) (hx : 1 < x) :
    1 / x ^ (1 + s) ≤ ((x - 1) ^ (-s) - x ^ (-s)) / s := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hL : 1 / x ≤ Real.log x - Real.log (x - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by positivity)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    have e : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
    linarith
  have hA : (x - 1) ^ (-s) = Real.exp (Real.log x * (-s)) *
      Real.exp (s * (Real.log x - Real.log (x - 1))) := by
    rw [Real.rpow_def_of_pos hx1, ← Real.exp_add]; congr 1; ring
  have hB : x ^ (-s) = Real.exp (Real.log x * (-s)) := Real.rpow_def_of_pos hx0 _
  have hC : 1 / x ^ (1 + s) = Real.exp (Real.log x * (-s)) / x := by
    rw [Real.rpow_def_of_pos hx0,
      show Real.log x * (1 + s) = Real.log x - Real.log x * (-s) by ring, Real.exp_sub,
      Real.exp_log hx0]
    field_simp
  rw [hA, hB, hC]
  set E := Real.exp (Real.log x * (-s))
  set D := Real.log x - Real.log (x - 1)
  have hE0 : 0 < E := Real.exp_pos _
  have h1 : 1 + s * D ≤ Real.exp (s * D) := by linarith [Real.add_one_le_exp (s * D)]
  have h2 : s * (1 / x) ≤ s * D := mul_le_mul_of_nonneg_left hL hs.le
  have h3 : E * (s * (1 / x)) ≤ E * (Real.exp (s * D) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hE0.le
  rw [div_le_div_iff₀ hx0 hs]
  calc E * s = E * (s * (1 / x)) * x := by field_simp
    _ ≤ E * (Real.exp (s * D) - 1) * x := mul_le_mul_of_nonneg_right h3 hx0.le
    _ = (E * Real.exp (s * D) - E) * x := by ring

lemma sum_le_aux (s : ℝ) (hs : 0 < s) (M : ℕ) :
    ∑ n ∈ range (M + 2), 1 / (n : ℝ) ^ (1 + s) ≤ 1 + (1 - ((M : ℝ) + 1) ^ (-s)) / s := by
  induction M with
  | zero =>
    norm_num [Finset.sum_range_succ, Real.zero_rpow (show (1 + s) ≠ 0 by linarith)]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ht := tele s ((k : ℝ) + 2) hs (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    rw [show (k : ℝ) + 2 - 1 = (k : ℝ) + 1 by ring] at ht
    push_cast
    rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
    calc _ ≤ 1 + (1 - ((k : ℝ) + 1) ^ (-s)) / s
          + (((k : ℝ) + 1) ^ (-s) - ((k : ℝ) + 2) ^ (-s)) / s := add_le_add ih ht
      _ = 1 + (1 - ((k : ℝ) + 2) ^ (-s)) / s := by ring

lemma sum_le (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ range N, 1 / (n : ℝ) ^ (1 + s) ≤ 1 + 1 / s := by
  have hsub : ∑ n ∈ range N, 1 / (n : ℝ) ^ (1 + s) ≤ ∑ n ∈ range (N + 2), 1 / (n : ℝ) ^ (1 + s) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun _ _ _ => by positivity)
  have hk := sum_le_aux s hs N
  have hp : 0 ≤ ((N : ℝ) + 1) ^ (-s) := by positivity
  have : (1 - ((N : ℝ) + 1) ^ (-s)) / s ≤ 1 / s := by gcongr; linarith
  linarith

theorem zeta_one_add_le (s : ℝ) (hs : 0 < s) :
    (riemannZeta ((1 + s : ℝ) : ℂ)).re ≤ 1 + 1 / s := by
  rw [zeta_re_eq_tsum (by linarith)]
  exact Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_le s hs)

/-! ### Lower bound for `ζ(2+ε)` -/

lemma term_ge (ε : ℝ) (n : ℕ) :
    1 / (n : ℝ) ^ 2 - ε * (Real.log n / (n : ℝ) ^ 2) ≤ 1 / (n : ℝ) ^ (2 + ε) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_add hx, Real.rpow_two, Real.rpow_def_of_pos hx]
  have h := Real.add_one_le_exp (-(Real.log n * ε))
  rw [Real.exp_neg] at h
  have hp : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  calc 1 / (n : ℝ) ^ 2 - ε * (Real.log n / (n : ℝ) ^ 2)
        = (-(Real.log n * ε) + 1) / (n : ℝ) ^ 2 := by field_simp; ring
    _ ≤ (Real.exp (Real.log n * ε))⁻¹ / (n : ℝ) ^ 2 := by gcongr
    _ = 1 / ((n : ℝ) ^ 2 * Real.exp (Real.log n * ε)) := by field_simp

lemma tele_log (x : ℝ) (hx : 4 ≤ x) :
    Real.log x / x ^ 2 ≤ (Real.log (x - 1) + 1) / (x - 1) - (Real.log x + 1) / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hL1 : Real.log x - 1 / (x - 1) ≤ Real.log (x - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < x / (x - 1) by positivity)
    rw [Real.log_div hx0.ne' hx1.ne'] at h
    have e : x / (x - 1) - 1 = 1 / (x - 1) := by field_simp; ring
    linarith
  have hL4 : 4 / 3 ≤ Real.log x := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hx
    linarith [Real.log_two_gt_d9]
  set L := Real.log x
  have hmono : (L - 1 / (x - 1) + 1) / (x - 1) ≤ (Real.log (x - 1) + 1) / (x - 1) := by
    gcongr
  have key : (L - 1 / (x - 1) + 1) / (x - 1) - (L + 1) / x - L / x ^ 2
      = (L * (x - 1) - x) / (x ^ 2 * (x - 1) ^ 2) := by
    field_simp; ring
  have hnum : 0 ≤ L * (x - 1) - x := by nlinarith
  have : 0 ≤ (L * (x - 1) - x) / (x ^ 2 * (x - 1) ^ 2) := by positivity
  linarith

/-- `K = log 2/4 + log 3/9 + (log 3 + 1)/3` bounds `∑ log n / n²`. -/
noncomputable def K : ℝ := Real.log 2 / 4 + Real.log 3 / 9 + (Real.log 3 + 1) / 3

lemma hlog_nonneg (n : ℕ) : 0 ≤ Real.log n / (n : ℝ) ^ 2 :=
  div_nonneg (Real.log_natCast_nonneg n) (sq_nonneg _)

lemma hsum_aux (M : ℕ) :
    ∑ n ∈ range (M + 4), Real.log n / (n : ℝ) ^ 2
      ≤ K - (Real.log ((M : ℝ) + 3) + 1) / ((M : ℝ) + 3) := by
  induction M with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, K]
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ht := tele_log ((k : ℝ) + 4) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    rw [show (k : ℝ) + 4 - 1 = (k : ℝ) + 3 by ring] at ht
    have e : ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 := by push_cast; ring
    rw [e]
    have e2 : ((k + 1 : ℕ) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
    rw [e2]
    linarith

lemma hsum_le (N : ℕ) : ∑ n ∈ range N, Real.log n / (n : ℝ) ^ 2 ≤ K := by
  have hsub : ∑ n ∈ range N, Real.log n / (n : ℝ) ^ 2 ≤ ∑ n ∈ range (N + 4), Real.log n / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun n _ _ => hlog_nonneg n)
  have hk := hsum_aux N
  have hp : 0 ≤ (Real.log ((N : ℝ) + 3) + 1) / ((N : ℝ) + 3) := by
    have : 0 ≤ Real.log ((N : ℝ) + 3) := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    positivity
  linarith

theorem zeta_two_add_ge (ε : ℝ) (hε : 0 ≤ ε) :
    Real.pi ^ 2 / 6 - ε * K ≤ (riemannZeta ((2 + ε : ℝ) : ℂ)).re := by
  rw [zeta_re_eq_tsum (by linarith)]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 + ε)) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hg := hasSum_zeta_two.summable
  have hh : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) :=
    summable_of_sum_range_le hlog_nonneg hsum_le
  have hhK : ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 ≤ K := Real.tsum_le_of_sum_range_le hlog_nonneg hsum_le
  have hsplit : ∑' n : ℕ, (1 / (n : ℝ) ^ 2 - ε * (Real.log n / (n : ℝ) ^ 2))
      = Real.pi ^ 2 / 6 - ε * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
    rw [hg.tsum_sub (hh.mul_left ε), tsum_mul_left, hasSum_zeta_two.tsum_eq]
  calc Real.pi ^ 2 / 6 - ε * K ≤ Real.pi ^ 2 / 6 - ε * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
        gcongr
    _ = ∑' n : ℕ, (1 / (n : ℝ) ^ 2 - ε * (Real.log n / (n : ℝ) ^ 2)) := hsplit.symm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 + ε) :=
        Summable.tsum_le_tsum (term_ge ε) (hg.sub (hh.mul_left ε)) hf

/-! ### Numerical values -/

lemma K_le : K ≤ 1.0116398448 := by
  have h3 : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow] at h
    norm_num at h
    linarith
  unfold K
  linarith [Real.log_two_lt_d9]

/-- `1 ≤ ζ(s)` for real `s > 1` (the term `n = 1` of the series). -/
theorem one_le_zeta_re {s : ℝ} (hs : 1 < s) : 1 ≤ (riemannZeta (s : ℂ)).re := by
  rw [zeta_re_eq_tsum hs]
  have hf : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) := Real.summable_one_div_nat_rpow.2 hs
  have := hf.le_tsum 1 (fun j _ => by positivity)
  simpa using this

theorem zeta_re_pos {s : ℝ} (hs : 1 < s) : 0 < (riemannZeta (s : ℂ)).re :=
  lt_of_lt_of_le one_pos (one_le_zeta_re hs)

/-- `‖ζ(s)‖ ≤ ζ(Re s)` for `Re s > 1` (termwise, from the Dirichlet series). -/
theorem norm_zeta_le_zeta_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta (s.re : ℂ)).re := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs, zeta_re_eq_tsum hs]
  have hre : s.re ≠ 0 := by linarith
  have hnorm : ∀ n : ℕ, ‖1 / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := by
    intro n
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_re_ne_zero n hre]
  have hsum : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ s‖) := by
    simp_rw [hnorm]; exact Real.summable_one_div_nat_rpow.2 hs
  calc ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by simp_rw [hnorm]

end Common.ZetaSeries
