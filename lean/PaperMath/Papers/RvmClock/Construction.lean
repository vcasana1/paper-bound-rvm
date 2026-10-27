import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Int.Log
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The prime-corrected clock (Section 7.1 and Proposition 7.1, article v7)

* `prime ν = p_{ν+1}` (so `prime 0 = 2`);
* `PhiM m t = -(1/π) Σ_{ν<m} arg (1 - p_{ν+1}^{-1/2-it})`  (eq. (1.10));
* `N0 t = t/(2π) log (t/(2πe)) + 7/8`;
* `budget j = ⌊2^{j/2}⌋`, `blk t = ⌊log₂ t⌋`;
* `Phi`, `F = N0 + Phi` (eq. (1.11)), `xClock k = |{t > 0 : F t < k - 1/2}|` (eq. (1.12)).
-/

open Real Set MeasureTheory

namespace RvmClock

noncomputable def prime (ν : ℕ) : ℕ := Nat.nth Nat.Prime ν

lemma two_le_prime (ν : ℕ) : 2 ≤ prime ν := (Nat.prime_nth_prime ν).two_le

noncomputable def eulerArg (n : ℕ) (t : ℝ) : ℝ :=
  Complex.arg (1 - (n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I))

noncomputable def PhiM (m : ℕ) (t : ℝ) : ℝ := -(1 / π) * ∑ ν ∈ Finset.range m, eulerArg (prime ν) t

noncomputable def N0 (t : ℝ) : ℝ := t / (2 * π) * Real.log (t / (2 * π * Real.exp 1)) + 7 / 8

noncomputable def budget (j : ℤ) : ℕ := ⌊(2 : ℝ) ^ ((j : ℝ) / 2)⌋₊

noncomputable def blk (t : ℝ) : ℤ := Int.log 2 t

/-- The interpolated phase on the block `[2^j, 2^{j+1}]`. -/
noncomputable def G (j : ℤ) (t : ℝ) : ℝ :=
  (2 - t / (2 : ℝ) ^ j) * PhiM (budget j) t + (t / (2 : ℝ) ^ j - 1) * PhiM (budget (j + 1)) t

noncomputable def Phi (t : ℝ) : ℝ := G (blk t) t

noncomputable def F (t : ℝ) : ℝ := N0 t + Phi t

noncomputable def xClock (k : ℕ) : ℝ := volume.real {t ∈ Ioi (0 : ℝ) | F t < (k : ℝ) - 1 / 2}

/-- **Casaña's method** (Section 7.1 of the article): the `k`-th ordinate is approximated by the sublevel
measure `x_k = |{t > 0 : N₀(t) + Φ(t) < k − 1/2}|` of the Riemann–von Mangoldt main term corrected by the
finite Euler phase `Φ` with about `√t` primes, equation (1.12). `casanya_method k` is `xClock k`. -/
noncomputable def casanya_method (k : ℕ) : ℝ := xClock k

@[simp] theorem casanya_method_eq (k : ℕ) : casanya_method k = xClock k := rfl

/-! ### `|arg (1 - z)| ≤ arcsin |z|` -/

lemma abs_arg_one_sub_le (z : ℂ) (hz : ‖z‖ < 1) : |Complex.arg (1 - z)| ≤ Real.arcsin ‖z‖ := by
  have hre : 0 ≤ (1 - z).re := by
    have := Complex.abs_re_le_norm z
    simp only [Complex.sub_re, Complex.one_re]
    linarith [le_abs_self z.re]
  rw [Complex.arg_of_re_nonneg hre]
  set a := (1 - z).im / ‖1 - z‖ with ha
  have hw : 0 < ‖1 - z‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h; rw [← h] at hz; simp at hz
  have hab : |a| ≤ ‖z‖ := by
    rw [ha, abs_div, abs_norm, div_le_iff₀ hw]
    have h1 : |(1 - z).im| = |z.im| := by simp [abs_neg]
    rw [h1]
    have hx := Complex.sq_norm z
    have hy := Complex.sq_norm (1 - z)
    rw [Complex.normSq_apply] at hx hy
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at hy
    have key : z.im ^ 2 ≤ (‖z‖ * ‖1 - z‖) ^ 2 := by
      rw [mul_pow, hx, hy]
      nlinarith [sq_nonneg (z.re - z.re ^ 2 - z.im ^ 2)]
    have h0 : 0 ≤ ‖z‖ * ‖1 - z‖ := by positivity
    calc |z.im| = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((‖z‖ * ‖1 - z‖) ^ 2) := Real.sqrt_le_sqrt key
      _ = ‖z‖ * ‖1 - z‖ := Real.sqrt_sq h0
  rw [abs_le]
  constructor
  · rw [← Real.arcsin_neg]; exact Real.arcsin_le_arcsin (by linarith [neg_abs_le a])
  · exact Real.arcsin_le_arcsin (le_trans (le_abs_self a) hab)

lemma norm_prime_cpow (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I)‖ ≤ 1 / Real.sqrt 2 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  have hre : (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I).re = -(1 / 2) := by simp
  rw [hre, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  rw [one_div]
  apply inv_anti₀ (by positivity)
  exact Real.sqrt_le_sqrt (by exact_mod_cast hn)

lemma arcsin_inv_sqrt_two : Real.arcsin (1 / Real.sqrt 2) = π / 4 := by
  have h : 1 / Real.sqrt 2 = Real.sin (π / 4) := by
    rw [Real.sin_pi_div_four]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

lemma abs_eulerArg_le (n : ℕ) (hn : 2 ≤ n) (t : ℝ) : |eulerArg n t| ≤ π / 4 := by
  have h1 := norm_prime_cpow n hn t
  have hlt : (1 : ℝ) / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    exact this
  calc |eulerArg n t| ≤ Real.arcsin ‖(n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I)‖ :=
        abs_arg_one_sub_le _ (lt_of_le_of_lt h1 hlt)
    _ ≤ Real.arcsin (1 / Real.sqrt 2) := Real.arcsin_le_arcsin h1
    _ = π / 4 := arcsin_inv_sqrt_two

/-- Eq. (7.1): `|Φ_m(t)| ≤ m/4`. -/
lemma abs_PhiM_le (m : ℕ) (t : ℝ) : |PhiM m t| ≤ m / 4 := by
  unfold PhiM
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have h : |∑ ν ∈ Finset.range m, eulerArg (prime ν) t| ≤ m * (π / 4) := by
    calc |∑ ν ∈ Finset.range m, eulerArg (prime ν) t| ≤ ∑ ν ∈ Finset.range m, |eulerArg (prime ν) t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ν ∈ Finset.range m, π / 4 := Finset.sum_le_sum (fun ν _ => abs_eulerArg_le _ (two_le_prime ν) t)
      _ = m * (π / 4) := by simp
  calc 1 / π * |∑ ν ∈ Finset.range m, eulerArg (prime ν) t| ≤ 1 / π * (m * (π / 4)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = m / 4 := by field_simp

/-! ### Dyadic blocks -/

lemma two_zpow_pos (j : ℤ) : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j

lemma blk_eq {t : ℝ} (ht : 0 < t) {j : ℤ} (h1 : (2 : ℝ) ^ j ≤ t) (h2 : t < (2 : ℝ) ^ (j + 1)) : blk t = j := by
  unfold blk
  have a := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) ht).mp (by exact_mod_cast h1)
  have b := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) ht).mp (by exact_mod_cast h2)
  omega

lemma mem_blk {t : ℝ} (ht : 0 < t) : (2 : ℝ) ^ blk t ≤ t ∧ t < (2 : ℝ) ^ (blk t + 1) := by
  unfold blk
  exact ⟨by exact_mod_cast Int.zpow_log_le_self (b := 2) (by norm_num) ht,
    by exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) (by norm_num) t⟩

lemma rpow_half_sq (j : ℤ) : ((2 : ℝ) ^ ((j : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  push_cast
  rw [show (j : ℝ) / 2 * 2 = (j : ℝ) by ring, Real.rpow_intCast]

lemma budget_le_rpow (j : ℤ) : (budget j : ℝ) ≤ (2 : ℝ) ^ ((j : ℝ) / 2) :=
  Nat.floor_le (by positivity)

lemma budget_sq_le (j : ℤ) : (budget j : ℝ) ^ 2 ≤ (2 : ℝ) ^ j := by
  rw [← rpow_half_sq j]
  exact pow_le_pow_left₀ (by positivity) (budget_le_rpow j) 2

lemma budget_mono (j : ℤ) : budget j ≤ budget (j + 1) := by
  unfold budget
  apply Nat.floor_le_floor
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast; linarith

/-- On a dyadic block the phase is the interpolation `G j`. -/
lemma Phi_eq_G {j : ℤ} {t : ℝ} (h1 : (2 : ℝ) ^ j ≤ t) (h2 : t ≤ (2 : ℝ) ^ (j + 1)) : Phi t = G j t := by
  have ht : 0 < t := lt_of_lt_of_le (two_zpow_pos j) h1
  rcases lt_or_eq_of_le h2 with h | h
  · unfold Phi; rw [blk_eq ht h1 h]
  · have hb : blk t = j + 1 := blk_eq ht (le_of_eq h.symm) (by
      rw [h]; exact zpow_lt_zpow_right₀ (by norm_num) (by omega))
    unfold Phi; rw [hb]
    unfold G
    have hj := two_zpow_pos j
    have e1 : t / (2 : ℝ) ^ (j + 1) = 1 := by rw [h]; exact div_self (two_zpow_pos _).ne'
    have e2 : t / (2 : ℝ) ^ j = 2 := by
      rw [h, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; field_simp
    rw [e1, e2]; ring

lemma abs_G_le {j : ℤ} {t : ℝ} (h1 : (2 : ℝ) ^ j ≤ t) (h2 : t ≤ (2 : ℝ) ^ (j + 1)) :
    |G j t| ≤ (budget (j + 1) : ℝ) / 4 := by
  have hj := two_zpow_pos j
  have hw1 : 0 ≤ 2 - t / (2 : ℝ) ^ j := by
    rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)] at h2
    rw [sub_nonneg, div_le_iff₀ hj]; linarith
  have hw2 : 0 ≤ t / (2 : ℝ) ^ j - 1 := by
    rw [sub_nonneg, le_div_iff₀ hj]; linarith
  have hm : (budget j : ℝ) ≤ budget (j + 1) := by exact_mod_cast budget_mono j
  unfold G
  calc |(2 - t / (2 : ℝ) ^ j) * PhiM (budget j) t + (t / (2 : ℝ) ^ j - 1) * PhiM (budget (j + 1)) t|
      ≤ (2 - t / (2 : ℝ) ^ j) * |PhiM (budget j) t| + (t / (2 : ℝ) ^ j - 1) * |PhiM (budget (j + 1)) t| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2]
    _ ≤ (2 - t / (2 : ℝ) ^ j) * ((budget (j + 1) : ℝ) / 4) + (t / (2 : ℝ) ^ j - 1) * ((budget (j + 1) : ℝ) / 4) := by
        gcongr
        · exact le_trans (abs_PhiM_le _ t) (by linarith)
        · exact abs_PhiM_le _ t
    _ = (budget (j + 1) : ℝ) / 4 := by ring

lemma abs_Phi_le_budget {t : ℝ} (ht : 0 < t) : |Phi t| ≤ (budget (blk t + 1) : ℝ) / 4 := by
  obtain ⟨h1, h2⟩ := mem_blk ht
  unfold Phi
  exact abs_G_le h1 h2.le

/-- Eq. (7.2): `|Φ(t)| ≤ √(2t)/4`. -/
lemma abs_Phi_le_sqrt {t : ℝ} (ht : 0 < t) : |Phi t| ≤ Real.sqrt (2 * t) / 4 := by
  obtain ⟨h1, h2⟩ := mem_blk ht
  have hb := budget_sq_le (blk t + 1)
  have h3 : (2 : ℝ) ^ (blk t + 1) ≤ 2 * t := by
    rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; linarith
  have h4 : (budget (blk t + 1) : ℝ) ≤ Real.sqrt (2 * t) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg (budget (blk t + 1)))]
    exact Real.sqrt_le_sqrt (le_trans hb h3)
  linarith [abs_Phi_le_budget ht]

/-! ### Continuity -/

lemma continuous_eulerArg (n : ℕ) (hn : 2 ≤ n) : Continuous (eulerArg n) := by
  have hc : Continuous fun t : ℝ => (n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I) :=
    (by fun_prop : Continuous fun t : ℝ => -(1 / 2 : ℂ) - (t : ℂ) * Complex.I).const_cpow
      (Or.inl (by exact_mod_cast (show n ≠ 0 by omega)))
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  apply (Complex.continuousAt_arg _).comp (continuous_const.sub hc).continuousAt
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 := norm_prime_cpow n hn t
  have h2 := Complex.abs_re_le_norm ((n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I))
  have h3 : (1 : ℝ) / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by positivity)]
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  show 0 < (1 - (n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re
  rw [Complex.sub_re, Complex.one_re]
  linarith [le_abs_self ((n : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I)).re]

lemma continuous_PhiM (m : ℕ) : Continuous (PhiM m) := by
  unfold PhiM
  exact continuous_const.mul (continuous_finsetSum _ (fun ν _ => continuous_eulerArg _ (two_le_prime ν)))

lemma continuous_G (j : ℤ) : Continuous (G j) := by
  unfold G
  have := continuous_PhiM (budget j)
  have := continuous_PhiM (budget (j + 1))
  fun_prop

lemma continuousAt_Phi {t : ℝ} (ht : 0 < t) : ContinuousAt Phi t := by
  obtain ⟨h1, h2⟩ := mem_blk ht
  set j := blk t
  rcases lt_or_eq_of_le h1 with hlt | heq
  · -- interior of the block
    have hev : Phi =ᶠ[nhds t] G j := by
      filter_upwards [Ioo_mem_nhds hlt h2] with x hx
      exact Phi_eq_G hx.1.le hx.2.le
    exact (continuous_G j).continuousAt.congr hev.symm
  · -- left endpoint t = 2^j
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have hl : (2 : ℝ) ^ (j - 1) < t := by
        rw [← heq]; exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
      have hev : Phi =ᶠ[nhdsWithin t (Iic t)] G (j - 1) := by
        filter_upwards [Ioc_mem_nhdsLE hl] with x hx
        exact Phi_eq_G hx.1.le (by rw [show j - 1 + 1 = j by ring, heq]; exact hx.2)
      have hval : Phi t = G (j - 1) t := Phi_eq_G hl.le (by rw [show j - 1 + 1 = j by ring, heq])
      exact ((continuous_G (j - 1)).continuousWithinAt).congr_of_eventuallyEq hev hval
    · have hev : Phi =ᶠ[nhdsWithin t (Ici t)] G j := by
        filter_upwards [Ico_mem_nhdsGE h2] with x hx
        exact Phi_eq_G (by rw [heq]; exact hx.1) hx.2.le
      have hval : Phi t = G j t := Phi_eq_G (le_of_eq heq) h2.le
      exact ((continuous_G j).continuousWithinAt).congr_of_eventuallyEq hev hval

lemma continuousAt_N0 {t : ℝ} (ht : 0 < t) : ContinuousAt N0 t := by
  unfold N0
  have : t / (2 * π * Real.exp 1) ≠ 0 := by positivity
  fun_prop (disch := assumption)

lemma continuousAt_F {t : ℝ} (ht : 0 < t) : ContinuousAt F t :=
  (continuousAt_N0 ht).add (continuousAt_Phi ht)

lemma continuousOn_F : ContinuousOn F (Ioi 0) := fun _ ht => (continuousAt_F ht).continuousWithinAt

/-! ### Values at `2π` -/

lemma blk_two_pi : blk (2 * π) = 2 := by
  apply blk_eq (by positivity)
  · norm_num; linarith [Real.pi_gt_three]
  · norm_num; linarith [Real.pi_lt_four]

lemma budget_three : budget 3 = 2 := by
  unfold budget
  have hsq := rpow_half_sq 3
  set x := (2 : ℝ) ^ (((3 : ℤ) : ℝ) / 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have h8 : x ^ 2 = 8 := by rw [hsq]; norm_num
  rw [Nat.floor_eq_iff hx0]
  constructor
  · push_cast; nlinarith
  · push_cast; nlinarith

lemma N0_two_pi : N0 (2 * π) = -1 / 8 := by
  unfold N0
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have e1 : 2 * π / (2 * π) = 1 := div_self (by positivity)
  have e2 : 2 * π / (2 * π * Real.exp 1) = (Real.exp 1)⁻¹ := by field_simp
  rw [e1, e2, Real.log_inv, Real.log_exp]
  norm_num

lemma F_two_pi_le : F (2 * π) ≤ 3 / 8 := by
  have h := abs_Phi_le_budget (t := 2 * π) (by positivity)
  rw [blk_two_pi, show (2 : ℤ) + 1 = 3 by norm_num, budget_three] at h
  unfold F
  rw [N0_two_pi]
  have := le_abs_self (Phi (2 * π))
  push_cast at h
  linarith

/-! ### Growth of `N0` and of `F` -/

lemma N0_sub_ge {τ t : ℝ} (hτ : 0 < τ) (htτ : τ ≤ t) :
    (t - τ) * Real.log (τ / (2 * π)) / (2 * π) ≤ N0 t - N0 τ := by
  have ht : 0 < t := lt_of_lt_of_le hτ htτ
  have hpi : 0 < π := Real.pi_pos
  have hL : ∀ x : ℝ, 0 < x → Real.log (x / (2 * π * Real.exp 1)) = Real.log x - Real.log (2 * π) - 1 := by
    intro x hx
    rw [Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp]; ring
  have hL2 : Real.log (τ / (2 * π)) = Real.log τ - Real.log (2 * π) := Real.log_div hτ.ne' (by positivity)
  have key : t - τ ≤ t * (Real.log t - Real.log τ) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < τ / t by positivity)
    rw [Real.log_div hτ.ne' ht.ne'] at h1
    have h2 : t * (τ / t) = τ := by field_simp
    nlinarith
  unfold N0
  rw [hL t ht, hL τ hτ, hL2]
  rw [div_le_iff₀ (by positivity)]
  have e : (t / (2 * π) * (Real.log t - Real.log (2 * π) - 1) + 7 / 8 -
      (τ / (2 * π) * (Real.log τ - Real.log (2 * π) - 1) + 7 / 8)) * (2 * π)
      = t * (Real.log t - Real.log (2 * π) - 1) - τ * (Real.log τ - Real.log (2 * π) - 1) := by
    field_simp
    ring
  rw [e]
  nlinarith

/-- For `τ ≥ 2πe` and `t ≥ 2τ`, `F t > N0 τ` (proof of Proposition 7.1). -/
lemma N0_lt_F {τ t : ℝ} (hτ : 2 * π * Real.exp 1 ≤ τ) (ht : 2 * τ ≤ t) : N0 τ < F t := by
  have hpi : 0 < π := Real.pi_pos
  have he : 2 < Real.exp 1 := Real.exp_one_gt_two
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log (τ / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]; linarith
  have h1 := N0_sub_ge hτ0 (show τ ≤ t by linarith)
  have hA : t / 2 ≤ (t - τ) * Real.log (τ / (2 * π)) := by
    have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ t - τ by linarith)
    linarith
  have h2 : t / (4 * π) ≤ N0 t - N0 τ := by
    refine le_trans ?_ h1
    calc t / (4 * π) = (t / 2) / (2 * π) := by field_simp; ring
      _ ≤ (t - τ) * Real.log (τ / (2 * π)) / (2 * π) := div_le_div_of_nonneg_right hA (by positivity)
  have hbig : 2 * π ^ 2 < t := by
    have : 4 * π * Real.exp 1 ≤ t := by linarith
    nlinarith [Real.pi_lt_four, Real.pi_gt_three]
  have h3 : Real.sqrt (2 * t) < t / π := by
    rw [Real.sqrt_lt' (by positivity), div_pow, lt_div_iff₀ (by positivity)]
    nlinarith
  have h4 := abs_Phi_le_sqrt ht0
  unfold F
  have h5 := neg_abs_le (Phi t)
  have h6 : t / π / 4 = t / (4 * π) := by field_simp
  linarith

/-! ### Proposition 7.1 -/

/-- The sublevel set `{t > 0 : F t < c}`. -/
def Sub (c : ℝ) : Set ℝ := {t ∈ Ioi (0 : ℝ) | F t < c}

lemma exists_tau (c : ℝ) : ∃ τ : ℝ, 2 * π * Real.exp 1 ≤ τ ∧ c ≤ N0 τ := by
  set s := max c 1 with hs
  refine ⟨2 * π * Real.exp 1 * Real.exp s, ?_, ?_⟩
  · have : 1 ≤ Real.exp s := Real.one_le_exp (by positivity)
    have : 0 < 2 * π * Real.exp 1 := by positivity
    nlinarith
  · unfold N0
    have hpi : 0 < π := Real.pi_pos
    have e1 : 2 * π * Real.exp 1 * Real.exp s / (2 * π * Real.exp 1) = Real.exp s := by field_simp
    have e2 : 2 * π * Real.exp 1 * Real.exp s / (2 * π) = Real.exp 1 * Real.exp s := by field_simp
    rw [e1, e2, Real.log_exp]
    have h1 : 1 ≤ Real.exp 1 * Real.exp s := by
      have := Real.one_le_exp (show (0:ℝ) ≤ 1 by norm_num)
      have := Real.one_le_exp (show (0:ℝ) ≤ s by positivity)
      nlinarith
    have hs1 : 1 ≤ s := le_max_right _ _
    have hcs : c ≤ s := le_max_left _ _
    nlinarith

lemma Sub_subset (c : ℝ) : ∃ R : ℝ, 0 < R ∧ Sub c ⊆ Ioo 0 R := by
  obtain ⟨τ, hτ, hc⟩ := exists_tau c
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  refine ⟨2 * τ, by positivity, fun t ht => ⟨ht.1, ?_⟩⟩
  by_contra h
  push Not at h
  have := N0_lt_F hτ h
  linarith [ht.2]

/-- **Proposition 7.1 (i)**: each sublevel set has finite measure. -/
theorem volume_Sub_lt_top (c : ℝ) : volume (Sub c) < ⊤ := by
  obtain ⟨R, _, h⟩ := Sub_subset c
  exact lt_of_le_of_lt (measure_mono h) (by simp)

lemma exists_Ioo_sub {t₀ a b : ℝ} (ht₀ : 0 < t₀) (ha : a < F t₀) (hb : F t₀ < b) :
    ∃ ε > 0, Ioo (t₀ - ε) (t₀ + ε) ⊆ {t ∈ Ioi (0 : ℝ) | a < F t ∧ F t < b} := by
  have h1 : ∀ᶠ x in nhds t₀, F x ∈ Ioo a b := (continuousAt_F ht₀).eventually (Ioo_mem_nhds ha hb)
  have h2 : ∀ᶠ x in nhds t₀, x ∈ Ioi (0 : ℝ) := Ioi_mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (h1.and h2)
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hd : dist x t₀ < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  obtain ⟨⟨h3, h4⟩, h5⟩ := hball hd
  exact ⟨h5, h3, h4⟩

/-- **Proposition 7.1 (ii)**: `0 < x_k` for `k ≥ 1`. -/
theorem xClock_pos {k : ℕ} (hk : 1 ≤ k) : 0 < xClock k := by
  have hF := F_two_pi_le
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨ε, hε, hsub⟩ := exists_Ioo_sub (t₀ := 2 * π) (a := F (2 * π) - 1) (b := (k : ℝ) - 1 / 2)
    (by positivity) (by linarith) (by linarith)
  have hsub' : Ioo (2 * π - ε) (2 * π + ε) ⊆ Sub ((k : ℝ) - 1 / 2) := fun x hx => ⟨(hsub hx).1, (hsub hx).2.2⟩
  have hpos : 0 < volume (Sub ((k : ℝ) - 1 / 2)) := by
    refine lt_of_lt_of_le ?_ (measure_mono hsub')
    rw [Real.volume_Ioo]; simp; linarith
  unfold xClock
  exact ENNReal.toReal_pos hpos.ne' (volume_Sub_lt_top _).ne

/-- **Proposition 7.1 (ii)**: `x_k < x_{k+1}` for `k ≥ 1`. -/
theorem xClock_lt_succ {k : ℕ} (hk : 1 ≤ k) : xClock k < xClock (k + 1) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨τ, hτ, hc⟩ := exists_tau (k : ℝ)
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hR : 2 * π ≤ 2 * τ := by
    have : 2 * π ≤ 2 * π * Real.exp 1 := by nlinarith [Real.exp_one_gt_two]
    linarith
  have hFR : (k : ℝ) < F (2 * τ) := lt_of_le_of_lt hc (N0_lt_F hτ le_rfl)
  have hF0 : F (2 * π) < (k : ℝ) := by linarith [F_two_pi_le]
  have hcont : ContinuousOn F (Icc (2 * π) (2 * τ)) :=
    continuousOn_F.mono (fun x hx => lt_of_lt_of_le (by positivity) hx.1)
  obtain ⟨t₀, ht₀, hFt₀⟩ := intermediate_value_Icc hR hcont ⟨hF0.le, hFR.le⟩
  have ht₀pos : 0 < t₀ := lt_of_lt_of_le (by positivity) ht₀.1
  obtain ⟨ε, hε, hsub⟩ := exists_Ioo_sub (t₀ := t₀) (a := (k : ℝ) - 1 / 2) (b := (k : ℝ) + 1 / 2)
    ht₀pos (by linarith) (by linarith)
  set I := Ioo (t₀ - ε) (t₀ + ε)
  have hcast : ((k + 1 : ℕ) : ℝ) - 1 / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  have hdisj : Disjoint (Sub ((k : ℝ) - 1 / 2)) I := by
    rw [Set.disjoint_left]
    intro x hx hxI
    have := (hsub hxI).2.1
    linarith [hx.2]
  have hU : Sub ((k : ℝ) - 1 / 2) ∪ I ⊆ Sub ((k : ℝ) + 1 / 2) := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨hx.1, by linarith [hx.2]⟩
    · exact ⟨(hsub hx).1, (hsub hx).2.2⟩
  have hvol : volume (Sub ((k : ℝ) - 1 / 2)) + volume I ≤ volume (Sub ((k : ℝ) + 1 / 2)) := by
    rw [← measure_union hdisj measurableSet_Ioo]; exact measure_mono hU
  have hI : volume I = ENNReal.ofReal (2 * ε) := by
    rw [Real.volume_Ioo]; congr 1; ring
  have hfin1 := (volume_Sub_lt_top ((k : ℝ) - 1 / 2)).ne
  have hfin2 := (volume_Sub_lt_top ((k : ℝ) + 1 / 2)).ne
  unfold xClock
  rw [hcast]
  have h1 := ENNReal.toReal_mono hfin2 hvol
  rw [ENNReal.toReal_add hfin1 (by rw [hI]; exact ENNReal.ofReal_ne_top), hI, ENNReal.toReal_ofReal (by linarith)] at h1
  show (volume (Sub ((k : ℝ) - 1 / 2))).toReal < (volume (Sub ((k : ℝ) + 1 / 2))).toReal
  linarith

/-- **Proposition 7.1 (iii)**: truncation at `2τ_k` when `τ_k ≥ 2πe`. -/
theorem Sub_subset_two_tau {τ : ℝ} (hτ : 2 * π * Real.exp 1 ≤ τ) {c : ℝ} (hc : c ≤ N0 τ) :
    Sub c ⊆ Ioo 0 (2 * τ) := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  by_contra h
  push Not at h
  have := N0_lt_F hτ h
  linarith [ht.2]

/-- **Proposition 7.1 (iii)**: for `0 < t ≤ 2τ`, `F t` uses only the primes `p_ν`,
`ν ≤ budget (blk t + 1) ≤ ⌊2√τ⌋`. -/
theorem budget_le_two_sqrt {τ t : ℝ} (ht : 0 < t) (htτ : t ≤ 2 * τ) :
    budget (blk t) ≤ budget (blk t + 1) ∧ budget (blk t + 1) ≤ ⌊2 * Real.sqrt τ⌋₊ := by
  refine ⟨budget_mono _, ?_⟩
  obtain ⟨h1, h2⟩ := mem_blk ht
  have hb := budget_sq_le (blk t + 1)
  have h3 : (2 : ℝ) ^ (blk t + 1) ≤ 4 * τ := by
    rw [zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; linarith
  have hτ : 0 ≤ τ := by linarith
  apply Nat.le_floor
  rw [← Real.sqrt_sq (Nat.cast_nonneg (budget (blk t + 1)))]
  calc Real.sqrt ((budget (blk t + 1) : ℝ) ^ 2) ≤ Real.sqrt (4 * τ) := Real.sqrt_le_sqrt (le_trans hb h3)
    _ = 2 * Real.sqrt τ := by
        rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end RvmClock
