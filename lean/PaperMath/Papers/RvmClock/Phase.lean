import PaperMath.Papers.RvmClock.PrimeFourth
import PaperMath.Papers.RvmClock.Construction
import PaperMath.Papers.RvmClock.Mertens
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.PSeries

/-!
# Expansion of the finite Euler phase (equation (7.5) `phase_split` in the proof of Lemma 7.6)

`Φ_m(t) = (1/π) Im Σ_{ν<m} p_ν^{-1/2-it} + (1/2π) Im Σ_{ν<m} p_ν^{-1-2it} + Φ⁽³⁾(t)`,
with `|Φ⁽³⁾(t)| ≤ K` uniformly in `m` and `t`.
-/

open Complex Finset
open scoped ComplexConjugate Real

namespace RvmClock

/-- `z_p(t) = p^{-1/2-it}`, the same expression as in `eulerArg`. -/
noncomputable def zp (p : ℕ) (t : ℝ) : ℂ := (p : ℂ) ^ (-(1 / 2 : ℂ) - (t : ℂ) * Complex.I)

lemma eulerArg_eq (p : ℕ) (t : ℝ) : eulerArg p t = Complex.arg (1 - zp p t) := rfl

lemma zp_eq {p : ℕ} (hp : 0 < p) (t : ℝ) :
    zp p t = (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * ex (t * Real.log p) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  unfold zp ex
  rw [Real.rpow_def_of_pos hp', Complex.ofReal_exp, ← Complex.exp_add,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  congr 1
  have : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hp'.le]; push_cast; rfl
  rw [this]; push_cast; ring

lemma norm_zp {p : ℕ} (hp : 0 < p) (t : ℝ) : ‖zp p t‖ = (p : ℝ) ^ (-(1 / 2) : ℝ) := by
  rw [zp_eq hp, norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

lemma rpow_half_sq' {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2) : ℝ)) ^ 2 = 1 / x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  rw [Real.rpow_neg_one]

lemma zp_sq {p : ℕ} (hp : 0 < p) (t : ℝ) :
    zp p t ^ 2 = (((1 / (p : ℝ)) : ℝ) : ℂ) * ex (t * Real.log ((p : ℝ) ^ 2)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [zp_eq hp, mul_pow, ← Complex.ofReal_pow, rpow_half_sq' hp', sq (ex _), ex_add, Real.log_pow]
  congr 2; push_cast; ring

lemma norm_zp_le {p : ℕ} (hp : 2 ≤ p) (t : ℝ) : ‖zp p t‖ ≤ 3 / 4 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [norm_zp (by omega)]
  have h0 : 0 ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have h2 : ((p : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 ≤ 1 / 2 := by
    rw [rpow_half_sq' (by linarith)]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  nlinarith

lemma norm_zp_cube {p : ℕ} (hp : 0 < p) (t : ℝ) : ‖zp p t‖ ^ 3 = (p : ℝ) ^ (-(3 / 2) : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [norm_zp hp, ← Real.rpow_natCast, ← Real.rpow_mul hp'.le]; norm_num

/-- Third-order expansion of `arg (1 − z_p)`. -/
lemma eulerArg_expand {p : ℕ} (hp : 2 ≤ p) (t : ℝ) :
    |eulerArg p t + (zp p t).im + (zp p t ^ 2).im / 2| ≤ 4 / 3 * (p : ℝ) ^ (-(3 / 2) : ℝ) := by
  set z := zp p t
  have hz : ‖z‖ ≤ 3 / 4 := norm_zp_le hp t
  have hw : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have key := Complex.norm_log_sub_logTaylor_le 2 hw
  have hT : Complex.logTaylor (2 + 1) (-z) = -z - z ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]; ring
  rw [hT, norm_neg] at key
  have harg : eulerArg p t = (Complex.log (1 + -z)).im := by
    rw [eulerArg_eq, Complex.log_im, ← sub_eq_add_neg]
  have him : eulerArg p t + z.im + (z ^ 2).im / 2 = (Complex.log (1 + -z) - (-z - z ^ 2 / 2)).im := by
    rw [harg]; simp [Complex.sub_im, Complex.div_im]; ring
  rw [him]
  refine le_trans (Complex.abs_im_le_norm _) (le_trans key ?_)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hc : ‖z‖ ^ (2 + 1) = (p : ℝ) ^ (-(3 / 2) : ℝ) := norm_zp_cube (by omega) t
  rw [hc]
  have h0 : 0 ≤ (p : ℝ) ^ (-(3 / 2) : ℝ) := by positivity
  have : (p : ℝ) ^ (-(3 / 2) : ℝ) * (1 - ‖z‖)⁻¹ ≤ (p : ℝ) ^ (-(3 / 2) : ℝ) * 4 :=
    mul_le_mul_of_nonneg_left hinv h0
  push_cast
  linarith

lemma prime_injective : Function.Injective prime := Nat.nth_injective Nat.infinite_setOf_prime

lemma summable_rpow32 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
  Real.summable_nat_rpow.mpr (by norm_num)

lemma sum_prime_rpow32_le (m : ℕ) :
    ∑ ν ∈ Finset.range m, ((prime ν : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  rw [← Finset.sum_image (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2) : ℝ))
    (fun a _ b _ h => prime_injective h)]
  exact summable_rpow32.sum_le_tsum _ (fun i _ => by positivity)

/-- **Expansion of the finite Euler phase**, uniformly in `m` and `t`. -/
theorem PhiM_expand :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (t : ℝ),
      |PhiM m t - (1 / π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t).im
        - 1 / (2 * π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t ^ 2).im| ≤ K := by
  set Z := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => by positivity)
  refine ⟨1 / π * (4 / 3 * Z), by positivity, fun m t => ?_⟩
  have hid : PhiM m t - (1 / π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t).im
      - 1 / (2 * π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t ^ 2).im
      = -(1 / π) * ∑ ν ∈ Finset.range m,
          (eulerArg (prime ν) t + (zp (prime ν) t).im + (zp (prime ν) t ^ 2).im / 2) := by
    unfold PhiM
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    field_simp; ring
  rw [hid, abs_mul, abs_neg, abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ ν ∈ Finset.range m, |eulerArg (prime ν) t + (zp (prime ν) t).im + (zp (prime ν) t ^ 2).im / 2|
      ≤ ∑ ν ∈ Finset.range m, 4 / 3 * ((prime ν : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
        Finset.sum_le_sum (fun ν _ => eulerArg_expand (two_le_prime ν) t)
    _ = 4 / 3 * ∑ ν ∈ Finset.range m, ((prime ν : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 4 / 3 * Z := mul_le_mul_of_nonneg_left (sum_prime_rpow32_le m) (by norm_num)

end RvmClock
