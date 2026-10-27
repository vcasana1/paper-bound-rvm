import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 1.3 of `rvm_clock_envelope`: the final deduction

From the assembled inequality (5.5) at `T ≥ 100` (Proposition 5.1 with Lemma 4.4) and Platt's
bound (Theorem 3.6) on `[e, 100]`, we deduce
`|S(T)| ≤ 0.09783 log T + 0.7214 log log T + 10.6` for every `T ≥ e`, and the `N(T)` version with `10.7`.

`C₂ = 1/(2𝔡)`, `𝔡 = log (R/(c-1/2))`, `c = 1.000002`, `R = 1.000005` is computed here.
The values of `C₁`, `log ζ(σ♯)` and the bound for `𝓔(T,δ♯)/(2π)` enter as hypotheses
(numerical inequalities checked separately with interval arithmetic).
-/

namespace RvmClock.Explicit

open Real

noncomputable def cc : ℝ := 1.000002
noncomputable def RR : ℝ := 1.000005
/-- `𝔡 = log (R / (c - 1/2))`. -/
noncomputable def dd : ℝ := Real.log (RR / (cc - 1 / 2))
/-- `C₂ = 1 / (2𝔡)`. -/
noncomputable def C2 : ℝ := 1 / (2 * dd)

lemma log_two_lt_dd : Real.log 2 < dd := by
  unfold dd cc RR
  exact Real.log_lt_log (by norm_num) (by norm_num)

lemma dd_pos : 0 < dd := lt_trans (Real.log_pos (by norm_num)) log_two_lt_dd

lemma C2_nonneg : 0 ≤ C2 := by
  unfold C2; have := dd_pos; positivity

lemma C2_le : C2 ≤ 0.7213476 := by
  unfold C2
  have h := Real.log_two_gt_d9
  have h2 := log_two_lt_dd
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma C2_lt : C2 < 0.7214 := lt_of_le_of_lt C2_le (by norm_num)

lemma log_274 : Real.log 2.74 ≤ 1.008 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 1.008 = Real.exp 1 * Real.exp 0.008 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_one_gt_d9
  have h3 : (0.008 : ℝ) + 1 ≤ Real.exp 0.008 := Real.add_one_le_exp _
  rw [h1]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.008]

lemma log_100 : (4.158 : ℝ) ≤ Real.log 100 := by
  have h1 : Real.log 64 ≤ Real.log 100 := Real.log_le_log (by norm_num) (by norm_num)
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

/-- `log (T + a) ≤ log T + a / T`. -/
lemma log_add_le {T a : ℝ} (hT : 0 < T) (ha : 0 ≤ a) :
    Real.log (T + a) ≤ Real.log T + a / T := by
  have h1 : Real.log ((T + a) / T) ≤ (T + a) / T - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) hT.ne'] at h1
  have : (T + a) / T - 1 = a / T := by field_simp; ring
  linarith

/-- `log log (T + 2) ≤ log log T + 2 / (T log T)` for `T > 1`. -/
lemma loglog_add_le {T : ℝ} (hT : 1 < T) :
    Real.log (Real.log (T + 2)) ≤ Real.log (Real.log T) + 2 / (T * Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hL2 : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have h1 : Real.log (Real.log (T + 2) / Real.log T) ≤ Real.log (T + 2) / Real.log T - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hL2.ne' hL.ne'] at h1
  have h2 := log_add_le hT0 (by norm_num : (0 : ℝ) ≤ 2)
  have h3 : Real.log (T + 2) / Real.log T - 1 ≤ 2 / (T * Real.log T) := by
    rw [div_sub_one hL.ne', div_le_div_iff₀ hL (by positivity)]
    have : (Real.log (T + 2) - Real.log T) ≤ 2 / T := by linarith
    have h4 : (Real.log (T + 2) - Real.log T) * T ≤ 2 := by
      rwa [le_div_iff₀ hT0] at this
    nlinarith
  linarith

/-- Theorem 1.3, inequality (1.7). -/
theorem explicit_S (S : ℝ → ℝ) (C1 Lz : ℝ) (E : ℝ → ℝ)
    (hC1 : C1 ≤ 0.0978293) (hC1' : 0 ≤ C1) (hLz : Lz ≤ 1.52499)
    (hE : ∀ T, 100 ≤ T → E T ≤ 0.00055)
    (hmaster : ∀ T, 100 ≤ T → |S T| ≤ C1 * Real.log (T + 2) + C2 * Real.log (Real.log (T + 2))
        + C2 * (12.62467 + Real.log ((T + 3) / T) + Real.log 2.74) + Lz / π
        + 0.7501 / (π * T) + E T + 1 / 4)
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 := by
  intro T hT
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT
  have hLL : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hL1
  have hLpos : 0 ≤ Real.log T := by linarith
  rcases le_or_gt T 100 with h100 | h100
  · have := hplatt T hT h100
    nlinarith
  · have h100' : (100 : ℝ) ≤ T := h100.le
    have hm := hmaster T h100'
    have hpi := Real.pi_gt_d6
    have hpi0 : 0 < π := Real.pi_pos
    have hLT : (4.158 : ℝ) ≤ Real.log T :=
      le_trans log_100 (Real.log_le_log (by norm_num) h100')
    -- the three logarithmic shifts
    have a1 := log_add_le hT0 (by norm_num : (0 : ℝ) ≤ 2)
    have a2 := loglog_add_le hT1
    have a3 : Real.log ((T + 3) / T) ≤ 0.03 := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (T + 3) / T)
      have : (T + 3) / T - 1 = 3 / T := by field_simp; ring
      have h3 : 3 / T ≤ 0.03 := by rw [div_le_iff₀ hT0]; linarith
      linarith
    have hC2 := C2_le
    have hC20 := C2_nonneg
    have b1 : 2 / T ≤ 0.02 := by rw [div_le_iff₀ hT0]; linarith
    have b2 : 2 / (T * Real.log T) ≤ 2 / (100 * 4.158) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have b3 : Lz / π ≤ 1.52499 / 3.141592 := by
      calc Lz / π ≤ 1.52499 / π := by gcongr
        _ ≤ 1.52499 / 3.141592 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi.le
    have b4 : 0.7501 / (π * T) ≤ 0.7501 / (3.141592 * 100) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    have hET := hE T h100'
    have l274 := log_274
    -- assemble
    have k1 : C1 * Real.log (T + 2) ≤ 0.09783 * Real.log T + 0.0978293 * 0.02 := by
      have : C1 * Real.log (T + 2) ≤ C1 * Real.log T + C1 * (2 / T) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left a1 hC1'
      nlinarith
    have k2 : C2 * Real.log (Real.log (T + 2))
        ≤ 0.7214 * Real.log (Real.log T) + 0.7213476 * (2 / (100 * 4.158)) := by
      have : C2 * Real.log (Real.log (T + 2))
          ≤ C2 * Real.log (Real.log T) + C2 * (2 / (T * Real.log T)) := by
        rw [← mul_add]; exact mul_le_mul_of_nonneg_left a2 hC20
      have hpos : 0 ≤ 2 / (T * Real.log T) := by positivity
      nlinarith
    have k3 : C2 * (12.62467 + Real.log ((T + 3) / T) + Real.log 2.74)
        ≤ 0.7213476 * (12.62467 + 0.03 + 1.008) := by
      have hlog3 : 0 ≤ Real.log ((T + 3) / T) :=
        Real.log_nonneg (by rw [le_div_iff₀ hT0]; linarith)
      have hlog274 : 0 ≤ Real.log 2.74 := Real.log_nonneg (by norm_num)
      have hin : 12.62467 + Real.log ((T + 3) / T) + Real.log 2.74 ≤ 12.62467 + 0.03 + 1.008 := by
        linarith
      calc C2 * (12.62467 + Real.log ((T + 3) / T) + Real.log 2.74)
          ≤ C2 * (12.62467 + 0.03 + 1.008) := mul_le_mul_of_nonneg_left hin hC20
        _ ≤ 0.7213476 * (12.62467 + 0.03 + 1.008) := by
          apply mul_le_mul_of_nonneg_right hC2 (by norm_num)
    have hnum : 0.0978293 * 0.02 + 0.7213476 * (2 / (100 * 4.158))
        + 0.7213476 * (12.62467 + 0.03 + 1.008) + 1.52499 / 3.141592
        + 0.7501 / (3.141592 * 100) + 0.00055 + 1 / 4 ≤ (10.6 : ℝ) := by norm_num
    linarith

/-- Theorem 1.3, inequality (1.8): `N - N₀ = S + ϖ/π` with `|ϖ(t)| ≤ 0.53/t` (Lemma 4.1). -/
theorem explicit_N (S G varpi : ℝ → ℝ) (hG : ∀ T, G T = S T + varpi T / π)
    (hvarpi : ∀ T, 0 < T → |varpi T| ≤ 0.53 / T)
    (hS : ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6) :
    ∀ T, Real.exp 1 ≤ T →
      |G T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.7 := by
  intro T hT
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hT0 : 0 < T := by linarith
  have hpi := Real.pi_gt_d6
  have hv := hvarpi T hT0
  have h1 : |varpi T / π| ≤ 0.07 := by
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
    have : 0.53 / T ≤ 0.53 / 2.7182818283 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    nlinarith
  rw [hG]
  have := abs_add_le (S T) (varpi T / π)
  have := hS T hT
  linarith

end RvmClock.Explicit

namespace RvmClock.Explicit

/-- `σ♯ = c + (c - 1/2)^2 / R`. -/
noncomputable def sigS : ℝ := cc + (cc - 1 / 2) ^ 2 / RR
/-- `δ♯ = 2c - σ♯ - 1/2`. -/
noncomputable def delS : ℝ := 2 * cc - sigS - 1 / 2

/-- The conditions (3.3) of Theorem 3.5 at `c = 1.000002`, `R = 1.000005`, and `δ♯ ∈ [1/4, 5/8]`. -/
theorem backlund_conditions :
    cc - RR < 1 / 2 ∧ (1 : ℝ) / 2 < 1 ∧ 1 < cc ∧ cc < sigS ∧ sigS < cc + RR ∧ cc < RR ∧
      0 < delS ∧ delS < 1 / 2 ∧ 1 / 4 ≤ delS ∧ delS ≤ 5 / 8 ∧ cc + RR ≤ 3 ∧ -0.01 ≤ cc - RR := by
  unfold delS sigS cc RR
  norm_num

/-- Theorem 3.5(c) at `δ♯`, `T ≥ 100`: `𝓔(T,δ♯)/(2π) < 0.00055`. -/
theorem E_bound (E : ℝ → ℝ)
    (h : ∀ T, 100 ≤ T → E T ≤ (1 / 2) * ((640 * delS - 112) / (1536 * (3 * T - 1)) + (1 / 1024))) :
    ∀ T, 100 ≤ T → E T ≤ 0.00055 := by
  intro T hT
  have h1 := h T hT
  have hd : 640 * delS - 112 ≤ 48.0009 := by unfold delS sigS cc RR; norm_num
  have hd0 : 0 ≤ 640 * delS - 112 := by unfold delS sigS cc RR; norm_num
  have h3 : (640 * delS - 112) / (1536 * (3 * T - 1)) ≤ 48.0009 / (1536 * 299) := by
    apply div_le_div₀ (by norm_num) hd (by norm_num)
    nlinarith
  have : (1 : ℝ) / 2 * (48.0009 / (1536 * 299) + (1 / 1024)) ≤ 0.00055 := by norm_num
  linarith

end RvmClock.Explicit

namespace RvmClock.Explicit

/-- Theorem 1.3 (1.7), from: the assembled bound (5.5) of Proposition 5.1 at `T ≥ 100`, with
`𝓔(T,δ♯)/(2π)` bounded as in Theorem 3.5(c); Platt's bound (Theorem 3.6) on `[e,100]`; and the
numerical values `C₁ ≤ 0.0978293`, `log ζ(σ♯) ≤ 1.52499`. -/
theorem thm_1_3 (S : ℝ → ℝ) (C1 Lz : ℝ) (E : ℝ → ℝ)
    (hC1 : C1 ≤ 0.0978293) (hC1' : 0 ≤ C1) (hLz : Lz ≤ 1.52499)
    (hE : ∀ T, 100 ≤ T → E T ≤ (1 / 2) * ((640 * delS - 112) / (1536 * (3 * T - 1)) + (1 / 1024)))
    (hmaster : ∀ T, 100 ≤ T → |S T| ≤ C1 * Real.log (T + 2) + C2 * Real.log (Real.log (T + 2))
        + C2 * (12.62467 + Real.log ((T + 3) / T) + Real.log 2.74) + Lz / Real.pi
        + 0.7501 / (Real.pi * T) + E T + 1 / 4)
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 :=
  explicit_S S C1 Lz E hC1 hC1' hLz (E_bound E hE) hmaster hplatt

end RvmClock.Explicit
