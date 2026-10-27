import PaperMath.Common.TrigBounds
import PaperMath.Papers.RvmClock.Thm13Zeta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The numerical input `C₁ ≤ 0.0978293` of Theorem 1.3

`C₁ = (1/(2π𝔡)) ∫₀^π 𝔢_E^*(c + R cos θ) dθ`, `c = 1.000002`, `R = 1.000005`, `𝔡 = log (R/(c - 1/2))`.
Value `0.0978292318785…`; margin `6.8 · 10⁻⁸`.

The integrand is piecewise linear in `cos θ` (`Profile.gE` is a sum of hinge terms `max 0 (σ - ς_i)`), so the
integral is computed exactly:
* on `[0, θ_h]` (`σ ≥ 1/2`, `θ_h = arccos ((1/2 - c)/R)`), `𝔢_E^* = gE`, and each hinge integrates to
  `(c - a) θ_a + R sin θ_a`, `θ_a = arccos ((a - c)/R)` (`int_max_a`);
* on `[θ_h, π]` (`σ ≤ 1/2`), `𝔢_E^* = 1/2 - σ + gE (1 - σ)`, and each hinge integrates to
  `(1 - c - a)(π - θ'_a) + R sin θ'_a`, `θ'_a = arccos ((1 - a - c)/R)` (`int_max_b`).
With `arccos x = π/2 + arcsin (-x)` and `sin (arccos x) = √(1 - x²)`, `I` is a linear combination of
`π`, 15 values `arcsin y` (`y` rational) and 15 square roots of rationals; each is bounded to 12 decimals
(`Common.TrigBounds`: alternating Taylor series of `sin`, `Real.pi_gt_d20`), and `linarith` closes.
-/

open Real RvmClock.Profile RvmClock.Explicit RvmClock.ZetaLines Common.TrigBounds intervalIntegral

namespace RvmClock.C1

/-- Kink angle of `max 0 (c + R cos θ - a)`. -/
noncomputable def θa (a : ℝ) : ℝ := arccos ((a - cc) / RR)
/-- Kink angle of `max 0 (1 - (c + R cos θ) - a)`. -/
noncomputable def θb (a : ℝ) : ℝ := arccos ((1 - a - cc) / RR)
/-- `θ_h = θa (1/2)`: the angle where `σ = 1/2`. -/
noncomputable def θh : ℝ := θa (1 / 2)

lemma RR_pos : 0 < RR := by unfold RR; norm_num
lemma RR_ne : RR ≠ 0 := RR_pos.ne'

lemma xa_mem {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : -1 ≤ (a - cc) / RR ∧ (a - cc) / RR ≤ 1 := by
  unfold cc RR
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith

lemma xb_mem {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) :
    -1 ≤ (1 - a - cc) / RR ∧ (1 - a - cc) / RR ≤ 1 := by
  unfold cc RR
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith

lemma cos_θa {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : cos (θa a) = (a - cc) / RR :=
  cos_arccos (xa_mem h1 h2).1 (xa_mem h1 h2).2
lemma cos_θb {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : cos (θb a) = (1 - a - cc) / RR :=
  cos_arccos (xb_mem h1 h2).1 (xb_mem h1 h2).2
lemma θa_nonneg (a : ℝ) : 0 ≤ θa a := arccos_nonneg _
lemma θa_le_pi (a : ℝ) : θa a ≤ π := arccos_le_pi _
lemma θb_nonneg (a : ℝ) : 0 ≤ θb a := arccos_nonneg _
lemma θb_le_pi (a : ℝ) : θb a ≤ π := arccos_le_pi _
lemma θh_nonneg : 0 ≤ θh := θa_nonneg _
lemma θh_le_pi : θh ≤ π := θa_le_pi _
lemma cos_θh : cos θh = (1 / 2 - cc) / RR := cos_θa (by norm_num) (by norm_num)

lemma θa_le_θh {a : ℝ} (h1 : 1 / 2 ≤ a) : θa a ≤ θh := by
  unfold θh θa
  apply arccos_le_arccos
  exact div_le_div_of_nonneg_right (by linarith) RR_pos.le

lemma θh_le_θb {a : ℝ} (h1 : 1 / 2 ≤ a) : θh ≤ θb a := by
  unfold θh θa θb
  apply arccos_le_arccos
  exact div_le_div_of_nonneg_right (by linarith) RR_pos.le

/-! ### Elementary integrals -/

lemma integral_lin (a α β : ℝ) :
    ∫ θ in α..β, (cc + RR * cos θ - a) = (cc - a) * (β - α) + RR * (sin β - sin α) := by
  have e : (fun θ => cc + RR * cos θ - a) = fun θ => (cc - a) + RR * cos θ := by funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => RR * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

lemma integral_lin' (a α β : ℝ) :
    ∫ θ in α..β, (1 - (cc + RR * cos θ) - a) = (1 - cc - a) * (β - α) - RR * (sin β - sin α) := by
  have e : (fun θ => 1 - (cc + RR * cos θ) - a) = fun θ => (1 - cc - a) + (-RR) * cos θ := by
    funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -RR * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

lemma integral_half (α β : ℝ) :
    ∫ θ in α..β, (1 / 2 - (cc + RR * cos θ)) = (1 / 2 - cc) * (β - α) - RR * (sin β - sin α) := by
  have e : (fun θ => 1 / 2 - (cc + RR * cos θ)) = fun θ => (1 / 2 - cc) + (-RR) * cos θ := by
    funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -RR * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

/-- `∫₀^{θ_h} max 0 (c + R cos θ - a) = (c - a) θ_a + R sin θ_a` for `1/2 ≤ a ≤ 1`. -/
lemma int_max_a {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) :
    ∫ θ in (0 : ℝ)..θh, max 0 (cc + RR * cos θ - a) = (cc - a) * θa a + RR * sin (θa a) := by
  have hI : ∀ α β : ℝ, IntervalIntegrable (fun θ => max 0 (cc + RR * cos θ - a)) MeasureTheory.volume α β :=
    fun α β => (continuous_const.max (by fun_prop)).intervalIntegrable α β
  have hR := RR_ne
  have hc := cos_θa h1 h2
  have hcR : RR * ((a - cc) / RR) = a - cc := by field_simp
  rw [← integral_add_adjacent_intervals (hI 0 (θa a)) (hI (θa a) θh)]
  have e1 : ∫ θ in (0 : ℝ)..θa a, max 0 (cc + RR * cos θ - a)
      = ∫ θ in (0 : ℝ)..θa a, (cc + RR * cos θ - a) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θa_nonneg a)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 (θa_le_pi a) hθ.2
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_right (by linarith)
  have e2 : ∫ θ in θa a..θh, max 0 (cc + RR * cos θ - a) = ∫ θ in θa a..θh, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θa_le_θh h1)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θa_nonneg a) (hθ.2.trans θh_le_pi) hθ.1
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_left (by linarith)
  rw [e1, e2, integral_lin, integral_zero, sin_zero]
  ring

/-- `∫_{θ_h}^π max 0 (1 - (c + R cos θ) - a) = (1 - c - a)(π - θ'_a) + R sin θ'_a` for `1/2 ≤ a ≤ 1`. -/
lemma int_max_b {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) :
    ∫ θ in θh..π, max 0 (1 - (cc + RR * cos θ) - a)
      = (1 - cc - a) * (π - θb a) + RR * sin (θb a) := by
  have hI : ∀ α β : ℝ,
      IntervalIntegrable (fun θ => max 0 (1 - (cc + RR * cos θ) - a)) MeasureTheory.volume α β :=
    fun α β => (continuous_const.max (by fun_prop)).intervalIntegrable α β
  have hR := RR_ne
  have hc := cos_θb h1 h2
  have hcR : RR * ((1 - a - cc) / RR) = 1 - a - cc := by field_simp
  rw [← integral_add_adjacent_intervals (hI θh (θb a)) (hI (θb a) π)]
  have e1 : ∫ θ in θh..θb a, max 0 (1 - (cc + RR * cos θ) - a) = ∫ θ in θh..θb a, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θh_le_θb h1)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θh_nonneg.trans hθ.1) (θb_le_pi a) hθ.2
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_left (by linarith)
  have e2 : ∫ θ in θb a..π, max 0 (1 - (cc + RR * cos θ) - a)
      = ∫ θ in θb a..π, (1 - (cc + RR * cos θ) - a) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θb_le_pi a)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θb_nonneg a) hθ.2 hθ.1
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_right (by linarith)
  rw [e1, e2, integral_lin', integral_zero, sin_pi]
  ring

/-! ### The two halves of the integral -/

lemma eStar_left {θ : ℝ} (hθ : θ ∈ Set.uIcc 0 θh) :
    eStar (cc + RR * cos θ) = gE (cc + RR * cos θ) := by
  rw [Set.uIcc_of_le θh_nonneg] at hθ
  have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 θh_le_pi hθ.2
  rw [cos_θh] at h
  have hR := RR_ne
  have hcR : RR * ((1 / 2 - cc) / RR) = 1 / 2 - cc := by field_simp
  have h' := mul_le_mul_of_nonneg_left h RR_pos.le
  rw [hcR] at h'
  exact eStar_of_half_le (by linarith)

lemma eStar_right {θ : ℝ} (hθ : θ ∈ Set.uIcc θh π) :
    eStar (cc + RR * cos θ) = 1 / 2 - (cc + RR * cos θ) + gE (1 - (cc + RR * cos θ)) := by
  rw [Set.uIcc_of_le θh_le_pi] at hθ
  have h := cos_le_cos_of_nonneg_of_le_pi θh_nonneg hθ.2 hθ.1
  rw [cos_θh] at h
  have hR := RR_ne
  have hcR : RR * ((1 / 2 - cc) / RR) = 1 / 2 - cc := by field_simp
  have h' := mul_le_mul_of_nonneg_left h RR_pos.le
  rw [hcR] at h'
  exact eStar_of_le_half (by linarith)

lemma integral_left :
    ∫ θ in (0 : ℝ)..θh, gE (cc + RR * cos θ)
      = 27 / 164 * θh + s0 * ((cc - 1 / 2) * θh + RR * sin θh)
        + (s1 - s0) * ((cc - 5 / 7) * θa (5 / 7) + RR * sin (θa (5 / 7)))
        + (s2 - s1) * ((cc - 5 / 6) * θa (5 / 6) + RR * sin (θa (5 / 6)))
        + (s3 - s2) * ((cc - 28 / 31) * θa (28 / 31) + RR * sin (θa (28 / 31)))
        + (s4 - s3) * ((cc - 17 / 18) * θa (17 / 18) + RR * sin (θa (17 / 18)))
        + (s5 - s4) * ((cc - 123 / 127) * θa (123 / 127) + RR * sin (θa (123 / 127)))
        + (s6 - s5) * ((cc - 167 / 170) * θa (167 / 170) + RR * sin (θa (167 / 170)))
        + (0 - s6) * ((cc - 1) * θa 1 + RR * sin (θa 1)) := by
  simp only [gE]
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_add, integral_add]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_lin, int_max_a (a := 5 / 7) (by norm_num) (by norm_num),
      int_max_a (a := 5 / 6) (by norm_num) (by norm_num),
      int_max_a (a := 28 / 31) (by norm_num) (by norm_num),
      int_max_a (a := 17 / 18) (by norm_num) (by norm_num),
      int_max_a (a := 123 / 127) (by norm_num) (by norm_num),
      int_max_a (a := 167 / 170) (by norm_num) (by norm_num),
      int_max_a (a := 1) (by norm_num) (by norm_num), sin_zero]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma integral_right :
    ∫ θ in θh..π, (1 / 2 - (cc + RR * cos θ) + gE (1 - (cc + RR * cos θ)))
      = (1 / 2 - cc) * (π - θh) + RR * sin θh
        + (27 / 164 * (π - θh) + s0 * ((1 / 2 - cc) * (π - θh) + RR * sin θh)
        + (s1 - s0) * ((1 - cc - 5 / 7) * (π - θb (5 / 7)) + RR * sin (θb (5 / 7)))
        + (s2 - s1) * ((1 - cc - 5 / 6) * (π - θb (5 / 6)) + RR * sin (θb (5 / 6)))
        + (s3 - s2) * ((1 - cc - 28 / 31) * (π - θb (28 / 31)) + RR * sin (θb (28 / 31)))
        + (s4 - s3) * ((1 - cc - 17 / 18) * (π - θb (17 / 18)) + RR * sin (θb (17 / 18)))
        + (s5 - s4) * ((1 - cc - 123 / 127) * (π - θb (123 / 127)) + RR * sin (θb (123 / 127)))
        + (s6 - s5) * ((1 - cc - 167 / 170) * (π - θb (167 / 170)) + RR * sin (θb (167 / 170)))
        + (0 - s6) * ((1 - cc - 1) * (π - θb 1) + RR * sin (θb 1))) := by
  simp only [gE]
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_add, integral_add, integral_add]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_half, integral_lin', int_max_b (a := 5 / 7) (by norm_num) (by norm_num),
      int_max_b (a := 5 / 6) (by norm_num) (by norm_num),
      int_max_b (a := 28 / 31) (by norm_num) (by norm_num),
      int_max_b (a := 17 / 18) (by norm_num) (by norm_num),
      int_max_b (a := 123 / 127) (by norm_num) (by norm_num),
      int_max_b (a := 167 / 170) (by norm_num) (by norm_num),
      int_max_b (a := 1) (by norm_num) (by norm_num), sin_pi]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- `∫₀^π 𝔢_E^*(c + R cos θ) dθ` in closed form. -/
theorem integral_eStar_eq :
    ∫ θ in (0 : ℝ)..π, eStar (cc + RR * cos θ)
      = (27 / 164 * θh + s0 * ((cc - 1 / 2) * θh + RR * sin θh)
        + (s1 - s0) * ((cc - 5 / 7) * θa (5 / 7) + RR * sin (θa (5 / 7)))
        + (s2 - s1) * ((cc - 5 / 6) * θa (5 / 6) + RR * sin (θa (5 / 6)))
        + (s3 - s2) * ((cc - 28 / 31) * θa (28 / 31) + RR * sin (θa (28 / 31)))
        + (s4 - s3) * ((cc - 17 / 18) * θa (17 / 18) + RR * sin (θa (17 / 18)))
        + (s5 - s4) * ((cc - 123 / 127) * θa (123 / 127) + RR * sin (θa (123 / 127)))
        + (s6 - s5) * ((cc - 167 / 170) * θa (167 / 170) + RR * sin (θa (167 / 170)))
        + (0 - s6) * ((cc - 1) * θa 1 + RR * sin (θa 1)))
      + ((1 / 2 - cc) * (π - θh) + RR * sin θh
        + (27 / 164 * (π - θh) + s0 * ((1 / 2 - cc) * (π - θh) + RR * sin θh)
        + (s1 - s0) * ((1 - cc - 5 / 7) * (π - θb (5 / 7)) + RR * sin (θb (5 / 7)))
        + (s2 - s1) * ((1 - cc - 5 / 6) * (π - θb (5 / 6)) + RR * sin (θb (5 / 6)))
        + (s3 - s2) * ((1 - cc - 28 / 31) * (π - θb (28 / 31)) + RR * sin (θb (28 / 31)))
        + (s4 - s3) * ((1 - cc - 17 / 18) * (π - θb (17 / 18)) + RR * sin (θb (17 / 18)))
        + (s5 - s4) * ((1 - cc - 123 / 127) * (π - θb (123 / 127)) + RR * sin (θb (123 / 127)))
        + (s6 - s5) * ((1 - cc - 167 / 170) * (π - θb (167 / 170)) + RR * sin (θb (167 / 170)))
        + (0 - s6) * ((1 - cc - 1) * (π - θb 1) + RR * sin (θb 1)))) := by
  have hI : ∀ α β : ℝ, IntervalIntegrable (fun θ => eStar (cc + RR * cos θ)) MeasureTheory.volume α β :=
    fun α β => (eStar_continuous.comp (by fun_prop)).intervalIntegrable α β
  rw [← integral_add_adjacent_intervals (hI 0 θh) (hI θh π),
    integral_congr (fun θ hθ => eStar_left hθ), integral_congr (fun θ hθ => eStar_right hθ),
    integral_left, integral_right]

/-! ### The atoms: `θa a = π/2 + arcsin ((c - a)/R)`, `θb a = π/2 + arcsin ((c + a - 1)/R)`, and the sines -/

lemma θa_eq (a : ℝ) : θa a = π / 2 + arcsin ((cc - a) / RR) := by
  unfold θa
  rw [show (a - cc) / RR = -((cc - a) / RR) by ring, arccos_neg, arccos_eq_pi_div_two_sub_arcsin]
  ring

lemma θb_eq (a : ℝ) : θb a = π / 2 + arcsin ((cc + a - 1) / RR) := by
  unfold θb
  rw [show (1 - a - cc) / RR = -((cc + a - 1) / RR) by ring, arccos_neg,
    arccos_eq_pi_div_two_sub_arcsin]
  ring

lemma sin_θa (a : ℝ) : sin (θa a) = Real.sqrt (1 - ((a - cc) / RR) ^ 2) := by
  unfold θa; exact sin_arccos _

lemma sin_θb (a : ℝ) : sin (θb a) = Real.sqrt (1 - ((1 - a - cc) / RR) ^ 2) := by
  unfold θb; exact sin_arccos _

lemma θh_eq : θh = π / 2 + arcsin ((cc - 1 / 2) / RR) := θa_eq _
lemma sin_θh : sin θh = Real.sqrt (1 - ((1 / 2 - cc) / RR) ^ 2) := sin_θa _

/-- `𝔡 = log (R/(c - 1/2)) ≥ 0.6931471803 + 10⁻⁶/1.000005`. -/
lemma dd_ge : (0.6931471803 : ℝ) + (1 - 1000004 / 1000005) ≤ dd := by
  unfold dd cc RR
  have e : (1.000005 : ℝ) / (1.000002 - 1 / 2) = 2 * (1000005 / 1000004) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num)]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1000005 / 1000004 by norm_num)
  rw [inv_div] at h2
  linarith

/-! ### Rational bounds for the 15 arcsines and the 15 square roots (12 decimals) -/

lemma atom0 : (0.523598198251 : ℝ) ≤ Real.arcsin ((1.000002 - 1/2) / 1.000005) ∧ Real.arcsin ((1.000002 - 1/2) / 1.000005) ≤ 0.523598198252 := by
  have hy : (((1.000002 - 1/2) / 1.000005) : ℝ) = 500002 / 1000005 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.523598198251) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.523598198251 i
        ≤ 500002 / 1000005 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.523598198252) (by norm_num) (by norm_num) 6
    have hs : (500002 : ℝ) / 1000005
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.523598198252 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom1 : (0.866025692457 : ℝ) ≤ Real.sqrt (1 - ((1/2 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1/2 - 1.000002) / 1.000005) ^ 2) ≤ 0.866025692458 := by
  have hw : ((1 - ((1/2 - 1.000002) / 1.000005) ^ 2) : ℝ) = 750008000021 / 1000010000025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom2 : (0.289752297717 : ℝ) ≤ Real.arcsin ((1.000002 - 5/7) / 1.000005) ∧ Real.arcsin ((1.000002 - 5/7) / 1.000005) ≤ 0.289752297718 := by
  have hy : (((1.000002 - 5/7) / 1.000005) : ℝ) = 2000014 / 7000035 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.289752297717) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.289752297717 i
        ≤ 2000014 / 7000035 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.289752297718) (by norm_num) (by norm_num) 6
    have hs : (2000014 : ℝ) / 7000035
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.289752297718 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom3 : (0.958314677133 : ℝ) ≤ Real.sqrt (1 - ((5/7 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((5/7 - 1.000002) / 1.000005) ^ 2) ≤ 0.958314677134 := by
  have hw : ((1 - ((5/7 - 1.000002) / 1.000005) ^ 2) : ℝ) = 45000434001029 / 49000490001225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom4 : (0.167449262429 : ℝ) ≤ Real.arcsin ((1.000002 - 5/6) / 1.000005) ∧ Real.arcsin ((1.000002 - 5/6) / 1.000005) ≤ 0.16744926243 := by
  have hy : (((1.000002 - 5/6) / 1.000005) : ℝ) = 500006 / 3000015 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.167449262429) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.167449262429 i
        ≤ 500006 / 3000015 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.16744926243) (by norm_num) (by norm_num) 6
    have hs : (500006 : ℝ) / 3000015
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.16744926243 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom5 : (0.98601309998 : ℝ) ≤ Real.sqrt (1 - ((5/6 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((5/6 - 1.000002) / 1.000005) ^ 2) ≤ 0.986013099981 := by
  have hw : ((1 - ((5/6 - 1.000002) / 1.000005) ^ 2) : ℝ) = 8750084000189 / 9000090000225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom6 : (0.096927409311 : ℝ) ≤ Real.arcsin ((1.000002 - 28/31) / 1.000005) ∧ Real.arcsin ((1.000002 - 28/31) / 1.000005) ≤ 0.096927409312 := by
  have hy : (((1.000002 - 28/31) / 1.000005) : ℝ) = 3000062 / 31000155 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.096927409311) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.096927409311 i
        ≤ 3000062 / 31000155 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.096927409312) (by norm_num) (by norm_num) 6
    have hs : (3000062 : ℝ) / 31000155
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.096927409312 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom7 : (0.995306215201 : ℝ) ≤ Real.sqrt (1 - ((28/31 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((28/31 - 1.000002) / 1.000005) ^ 2) ≤ 0.995306215202 := by
  have hw : ((1 - ((28/31 - 1.000002) / 1.000005) ^ 2) : ℝ) = 952009238020181 / 961009610024025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom8 : (0.055585898158 : ℝ) ≤ Real.arcsin ((1.000002 - 17/18) / 1.000005) ∧ Real.arcsin ((1.000002 - 17/18) / 1.000005) ≤ 0.055585898159 := by
  have hy : (((1.000002 - 17/18) / 1.000005) : ℝ) = 500018 / 9000045 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.055585898158) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.055585898158 i
        ≤ 500018 / 9000045 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.055585898159) (by norm_num) (by norm_num) 6
    have hs : (500018 : ℝ) / 9000045
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.055585898159 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom9 : (0.998455501705 : ℝ) ≤ Real.sqrt (1 - ((17/18 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((17/18 - 1.000002) / 1.000005) ^ 2) ≤ 0.998455501706 := by
  have hw : ((1 - ((17/18 - 1.000002) / 1.000005) ^ 2) : ℝ) = 80750792001701 / 81000810002025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom10 : (0.031503116102 : ℝ) ≤ Real.arcsin ((1.000002 - 123/127) / 1.000005) ∧ Real.arcsin ((1.000002 - 123/127) / 1.000005) ≤ 0.031503116103 := by
  have hy : (((1.000002 - 123/127) / 1.000005) : ℝ) = 1333418 / 42333545 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.031503116102) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.031503116102 i
        ≤ 1333418 / 42333545 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.031503116103) (by norm_num) (by norm_num) 6
    have hs : (1333418 : ℝ) / 42333545
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.031503116103 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom11 : (0.999503817876 : ℝ) ≤ Real.sqrt (1 - ((123/127 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((123/127 - 1.000002) / 1.000005) ^ 2) ≤ 0.999503817877 := by
  have hw : ((1 - ((123/127 - 1.000002) / 1.000005) ^ 2) : ℝ) = 1790351028704301 / 1792129032267025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom12 : (0.017649886942 : ℝ) ≤ Real.arcsin ((1.000002 - 167/170) / 1.000005) ∧ Real.arcsin ((1.000002 - 167/170) / 1.000005) ≤ 0.017649886943 := by
  have hy : (((1.000002 - 167/170) / 1.000005) : ℝ) = 300034 / 17000085 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.017649886942) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.017649886942 i
        ≤ 300034 / 17000085 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.017649886943) (by norm_num) (by norm_num) 6
    have hs : (300034 : ℝ) / 17000085
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.017649886943 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom13 : (0.999844244788 : ℝ) ≤ Real.sqrt (1 - ((167/170 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((167/170 - 1.000002) / 1.000005) ^ 2) ≤ 0.999844244789 := by
  have hw : ((1 - ((167/170 - 1.000002) / 1.000005) ^ 2) : ℝ) = 288912869606069 / 289002890007225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom14 : (0.00000199999 : ℝ) ≤ Real.arcsin ((1.000002 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 - 1) / 1.000005) ≤ 0.000001999991 := by
  have hy : (((1.000002 - 1) / 1.000005) : ℝ) = 2 / 1000005 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.00000199999) (by norm_num) (by norm_num) 6
    have hs : ∑ i ∈ Finset.range (2 * 6 + 1), (-1 : ℝ) ^ i * sinTerm 0.00000199999 i
        ≤ 2 / 1000005 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.000001999991) (by norm_num) (by norm_num) 6
    have hs : (2 : ℝ) / 1000005
        ≤ ∑ i ∈ Finset.range (2 * 6), (-1 : ℝ) ^ i * sinTerm 0.000001999991 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom15 : (0.999999999998 : ℝ) ≤ Real.sqrt (1 - ((1 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 1.000002) / 1.000005) ^ 2) ≤ 0.999999999999 := by
  have hw : ((1 - ((1 - 1.000002) / 1.000005) ^ 2) : ℝ) = 1000010000021 / 1000010000025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom16 : (0.795600708132 : ℝ) ≤ Real.arcsin ((1.000002 + 5/7 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 5/7 - 1) / 1.000005) ≤ 0.795600708133 := by
  have hy : (((1.000002 + 5/7 - 1) / 1.000005) : ℝ) = 5000014 / 7000035 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.795600708132) (by norm_num) (by norm_num) 8
    have hs : ∑ i ∈ Finset.range (2 * 8 + 1), (-1 : ℝ) ^ i * sinTerm 0.795600708132 i
        ≤ 5000014 / 7000035 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.795600708133) (by norm_num) (by norm_num) 8
    have hs : (5000014 : ℝ) / 7000035
        ≤ ∑ i ∈ Finset.range (2 * 8), (-1 : ℝ) ^ i * sinTerm 0.795600708133 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom17 : (0.699855816044 : ℝ) ≤ Real.sqrt (1 - ((1 - 5/7 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 5/7 - 1.000002) / 1.000005) ^ 2) ≤ 0.699855816045 := by
  have hw : ((1 - ((1 - 5/7 - 1.000002) / 1.000005) ^ 2) : ℝ) = 24000350001029 / 49000490001225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom18 : (0.985106863721 : ℝ) ≤ Real.arcsin ((1.000002 + 5/6 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 5/6 - 1) / 1.000005) ≤ 0.985106863722 := by
  have hy : (((1.000002 + 5/6 - 1) / 1.000005) : ℝ) = 2500006 / 3000015 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 0.985106863721) (by norm_num) (by norm_num) 8
    have hs : ∑ i ∈ Finset.range (2 * 8 + 1), (-1 : ℝ) ^ i * sinTerm 0.985106863721 i
        ≤ 2500006 / 3000015 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 0.985106863722) (by norm_num) (by norm_num) 8
    have hs : (2500006 : ℝ) / 3000015
        ≤ ∑ i ∈ Finset.range (2 * 8), (-1 : ℝ) ^ i * sinTerm 0.985106863722 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom19 : (0.552774064735 : ℝ) ≤ Real.sqrt (1 - ((1 - 5/6 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 5/6 - 1.000002) / 1.000005) ^ 2) ≤ 0.552774064736 := by
  have hw : ((1 - ((1 - 5/6 - 1.000002) / 1.000005) ^ 2) : ℝ) = 2750060000189 / 9000090000225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom20 : (1.127221650905 : ℝ) ≤ Real.arcsin ((1.000002 + 28/31 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 28/31 - 1) / 1.000005) ≤ 1.127221650906 := by
  have hy : (((1.000002 + 28/31 - 1) / 1.000005) : ℝ) = 9333354 / 10333385 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 1.127221650905) (by norm_num) (by norm_num) 10
    have hs : ∑ i ∈ Finset.range (2 * 10 + 1), (-1 : ℝ) ^ i * sinTerm 1.127221650905 i
        ≤ 9333354 / 10333385 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 1.127221650906) (by norm_num) (by norm_num) 10
    have hs : (9333354 : ℝ) / 10333385
        ≤ ∑ i ∈ Finset.range (2 * 10), (-1 : ℝ) ^ i * sinTerm 1.127221650906 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom21 : (0.429170930744 : ℝ) ≤ Real.sqrt (1 - ((1 - 28/31 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 28/31 - 1.000002) / 1.000005) ^ 2) ≤ 0.429170930745 := by
  have hw : ((1 - ((1 - 28/31 - 1.000002) / 1.000005) ^ 2) : ℝ) = 19667348668909 / 106778845558225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom22 : (1.235891885983 : ℝ) ≤ Real.arcsin ((1.000002 + 17/18 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 17/18 - 1) / 1.000005) ≤ 1.235891885984 := by
  have hy : (((1.000002 + 17/18 - 1) / 1.000005) : ℝ) = 8500018 / 9000045 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 1.235891885983) (by norm_num) (by norm_num) 10
    have hs : ∑ i ∈ Finset.range (2 * 10 + 1), (-1 : ℝ) ^ i * sinTerm 1.235891885983 i
        ≤ 8500018 / 9000045 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 1.235891885984) (by norm_num) (by norm_num) 10
    have hs : (8500018 : ℝ) / 9000045
        ≤ ∑ i ∈ Finset.range (2 * 10), (-1 : ℝ) ^ i * sinTerm 1.235891885984 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom23 : (0.328678921289 : ℝ) ≤ Real.sqrt (1 - ((1 - 17/18 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 17/18 - 1.000002) / 1.000005) ^ 2) ≤ 0.32867892129 := by
  have hw : ((1 - ((1 - 17/18 - 1.000002) / 1.000005) ^ 2) : ℝ) = 8750504001701 / 81000810002025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom24 : (1.31913913046 : ℝ) ≤ Real.arcsin ((1.000002 + 123/127 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 123/127 - 1) / 1.000005) ≤ 1.319139130461 := by
  have hy : (((1.000002 + 123/127 - 1) / 1.000005) : ℝ) = 123000254 / 127000635 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 1.31913913046) (by norm_num) (by norm_num) 10
    have hs : ∑ i ∈ Finset.range (2 * 10 + 1), (-1 : ℝ) ^ i * sinTerm 1.31913913046 i
        ≤ 123000254 / 127000635 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 1.319139130461) (by norm_num) (by norm_num) 10
    have hs : (123000254 : ℝ) / 127000635
        ≤ ∑ i ∈ Finset.range (2 * 10), (-1 : ℝ) ^ i * sinTerm 1.319139130461 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom25 : (0.24900929691 : ℝ) ≤ Real.sqrt (1 - ((1 - 123/127 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 123/127 - 1.000002) / 1.000005) ^ 2) ≤ 0.249009296911 := by
  have hw : ((1 - ((1 - 123/127 - 1.000002) / 1.000005) ^ 2) : ℝ) = 1000098806338709 / 16129161290403225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom26 : (1.382636094103 : ℝ) ≤ Real.arcsin ((1.000002 + 167/170 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 167/170 - 1) / 1.000005) ≤ 1.382636094104 := by
  have hy : (((1.000002 + 167/170 - 1) / 1.000005) : ℝ) = 5566678 / 5666695 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 1.382636094103) (by norm_num) (by norm_num) 10
    have hs : ∑ i ∈ Finset.range (2 * 10 + 1), (-1 : ℝ) ^ i * sinTerm 1.382636094103 i
        ≤ 5566678 / 5666695 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 1.382636094104) (by norm_num) (by norm_num) 10
    have hs : (5566678 : ℝ) / 5666695
        ≤ ∑ i ∈ Finset.range (2 * 10), (-1 : ℝ) ^ i * sinTerm 1.382636094104 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom27 : (0.187051917087 : ℝ) ≤ Real.sqrt (1 - ((1 - 167/170 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 167/170 - 1.000002) / 1.000005) ^ 2) ≤ 0.187051917088 := by
  have hw : ((1 - ((1 - 167/170 - 1.000002) / 1.000005) ^ 2) : ℝ) = 1123528267341 / 32111432223025 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩

lemma atom28 : (1.568346842563 : ℝ) ≤ Real.arcsin ((1.000002 + 1 - 1) / 1.000005) ∧ Real.arcsin ((1.000002 + 1 - 1) / 1.000005) ≤ 1.568346842564 := by
  have hy : (((1.000002 + 1 - 1) / 1.000005) : ℝ) = 333334 / 333335 := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := 1.568346842563) (by norm_num) (by norm_num) 10
    have hs : ∑ i ∈ Finset.range (2 * 10 + 1), (-1 : ℝ) ^ i * sinTerm 1.568346842563 i
        ≤ 333334 / 333335 := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := 1.568346842564) (by norm_num) (by norm_num) 10
    have hs : (333334 : ℝ) / 333335
        ≤ ∑ i ∈ Finset.range (2 * 10), (-1 : ℝ) ^ i * sinTerm 1.568346842564 i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith

lemma atom29 : (0.002449481781 : ℝ) ≤ Real.sqrt (1 - ((1 - 1 - 1.000002) / 1.000005) ^ 2) ∧ Real.sqrt (1 - ((1 - 1 - 1.000002) / 1.000005) ^ 2) ≤ 0.002449481782 := by
  have hw : ((1 - ((1 - 1 - 1.000002) / 1.000005) ^ 2) : ℝ) = 666669 / 111112222225 := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩


/-- **Numerical input of Theorem 1.3**: `C₁ ≤ 0.0978293`. -/
theorem C1_le :
    (∫ θ in (0 : ℝ)..π, eStar (cc + RR * cos θ)) / (2 * π * dd) ≤ 0.0978293 := by
  rw [integral_eStar_eq, sin_θh, θh_eq]
  simp only [sin_θa, sin_θb]
  simp only [θa_eq, θb_eq]
  have hdd := dd_ge
  have hd0 := dd_pos
  rw [div_le_iff₀ (mul_pos (mul_pos two_pos Real.pi_pos) hd0)]
  have hπ1 := Real.pi_gt_d20
  have hπ2 := Real.pi_lt_d20
  have hpd : (3.14159265358979323846 : ℝ) * ((0.6931471803 : ℝ) + (1 - 1000004 / 1000005))
      ≤ π * dd := mul_le_mul hπ1.le hdd (by norm_num) (by linarith)
  simp only [cc, RR, s0, s1, s2, s3, s4, s5, s6, sl]
  obtain ⟨l0, u0⟩ := atom0

  obtain ⟨l1, u1⟩ := atom1
  obtain ⟨l2, u2⟩ := atom2
  obtain ⟨l3, u3⟩ := atom3
  obtain ⟨l4, u4⟩ := atom4
  obtain ⟨l5, u5⟩ := atom5
  obtain ⟨l6, u6⟩ := atom6
  obtain ⟨l7, u7⟩ := atom7
  obtain ⟨l8, u8⟩ := atom8
  obtain ⟨l9, u9⟩ := atom9
  obtain ⟨l10, u10⟩ := atom10
  obtain ⟨l11, u11⟩ := atom11
  obtain ⟨l12, u12⟩ := atom12
  obtain ⟨l13, u13⟩ := atom13
  obtain ⟨l14, u14⟩ := atom14
  obtain ⟨l15, u15⟩ := atom15
  obtain ⟨l16, u16⟩ := atom16
  obtain ⟨l17, u17⟩ := atom17
  obtain ⟨l18, u18⟩ := atom18
  obtain ⟨l19, u19⟩ := atom19
  obtain ⟨l20, u20⟩ := atom20
  obtain ⟨l21, u21⟩ := atom21
  obtain ⟨l22, u22⟩ := atom22
  obtain ⟨l23, u23⟩ := atom23
  obtain ⟨l24, u24⟩ := atom24
  obtain ⟨l25, u25⟩ := atom25
  obtain ⟨l26, u26⟩ := atom26
  obtain ⟨l27, u27⟩ := atom27
  obtain ⟨l28, u28⟩ := atom28
  obtain ⟨l29, u29⟩ := atom29
  linarith [hpd]


/-- **Theorem 1.3** with all numerical inputs proved: only the literature inputs remain. -/
theorem theorem_1_3_numeric (S : ℝ → ℝ)
    (I : ExplicitInputs) (chi : ℂ → ℂ)
    (hFE : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      riemannZeta (sp σ t) = chi (sp σ t) * riemannZeta (1 - sp σ t))
    (hchi : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      ‖chi (sp σ t)‖ ≤ 1.0070 * (t / (2 * Real.pi)) ^ (1/2 - σ))
    (Z : ℝ → ℕ → ℝ) (A0 D1 D2 E : ℝ → ℝ)
    (hA : ∀ T, 100 ≤ T → ∀ Ψ : ℝ → ℝ, (∀ θ, Ψ (-θ) = Ψ θ) →
      (∀ n : ℕ, 1 ≤ n → ∀ θ, (1 / (n : ℝ)) * Real.log ‖Backlund.fB T n (Backlund.pt cc RR θ)‖ ≤ Ψ θ) →
      ∃ nm : ℕ → ℕ, StrictMono nm ∧ ∀ ε > 0, ∃ M, ∀ m ≥ M,
        Z T (nm m) ≤ Real.log (Thm13.zetaC / (Real.sqrt ((cc - 1) ^ 2 + T ^ 2) * Thm13.zeta2C))
          + (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Ψ θ) + ε)
    (hB : ∀ T, 100 ≤ T → ∀ n : ℕ, 1 ≤ n → |D2 T| ≤ Real.pi * Z T n / (2 * dd) + E T / 2
      + 3 * Real.pi / (2 * n) + Real.pi / 4)
    (hEc : ∀ T, 100 ≤ T → E T / Real.pi ≤ (640 * delS - 112) / (1536 * (3 * T - 1)) + 1 / 1024)
    (hdec : ∀ T, 100 ≤ T → Real.pi * S T = A0 T + D2 T - D1 T)
    (hA0 : ∀ T, 100 ≤ T → |A0 T| ≤ Real.log Thm13.zetaS)
    (hD1 : ∀ T, 100 ≤ T →
      D1 T = Real.arctan ((cc + (cc - 1 / 2) ^ 2 / RR - 1) / T) + Real.arctan (1 / (2 * T)))
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 :=
  Thm13.theorem_1_3_zeta S I chi hFE hchi Z A0 D1 D2 E hA hB hEc hdec hA0 hD1 C1_le hplatt

end RvmClock.C1
