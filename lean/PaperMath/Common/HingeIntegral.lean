import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Exact integrals of hinge functions of `c + R cos θ` (reusable)

For a profile that is piecewise linear in `σ`, the angular integral `∫₀^π 𝔢^*(c + R cos θ) dθ` of
Backlund's method is a combination of the integrals computed here. With `θ_h = arccos ((1/2 - c)/R)`
(the angle where `σ = c + R cos θ` equals `1/2`), `θ_a = arccos ((a - c)/R)` and
`θ'_a = arccos ((1 - a - c)/R)`, for `1/2 ≤ a ≤ 1`:
* `int_max_a`: `∫₀^{θ_h} max 0 (c + R cos θ - a) dθ = (c - a) θ_a + R sin θ_a`;
* `int_max_b`: `∫_{θ_h}^π max 0 (1 - (c + R cos θ) - a) dθ = (1 - c - a)(π - θ'_a) + R sin θ'_a`;
* `integral_lin`, `integral_lin'`, `integral_half`: the linear parts;
* `θa_eq`, `θb_eq`, `sin_θa`, `sin_θb`: `θ_a = π/2 + arcsin ((c - a)/R)`, `sin θ_a = √(1 - ((a - c)/R)²)`.

Hypotheses on the disc: `0 < R`, `c - R ≤ 1/2`, `1 ≤ c + R`, `c ≤ R`. The article uses
`(c, R) = (1.000002, 1.000005)` (Theorem 1.3, `Papers/RvmClock/C1.lean`, which has its own copy of these
lemmas with the constants fixed) and `(c, R) = (1, 1)` (Corollary 1.2, `Papers/RvmClock/LambdaB.lean`).
-/

open Real intervalIntegral

namespace Common.HingeIntegral

variable (c R : ℝ)

/-- Kink angle of `max 0 (c + R cos θ - a)`. -/
noncomputable def θa (a : ℝ) : ℝ := arccos ((a - c) / R)
/-- Kink angle of `max 0 (1 - (c + R cos θ) - a)`. -/
noncomputable def θb (a : ℝ) : ℝ := arccos ((1 - a - c) / R)
/-- `θ_h = θa (1/2)`: the angle where `σ = 1/2`. -/
noncomputable def θh : ℝ := θa c R (1 / 2)

variable {c R}

section disc
variable (hR : 0 < R)
include hR

lemma xa_mem (h1 : c - R ≤ 1 / 2) (h2 : 1 ≤ c + R) {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) :
    -1 ≤ (a - c) / R ∧ (a - c) / R ≤ 1 := by
  constructor
  · rw [le_div_iff₀ hR]; linarith
  · rw [div_le_iff₀ hR]; linarith

lemma xb_mem (h2 : 1 ≤ c + R) (h3 : c ≤ R) {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) :
    -1 ≤ (1 - a - c) / R ∧ (1 - a - c) / R ≤ 1 := by
  constructor
  · rw [le_div_iff₀ hR]; linarith
  · rw [div_le_iff₀ hR]; linarith

lemma cos_θa (h1 : c - R ≤ 1 / 2) (h2 : 1 ≤ c + R) {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) :
    cos (θa c R a) = (a - c) / R :=
  cos_arccos (xa_mem hR h1 h2 ha1 ha2).1 (xa_mem hR h1 h2 ha1 ha2).2

lemma cos_θb (h2 : 1 ≤ c + R) (h3 : c ≤ R) {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 1) :
    cos (θb c R a) = (1 - a - c) / R :=
  cos_arccos (xb_mem hR h2 h3 ha1 ha2).1 (xb_mem hR h2 h3 ha1 ha2).2

lemma θa_le_θh {a : ℝ} (ha1 : 1 / 2 ≤ a) : θa c R a ≤ θh c R := by
  unfold θh θa
  apply arccos_le_arccos
  exact div_le_div_of_nonneg_right (by linarith) hR.le

lemma θh_le_θb {a : ℝ} (ha1 : 1 / 2 ≤ a) : θh c R ≤ θb c R a := by
  unfold θh θa θb
  apply arccos_le_arccos
  exact div_le_div_of_nonneg_right (by linarith) hR.le

end disc

lemma θa_nonneg (a : ℝ) : 0 ≤ θa c R a := arccos_nonneg _
lemma θa_le_pi (a : ℝ) : θa c R a ≤ π := arccos_le_pi _
lemma θb_nonneg (a : ℝ) : 0 ≤ θb c R a := arccos_nonneg _
lemma θb_le_pi (a : ℝ) : θb c R a ≤ π := arccos_le_pi _
lemma θh_nonneg : 0 ≤ θh c R := θa_nonneg _
lemma θh_le_pi : θh c R ≤ π := θa_le_pi _

lemma cos_θh (hR : 0 < R) (h1 : c - R ≤ 1 / 2) (h2 : 1 ≤ c + R) :
    cos (θh c R) = (1 / 2 - c) / R :=
  cos_θa hR h1 h2 (by norm_num) (by norm_num)

/-! ### Elementary integrals -/

lemma integral_lin (c R a α β : ℝ) :
    ∫ θ in α..β, (c + R * cos θ - a) = (c - a) * (β - α) + R * (sin β - sin α) := by
  have e : (fun θ => c + R * cos θ - a) = fun θ => (c - a) + R * cos θ := by funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => R * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

lemma integral_lin' (c R a α β : ℝ) :
    ∫ θ in α..β, (1 - (c + R * cos θ) - a) = (1 - c - a) * (β - α) - R * (sin β - sin α) := by
  have e : (fun θ => 1 - (c + R * cos θ) - a) = fun θ => (1 - c - a) + (-R) * cos θ := by
    funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -R * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

lemma integral_half (c R α β : ℝ) :
    ∫ θ in α..β, (1 / 2 - (c + R * cos θ)) = (1 / 2 - c) * (β - α) - R * (sin β - sin α) := by
  have e : (fun θ => 1 / 2 - (c + R * cos θ)) = fun θ => (1 / 2 - c) + (-R) * cos θ := by
    funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -R * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

/-- `∫₀^{θ_h} max 0 (c + R cos θ - a) = (c - a) θ_a + R sin θ_a` for `1/2 ≤ a ≤ 1`. -/
lemma int_max_a (hR : 0 < R) (h1 : c - R ≤ 1 / 2) (h2 : 1 ≤ c + R) {a : ℝ} (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 1) :
    ∫ θ in (0 : ℝ)..θh c R, max 0 (c + R * cos θ - a)
      = (c - a) * θa c R a + R * sin (θa c R a) := by
  have hI : ∀ α β : ℝ,
      IntervalIntegrable (fun θ => max 0 (c + R * cos θ - a)) MeasureTheory.volume α β :=
    fun α β => (continuous_const.max (by fun_prop)).intervalIntegrable α β
  have hRne := hR.ne'
  have hc := cos_θa hR h1 h2 ha1 ha2
  have hcR : R * ((a - c) / R) = a - c := by field_simp
  rw [← integral_add_adjacent_intervals (hI 0 (θa c R a)) (hI (θa c R a) (θh c R))]
  have e1 : ∫ θ in (0 : ℝ)..θa c R a, max 0 (c + R * cos θ - a)
      = ∫ θ in (0 : ℝ)..θa c R a, (c + R * cos θ - a) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θa_nonneg a)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 (θa_le_pi a) hθ.2
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h hR.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_right (by linarith)
  have e2 : ∫ θ in θa c R a..θh c R, max 0 (c + R * cos θ - a)
      = ∫ θ in θa c R a..θh c R, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θa_le_θh hR ha1)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θa_nonneg a) (hθ.2.trans θh_le_pi) hθ.1
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h hR.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_left (by linarith)
  rw [e1, e2, integral_lin, integral_zero, sin_zero]
  ring

/-- `∫_{θ_h}^π max 0 (1 - (c + R cos θ) - a) = (1 - c - a)(π - θ'_a) + R sin θ'_a` for `1/2 ≤ a ≤ 1`. -/
lemma int_max_b (hR : 0 < R) (h2 : 1 ≤ c + R) (h3 : c ≤ R) {a : ℝ} (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 1) :
    ∫ θ in θh c R..π, max 0 (1 - (c + R * cos θ) - a)
      = (1 - c - a) * (π - θb c R a) + R * sin (θb c R a) := by
  have hI : ∀ α β : ℝ,
      IntervalIntegrable (fun θ => max 0 (1 - (c + R * cos θ) - a)) MeasureTheory.volume α β :=
    fun α β => (continuous_const.max (by fun_prop)).intervalIntegrable α β
  have hRne := hR.ne'
  have hc := cos_θb hR h2 h3 ha1 ha2
  have hcR : R * ((1 - a - c) / R) = 1 - a - c := by field_simp
  rw [← integral_add_adjacent_intervals (hI (θh c R) (θb c R a)) (hI (θb c R a) π)]
  have e1 : ∫ θ in θh c R..θb c R a, max 0 (1 - (c + R * cos θ) - a)
      = ∫ θ in θh c R..θb c R a, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θh_le_θb hR ha1)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θh_nonneg.trans hθ.1) (θb_le_pi a) hθ.2
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h hR.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_left (by linarith)
  have e2 : ∫ θ in θb c R a..π, max 0 (1 - (c + R * cos θ) - a)
      = ∫ θ in θb c R a..π, (1 - (c + R * cos θ) - a) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θb_le_pi a)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θb_nonneg a) hθ.2 hθ.1
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h hR.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_right (by linarith)
  rw [e1, e2, integral_lin', integral_zero, sin_pi]
  ring

/-! ### The atoms -/

lemma θa_eq (c R a : ℝ) : θa c R a = π / 2 + arcsin ((c - a) / R) := by
  unfold θa
  rw [show (a - c) / R = -((c - a) / R) by ring, arccos_neg, arccos_eq_pi_div_two_sub_arcsin]
  ring

lemma θb_eq (c R a : ℝ) : θb c R a = π / 2 + arcsin ((c + a - 1) / R) := by
  unfold θb
  rw [show (1 - a - c) / R = -((c + a - 1) / R) by ring, arccos_neg,
    arccos_eq_pi_div_two_sub_arcsin]
  ring

lemma sin_θa (c R a : ℝ) : sin (θa c R a) = Real.sqrt (1 - ((a - c) / R) ^ 2) := by
  unfold θa; exact sin_arccos _

lemma sin_θb (c R a : ℝ) : sin (θb c R a) = Real.sqrt (1 - ((1 - a - c) / R) ^ 2) := by
  unfold θb; exact sin_arccos _

lemma θh_eq (c R : ℝ) : θh c R = π / 2 + arcsin ((c - 1 / 2) / R) := θa_eq _ _ _
lemma sin_θh (c R : ℝ) : sin (θh c R) = Real.sqrt (1 - ((1 / 2 - c) / R) ^ 2) := sin_θa _ _ _

end Common.HingeIntegral
