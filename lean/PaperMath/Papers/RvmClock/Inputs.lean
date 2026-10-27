import PaperMath.Papers.RvmClock.Gaps
import PaperMath.Papers.RvmClock.Construction
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Analytic inputs for Theorem 1.5, stated explicitly

`ZetaInputs` packages: the ordinates `γ` (an `Ordinates`), the Stirling remainder `ϖ` of the
Riemann–Siegel theta function with `|ϖ(t)| ≤ 1/t` (Lemma 4.1 gives `0.53/t`), and
`S := N − N₀ − ϖ/π` (this is the Riemann–von Mangoldt formula (1.1), used as the definition of `S`).

`FujiiB` is Theorem 3.8(b) of the article (Fujii 1974, Main Theorem, p. 225, with the corrections of
Fujii 1981, §5) in the only case used: `k = 2`, `α_F = 1/2`, `H = T`:
  `∫_T^{2T} (S(t+h) − S(t))⁴ dt ≤ A · T · (log (2 + h log T))²`  for `T ≥ T₀`, `0 < h ≤ 1`.
-/

open MeasureTheory Set Real

namespace RvmClock

structure ZetaInputs extends Ordinates where
  varpi : ℝ → ℝ
  varpi_meas : Measurable varpi
  varpi_bound : ∀ t : ℝ, 1 ≤ t → |varpi t| ≤ 1 / t

namespace ZetaInputs

variable (Z : ZetaInputs)

noncomputable def S (t : ℝ) : ℝ := (Z.N t : ℝ) - N0 t - Z.varpi t / π

/-- **Hypothesis (Fujii, Theorem 3.8(b), k = 2, α_F = 1/2, H = T).** -/
def FujiiB : Prop :=
  ∃ A T₀ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₀ ≤ T → ∀ h : ℝ, 0 < h → h ≤ 1 →
    ∫ t in Icc T (2 * T), (Z.S (t + h) - Z.S t) ^ 4 ≤ A * T * (Real.log (2 + h * Real.log T)) ^ 2

lemma N_mono : Monotone Z.N := by
  intro s t hst
  by_contra hc
  push Not at hc
  have := (Z.lt_N_iff s (Z.N t)).mp hc
  have h2 := Z.toOrdinates.lt_N_iff t (Z.N t)
  have : ¬ (Z.N t < Z.N t) := lt_irrefl _
  exact this (h2.mpr (by linarith))

lemma N_measurable : Measurable (fun t => (Z.N t : ℝ)) :=
  (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp Z.N_mono.measurable

lemma S_measurable : Measurable Z.S := by
  unfold S
  have h1 : Measurable N0 := by unfold N0; fun_prop
  exact (Z.N_measurable.sub h1).sub (Z.varpi_meas.div_const _)

end ZetaInputs

namespace ZetaInputs

variable (Z : ZetaInputs)

lemma N_le_of_le {s t : ℝ} (h : s ≤ t) : (Z.N s : ℝ) ≤ Z.N t := by exact_mod_cast Z.N_mono h

/-- `S` is bounded on `[a, b]` for `1 ≤ a`. -/
lemma S_bounded {a b : ℝ} (ha : 1 ≤ a) : ∃ B : ℝ, ∀ t ∈ Icc a b, |Z.S t| ≤ B := by
  have hc : ContinuousOn N0 (Icc a b) := fun t ht => (continuousAt_N0 (by linarith [ht.1])).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨(Z.N b : ℝ) + C + 1, fun t ht => ?_⟩
  unfold S
  have h1 : (Z.N t : ℝ) ≤ Z.N b := Z.N_le_of_le ht.2
  have h2 := hC t ht
  rw [Real.norm_eq_abs] at h2
  have h3 := Z.varpi_bound t (by linarith [ht.1])
  have h4 : |Z.varpi t / π| ≤ 1 := by
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
    have : 1 / t ≤ 1 := by rw [div_le_one (by linarith [ht.1])]; linarith [ht.1]
    linarith [Real.pi_gt_three]
  have h5 : (0 : ℝ) ≤ Z.N t := Nat.cast_nonneg _
  calc |(Z.N t : ℝ) - N0 t - Z.varpi t / π| ≤ |(Z.N t : ℝ)| + |N0 t| + |Z.varpi t / π| := by
        have := abs_sub (((Z.N t : ℝ) - N0 t)) (Z.varpi t / π)
        have := abs_sub ((Z.N t : ℝ)) (N0 t)
        linarith
    _ ≤ (Z.N b : ℝ) + C + 1 := by rw [abs_of_nonneg h5]; linarith

lemma integrableOn_Sdiff4 {a b h : ℝ} (ha : 1 ≤ a) (hh : 0 ≤ h) :
    IntegrableOn (fun t => (Z.S (t + h) - Z.S t) ^ 4) (Icc a b) := by
  obtain ⟨B, hB⟩ := Z.S_bounded (a := a) (b := b + h) ha
  refine IntegrableOn.of_bound (by simp)
    (((Z.S_measurable.comp (measurable_id.add_const h)).sub Z.S_measurable).pow_const 4).aestronglyMeasurable
    ((2 * B) ^ 4) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have h1 := hB (t + h) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 := hB t ⟨ht.1, by linarith [ht.2]⟩
  rw [Real.norm_eq_abs, abs_pow]
  have : |Z.S (t + h) - Z.S t| ≤ 2 * B := by
    have := abs_sub (Z.S (t + h)) (Z.S t); linarith
  exact pow_le_pow_left₀ (abs_nonneg _) this 4

/-- On `𝒜_h`, `|S(t+h) − S(t)| ≥ hL/(4π)` with `L = log(T/2π)`, when `hL ≥ 1` and `T ≥ 4π`. -/
lemma Sdiff_ge_on_A {T h t : ℝ} (hT : 4 * π ≤ T) (hh : 0 < h) (hv : 1 ≤ h * Real.log (T / (2 * π)))
    (ht : t ∈ Z.Aset T h) : h * Real.log (T / (2 * π)) / (4 * π) ≤ |Z.S (t + h) - Z.S t| := by
  obtain ⟨⟨htT, _⟩, hN⟩ := ht
  have hpi := Real.pi_pos
  have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
  have ht0 : 0 < t := by linarith
  have hdiff : Z.S (t + h) - Z.S t = -(N0 (t + h) - N0 t) - (Z.varpi (t + h) - Z.varpi t) / π := by
    unfold S; rw [hN]; ring
  have hN0 := N0_sub_ge ht0 (show t ≤ t + h by linarith)
  have hlog : Real.log (T / (2 * π)) ≤ Real.log (t / (2 * π)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right htT (by positivity))
  have hN0' : h * Real.log (T / (2 * π)) / (2 * π) ≤ N0 (t + h) - N0 t := by
    refine le_trans ?_ hN0
    rw [show t + h - t = h by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hh.le) (by positivity)
  have hv1 := Z.varpi_bound (t + h) (by linarith)
  have hv2 := Z.varpi_bound t (by linarith)
  have hvar : |(Z.varpi (t + h) - Z.varpi t) / π| ≤ 1 / T := by
    rw [abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have a1 : 1 / (t + h) ≤ 1 / T := one_div_le_one_div_of_le (by linarith) (by linarith)
    have a2 : 1 / t ≤ 1 / T := one_div_le_one_div_of_le (by linarith) htT
    have := abs_sub (Z.varpi (t + h)) (Z.varpi t)
    have hT0 : 0 < 1 / T := by positivity
    nlinarith [Real.pi_gt_three]
  have hsmall : 1 / T ≤ h * Real.log (T / (2 * π)) / (4 * π) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith
  rw [hdiff]
  have e : |-(N0 (t + h) - N0 t) - (Z.varpi (t + h) - Z.varpi t) / π|
      ≥ (N0 (t + h) - N0 t) - |(Z.varpi (t + h) - Z.varpi t) / π| := by
    rw [show -(N0 (t + h) - N0 t) - (Z.varpi (t + h) - Z.varpi t) / π
        = -((N0 (t + h) - N0 t) + (Z.varpi (t + h) - Z.varpi t) / π) by ring, abs_neg]
    have := abs_add_le ((N0 (t + h) - N0 t) + (Z.varpi (t + h) - Z.varpi t) / π)
      (-((Z.varpi (t + h) - Z.varpi t) / π))
    rw [abs_neg] at this
    have h' : (N0 (t + h) - N0 t) + (Z.varpi (t + h) - Z.varpi t) / π + -((Z.varpi (t + h) - Z.varpi t) / π)
        = N0 (t + h) - N0 t := by ring
    rw [h'] at this
    have h0 : 0 ≤ N0 (t + h) - N0 t := le_trans (by positivity) hN0'
    rw [abs_of_nonneg h0] at this
    linarith
  have e2 : h * Real.log (T / (2 * π)) / (4 * π) = h * Real.log (T / (2 * π)) / (2 * π) - h * Real.log (T / (2 * π)) / (4 * π) := by
    field_simp; ring
  linarith

end ZetaInputs

namespace ZetaInputs

variable (Z : ZetaInputs)

lemma measurableSet_Aset (T h : ℝ) : MeasurableSet (Z.Aset T h) := by
  have hN : Measurable Z.N := Z.N_mono.measurable
  exact measurableSet_Icc.inter (measurableSet_eq_fun (hN.comp (measurable_id.add_const h)) hN)

lemma log_comp {T h : ℝ} (hT : 1 ≤ T) (hh : 0 < h) (hh1 : h ≤ 1) (hv : 1 ≤ h * Real.log (T / (2 * π)))
    {T' : ℝ} (hT' : T ≤ T') (hT'2 : T' ≤ 2 * T) :
    (Real.log (2 + h * Real.log T')) ^ 2 ≤ 4 * (Real.log (2 + h * Real.log (T / (2 * π)))) ^ 2 := by
  have hpi := Real.pi_pos
  set L := Real.log (T / (2 * π))
  have hlogT' : Real.log T' ≤ L + Real.log 16 := by
    have : Real.log T' ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hT'2
    have e : Real.log (2 * T) = L + Real.log (4 * π) := by
      simp only [L]; rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
      rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    have h16 : Real.log (4 * π) ≤ Real.log 16 := Real.log_le_log (by positivity) (by linarith [Real.pi_lt_four])
    linarith
  have hl16 : Real.log 16 ≤ 2.78 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hlT'0 : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
  have hpos : 0 < 2 + h * Real.log T' := by positivity
  have hb : 2 + h * Real.log T' ≤ (2 + h * L) ^ 2 := by
    have : h * Real.log T' ≤ h * L + 2.78 := by
      have := mul_le_mul_of_nonneg_left hlogT' hh.le
      nlinarith
    nlinarith
  have h1 : Real.log (2 + h * Real.log T') ≤ 2 * Real.log (2 + h * L) := by
    have := Real.log_le_log hpos hb
    rw [Real.log_pow] at this; push_cast at this; linarith
  have h0 : 0 ≤ Real.log (2 + h * Real.log T') := Real.log_nonneg (by nlinarith)
  nlinarith

/-- **Chebyshev + Fujii (b)**: `|𝒜_h| ≤ K · T · log²(2 + hL) / (hL)⁴`. -/
theorem vol_A_le (hF : Z.FujiiB) : ∃ K T₁ : ℝ, 0 ≤ K ∧ ∀ T : ℝ, T₁ ≤ T → ∀ h : ℝ, 0 < h → h ≤ 1 →
    1 ≤ h * Real.log (T / (2 * π)) →
    volume.real (Z.Aset T h) ≤ K * T * (Real.log (2 + h * Real.log (T / (2 * π)))) ^ 2
      / (h * Real.log (T / (2 * π))) ^ 4 := by
  obtain ⟨A, T₀, hA, hFj⟩ := hF
  have hpi := Real.pi_pos
  refine ⟨12 * A * (4 * π) ^ 4, max T₀ (4 * π), by positivity, ?_⟩
  intro T hT h hh hh1 hv
  have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT4 : 4 * π ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
  set L := Real.log (T / (2 * π)) with hL
  set f := fun t => (Z.S (t + h) - Z.S t) ^ 4 with hf
  set c := (h * L / (4 * π)) ^ 4 with hc
  have hAm := Z.measurableSet_Aset T h
  have hAsub : Z.Aset T h ⊆ Icc T (4 * T) := fun t ht => ht.1
  have hAfin : volume (Z.Aset T h) ≠ ⊤ := measure_ne_top_of_subset hAsub (by simp)
  have hint4 := Z.integrableOn_Sdiff4 (a := T) (b := 4 * T) hT1 hh.le
  have hcheb : c * volume.real (Z.Aset T h) ≤ ∫ t in Z.Aset T h, f t := by
    refine setIntegral_ge_of_const_le_real hAm hAfin (fun t ht => ?_) (hint4.mono_set hAsub)
    have := Z.Sdiff_ge_on_A hT4 hh hv ht
    have h1 := pow_le_pow_left₀ (by positivity) this 4
    simp only [hf]
    rw [show (Z.S (t + h) - Z.S t) ^ 4 = |Z.S (t + h) - Z.S t| ^ 4 by
      rw [← abs_pow, abs_of_nonneg (by positivity)]]
    exact h1
  have hmono : ∫ t in Z.Aset T h, f t ≤ ∫ t in Icc T (4 * T), f t :=
    setIntegral_mono_set hint4 (Filter.Eventually.of_forall (fun t => by simp only [hf]; positivity))
      (Filter.Eventually.of_forall hAsub)
  have hsplit : ∫ t in Icc T (4 * T), f t ≤ (∫ t in Icc T (2 * T), f t) + ∫ t in Icc (2 * T) (2 * (2 * T)), f t := by
    have hu : Icc T (4 * T) = Icc T (2 * T) ∪ Ioc (2 * T) (4 * T) := (Set.Icc_union_Ioc_eq_Icc (by linarith) (by linarith)).symm
    have hd : Disjoint (Icc T (2 * T)) (Ioc (2 * T) (4 * T)) := by
      rw [Set.disjoint_left]; intro t h1 h2; linarith [h1.2, h2.1]
    rw [hu, setIntegral_union hd measurableSet_Ioc (hint4.mono_set (by intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩))
      (hint4.mono_set (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩))]
    have h2T : (2 : ℝ) * (2 * T) = 4 * T := by ring
    have : ∫ t in Ioc (2 * T) (4 * T), f t ≤ ∫ t in Icc (2 * T) (2 * (2 * T)), f t := by
      rw [h2T]
      exact setIntegral_mono_set (Z.integrableOn_Sdiff4 (a := 2 * T) (b := 4 * T) (by linarith) hh.le)
        (Filter.Eventually.of_forall (fun t => by simp only [hf]; positivity))
        (Filter.Eventually.of_forall Set.Ioc_subset_Icc_self)
    linarith
  have hF1 := hFj T hT0 h hh hh1
  have hF2 := hFj (2 * T) (by linarith) h hh hh1
  have hl1 := log_comp hT1 hh hh1 hv (le_refl T) (by linarith)
  have hl2 := log_comp hT1 hh hh1 hv (show T ≤ 2 * T by linarith) (le_refl _)
  have htot : c * volume.real (Z.Aset T h) ≤ 12 * A * T * (Real.log (2 + h * L)) ^ 2 := by
    have a1 : A * T * (Real.log (2 + h * Real.log T)) ^ 2 ≤ A * T * (4 * (Real.log (2 + h * L)) ^ 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    have a2 : A * (2 * T) * (Real.log (2 + h * Real.log (2 * T))) ^ 2 ≤ A * (2 * T) * (4 * (Real.log (2 + h * L)) ^ 2) :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    linarith
  have hcpos : 0 < c := by positivity
  have hcval : c = (h * L) ^ 4 / (4 * π) ^ 4 := by simp only [hc]; rw [div_pow]
  rw [le_div_iff₀ (by positivity)]
  have : volume.real (Z.Aset T h) * (h * L) ^ 4 = (4 * π) ^ 4 * (c * volume.real (Z.Aset T h)) := by
    rw [hcval]; field_simp
  rw [this]
  calc (4 * π) ^ 4 * (c * volume.real (Z.Aset T h)) ≤ (4 * π) ^ 4 * (12 * A * T * (Real.log (2 + h * L)) ^ 2) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 12 * A * (4 * π) ^ 4 * T * (Real.log (2 + h * L)) ^ 2 := by ring

end ZetaInputs

namespace ZetaInputs

variable (Z : ZetaInputs)

lemma sum_Ico_D {a b : ℕ} (hab : a ≤ b) : ∑ ℓ ∈ Finset.Ico a b, Z.D ℓ = Z.γ b - Z.γ a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    unfold Ordinates.D; ring

lemma log_two_add_pow_le (j : ℕ) : Real.log (2 + (2 : ℝ) ^ j) ≤ (j : ℝ) + 2 := by
  have h1 : (2 : ℝ) + 2 ^ j ≤ 2 ^ (j + 2) := by
    rw [pow_add]; have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); nlinarith
  calc Real.log (2 + (2 : ℝ) ^ j) ≤ Real.log ((2 : ℝ) ^ (j + 2)) := Real.log_le_log (by positivity) h1
    _ = ((j : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    _ ≤ (j : ℝ) + 2 := by
        have := Real.log_two_lt_d9
        have : (0:ℝ) ≤ (j : ℝ) + 2 := by positivity
        nlinarith

/-- **Lemma 7.5 (third moment of the gaps)**, from Fujii (b) and `D_ℓ ≤ 1` for large `γ_ℓ`:
`Σ_{T < γ_ℓ ≤ 2T} D_ℓ³ ≤ B · T / log²(T/2π)`. -/
theorem gaps_third_moment (hF : Z.FujiiB) (hgap : ∃ G : ℝ, ∀ ℓ, G ≤ Z.γ ℓ → Z.D ℓ ≤ 1) :
    ∃ B T₁ : ℝ, 0 ≤ B ∧ ∀ T : ℝ, T₁ ≤ T →
      ∑ ℓ ∈ Finset.Ico (Z.N T) (Z.N (2 * T)), Z.D ℓ ^ 3 ≤ B * T / (Real.log (T / (2 * π))) ^ 2 := by
  classical
  obtain ⟨K, T₁, hK, hvol⟩ := Z.vol_A_le hF
  obtain ⟨G, hG⟩ := hgap
  have hpi := Real.pi_pos
  refine ⟨8 + 512 * K, max (max T₁ G) (2 * π * Real.exp 1), by positivity, ?_⟩
  intro T hT
  have hT1' : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTG : G ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTe : 2 * π * Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := by nlinarith [Real.exp_one_gt_two, Real.pi_gt_three]
  set L := Real.log (T / (2 * π)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]; linarith
  set Λ := Finset.Ico (Z.N T) (Z.N (2 * T))
  have hΛ : ∀ ℓ ∈ Λ, T < Z.γ ℓ ∧ Z.γ ℓ ≤ 2 * T := by
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hℓ
    refine ⟨?_, (Z.lt_N_iff (2 * T) ℓ).mp h2⟩
    by_contra hc; push Not at hc
    have := (Z.lt_N_iff T ℓ).mpr hc; omega
  have hD1 : ∀ ℓ ∈ Λ, Z.D ℓ ≤ 1 := fun ℓ hℓ => hG ℓ (by linarith [(hΛ ℓ hℓ).1])
  have hD0 : ∀ ℓ ∈ Λ, 0 ≤ Z.D ℓ := fun ℓ _ => Z.D_nonneg ℓ
  have hhyp : ∀ j : ℕ, (2 : ℝ) ^ (j + 1) ≤ L →
      ∑ ℓ ∈ Λ.filter (fun ℓ => (2 : ℝ) ^ (j + 1) / L ≤ Z.D ℓ), Z.D ℓ
        ≤ (2 * K * T) * ((j : ℝ) + 2) ^ 2 / 16 ^ j := by
    intro j hj
    set h := (2 : ℝ) ^ j / L with hh
    have hL0 : 0 < L := by linarith
    have hhpos : 0 < h := by positivity
    have hh1 : h ≤ 1 := by
      rw [hh, div_le_one hL0]; rw [pow_succ] at hj; nlinarith [one_le_pow₀ (M₀ := ℝ) (n := j) (by norm_num : (1:ℝ) ≤ 2)]
    have hhL : h * L = 2 ^ j := by rw [hh]; field_simp
    have hv : 1 ≤ h * L := by rw [hhL]; exact one_le_pow₀ (by norm_num)
    have e2h : 2 * h = (2 : ℝ) ^ (j + 1) / L := by rw [hh, pow_succ]; ring
    have hB := Z.sum_D_le_two_vol hT1 hhpos Λ hΛ hD1
    rw [e2h] at hB
    have hV := hvol T hT1' h hhpos hh1 hv
    rw [hhL] at hV
    have hlog := log_two_add_pow_le j
    have hlog0 : 0 ≤ Real.log (2 + (2 : ℝ) ^ j) := Real.log_nonneg (by have h0 : (0:ℝ) < 2 ^ j := (by positivity); linarith)
    have hsq : (Real.log (2 + (2 : ℝ) ^ j)) ^ 2 ≤ ((j : ℝ) + 2) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
    have e16 : ((2 : ℝ) ^ j) ^ 4 = 16 ^ j := by
      calc ((2 : ℝ) ^ j) ^ 4 = ((2 : ℝ) ^ 4) ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = 16 ^ j := by norm_num
    rw [e16] at hV
    have hV' : volume.real (Z.Aset T h) ≤ K * T * ((j : ℝ) + 2) ^ 2 / 16 ^ j := by
      refine le_trans hV ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    calc ∑ ℓ ∈ Λ.filter (fun ℓ => (2 : ℝ) ^ (j + 1) / L ≤ Z.D ℓ), Z.D ℓ ≤ 2 * volume.real (Z.Aset T h) := hB
      _ ≤ 2 * (K * T * ((j : ℝ) + 2) ^ 2 / 16 ^ j) := by linarith
      _ = (2 * K * T) * ((j : ℝ) + 2) ^ 2 / 16 ^ j := by ring
  have hmain := sum_cube_le Λ Z.D hD0 hD1 hL1 (by positivity) hhyp
  have hsumD : ∑ ℓ ∈ Λ, Z.D ℓ ≤ T + 1 := by
    by_cases hne : Z.N T < Z.N (2 * T)
    · show ∑ ℓ ∈ Finset.Ico (Z.N T) (Z.N (2 * T)), Z.D ℓ ≤ T + 1
      rw [Z.sum_Ico_D hne.le]
      have hlast : Z.N (2 * T) - 1 ∈ Λ := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      have h1 := hD1 _ hlast
      have h2 := (hΛ _ hlast).2
      have h3 : T < Z.γ (Z.N T) := by
        classical
        by_contra hc; push Not at hc
        have := (Z.lt_N_iff T (Z.N T)).mpr hc; omega
      unfold Ordinates.D at h1
      rw [show Z.N (2 * T) - 1 + 1 = Z.N (2 * T) by omega] at h1
      linarith
    · push Not at hne
      have hE : Λ = ∅ := Finset.Ico_eq_empty_of_le hne
      rw [hE, Finset.sum_empty]; linarith
  calc ∑ ℓ ∈ Λ, Z.D ℓ ^ 3 ≤ (4 * ∑ ℓ ∈ Λ, Z.D ℓ + 256 * (2 * K * T)) / L ^ 2 := hmain
    _ ≤ (8 + 512 * K) * T / L ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith

end ZetaInputs

end RvmClock
