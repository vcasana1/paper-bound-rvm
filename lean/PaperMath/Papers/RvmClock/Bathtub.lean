import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bathtub inequalities (used in the proof of Theorem 7.3)

For a measurable set `S ⊆ [c, ∞)` of finite measure `u`, `u² ≤ 2 ∫_S (t - c)`;
for `S ⊆ (-∞, c]`, `u² ≤ 2 ∫_S (c - t)`.
-/

open MeasureTheory Set

namespace RvmClock

/-- Abstract bathtub comparison: if `S` and `T` have the same finite measure, and `g ≥ θ` on `S \ T`,
`g ≤ θ` on `T \ S`, then `∫_T g ≤ ∫_S g`. -/
lemma bathtub_compare {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSf : volume S ≠ ⊤) (hST : volume S = volume T) {g : ℝ → ℝ} (θ : ℝ)
    (hgS : IntegrableOn g S) (hgT : IntegrableOn g T)
    (h1 : ∀ x ∈ S \ T, θ ≤ g x) (h2 : ∀ x ∈ T \ S, g x ≤ θ) :
    ∫ x in T, g x ≤ ∫ x in S, g x := by
  have hTf : volume T ≠ ⊤ := hST ▸ hSf
  have eS : S = (S ∩ T) ∪ (S \ T) := (Set.inter_union_diff S T).symm
  have eT : T = (S ∩ T) ∪ (T \ S) := by rw [Set.inter_comm]; exact (Set.inter_union_diff T S).symm
  have dS : Disjoint (S ∩ T) (S \ T) := Set.disjoint_sdiff_inter.symm
  have dT : Disjoint (S ∩ T) (T \ S) := by
    rw [Set.inter_comm]; exact Set.disjoint_sdiff_inter.symm
  have iS : ∫ x in S, g x = (∫ x in S ∩ T, g x) + ∫ x in S \ T, g x := by
    have h := setIntegral_union dS (hS.diff hT) (hgS.mono_set Set.inter_subset_left) (hgS.mono_set Set.sdiff_subset)
    rw [← eS] at h
    exact h
  have iT : ∫ x in T, g x = (∫ x in S ∩ T, g x) + ∫ x in T \ S, g x := by
    have h := setIntegral_union dT (hT.diff hS) (hgS.mono_set Set.inter_subset_left) (hgT.mono_set Set.sdiff_subset)
    rw [← eT] at h
    exact h
  have mSd : volume.real (S \ T) = volume.real (T \ S) := by
    have a1 := measureReal_inter_add_sdiff (μ := volume) (s := S) hT hSf
    have a2 := measureReal_inter_add_sdiff (μ := volume) (s := T) hS hTf
    have a3 : volume.real S = volume.real T := by simp [Measure.real, hST]
    rw [Set.inter_comm] at a2
    linarith
  have lo : volume.real (S \ T) • θ ≤ ∫ x in S \ T, g x :=
    setIntegral_ge_of_const_le (hS.diff hT) (measure_ne_top_of_subset Set.sdiff_subset hSf)
      h1 (hgS.mono_set Set.sdiff_subset)
  have hi : ∫ x in T \ S, g x ≤ θ * volume.real (T \ S) := by
    have := setIntegral_mono_on (hgT.mono_set Set.sdiff_subset)
      (integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hTf)) (hT.diff hS) h2
    rw [setIntegral_const, smul_eq_mul] at this
    linarith
  rw [smul_eq_mul, mSd, mul_comm] at lo
  rw [iS, iT]
  linarith

lemma vol_Icc_eq {S : Set ℝ} {c d : ℝ} (hSsub : S ⊆ Icc c d) (c' : ℝ) :
    volume (Icc c' (c' + volume.real S)) = volume S := by
  have hfin : volume S ≠ ⊤ := measure_ne_top_of_subset hSsub (by simp)
  rw [Real.volume_Icc, show c' + volume.real S - c' = volume.real S by ring]
  exact ENNReal.ofReal_toReal hfin

/-- Bathtub, right side: `S ⊆ [c,d]` ⇒ `|S|² ≤ 2 ∫_S (t - c)`. -/
lemma bathtub_right {S : Set ℝ} {c d : ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Icc c d) :
    (volume.real S) ^ 2 ≤ 2 * ∫ x in S, (x - c) := by
  set u := volume.real S with hu
  have hu0 : 0 ≤ u := measureReal_nonneg
  have hfin : volume S ≠ ⊤ := measure_ne_top_of_subset hSsub (by simp)
  have hcmp := bathtub_compare (S := S) (T := Icc c (c + u)) hS measurableSet_Icc hfin
    (vol_Icc_eq hSsub c).symm (g := fun x => x - c) u
    ((by fun_prop : Continuous fun x : ℝ => x - c).integrableOn_Icc.mono_set hSsub)
    (by fun_prop : Continuous fun x : ℝ => x - c).integrableOn_Icc
    (fun x hx => by
      have h1 := hSsub hx.1
      have h2 : x ∉ Icc c (c + u) := hx.2
      simp only [Set.mem_Icc, not_and, not_le] at h2
      linarith [h2 h1.1])
    (fun x hx => by have := hx.1; simp only [Set.mem_Icc] at this; linarith)
  have hT : ∫ x in Icc c (c + u), (x - c) = u ^ 2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_right (fun x => x) c, integral_id]
    ring
  linarith

/-- Bathtub, left side: `S ⊆ [d,c]` ⇒ `|S|² ≤ 2 ∫_S (c - t)`. -/
lemma bathtub_left {S : Set ℝ} {c d : ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Icc d c) :
    (volume.real S) ^ 2 ≤ 2 * ∫ x in S, (c - x) := by
  set u := volume.real S with hu
  have hu0 : 0 ≤ u := measureReal_nonneg
  have hfin : volume S ≠ ⊤ := measure_ne_top_of_subset hSsub (by simp)
  have hvol : volume (Icc (c - u) c) = volume S := by
    rw [Real.volume_Icc, show c - (c - u) = u by ring]
    exact ENNReal.ofReal_toReal hfin
  have hcmp := bathtub_compare (S := S) (T := Icc (c - u) c) hS measurableSet_Icc hfin
    hvol.symm (g := fun x => c - x) u
    ((by fun_prop : Continuous fun x : ℝ => c - x).integrableOn_Icc.mono_set hSsub)
    (by fun_prop : Continuous fun x : ℝ => c - x).integrableOn_Icc
    (fun x hx => by
      have h1 := hSsub hx.1
      have h2 : x ∉ Icc (c - u) c := hx.2
      simp only [Set.mem_Icc, not_and, not_le] at h2
      by_contra hc
      push Not at hc
      exact absurd h1.2 (not_le.mpr (h2 (by linarith))))
    (fun x hx => by have := hx.1; simp only [Set.mem_Icc] at this; linarith)
  have hT : ∫ x in Icc (c - u) c, (c - x) = u ^ 2 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_sub_left (fun x => x) c, integral_id]
    ring
  linarith

end RvmClock
