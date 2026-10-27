import PaperMath.Papers.RvmClock.ZetaNodes
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Lemma 4.4: `|ζ(σ+it)| ≤ 2.74 t^{𝔢_E^*(σ)} log t` for `-0.01 ≤ σ ≤ 3`, `t ≥ 98`

The functional equation `ζ(s) = χ(s) ζ(1-s)` and Lemma 4.3 (`|χ(s)| ≤ 1.0070 (t/2π)^{1/2-σ}`) enter as
hypotheses `hFE`, `hchi`.
-/

namespace RvmClock.ZetaLines

open Complex RvmClock.Profile

lemma log_98 : (4.5747 : ℝ) ≤ Real.log 98 := by
  have h : Real.log ((2 : ℝ) ^ 33) ≤ Real.log ((98 : ℝ) ^ 5) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

lemma zeta_conj_norm' (w : ℂ) : ‖riemannZeta w‖ = ‖riemannZeta ((starRingEnd ℂ) w)‖ := by
  rw [riemannZeta_conj, Complex.norm_conj]

/-- the right half: `1/2 ≤ σ ≤ 3`, `t ≥ 98` (display (4.5), with `2.7185` for `2.7167`). -/
theorem right_half (I : ExplicitInputs) {σ t : ℝ} (hσ : σ ∈ Set.Icc (1/2 : ℝ) 3) (ht : 98 ≤ t) :
    ‖riemannZeta (sp σ t)‖ ≤ 2.7185 * t ^ gE σ * Real.log t := by
  obtain ⟨h1, h2⟩ := hσ
  have ht0 : 0 < t := by linarith
  obtain ⟨g0, g1⟩ := gE_bounds h1
  set g := gE σ with hg
  set w := (10 : ℂ) + sp σ t with hw
  set u := 1 + 84.5 / t ^ 2 with hu
  have hX := half_three I σ ⟨h1, h2⟩ t
  rw [← hg, ← hw] at hX
  -- |s - 1| ≥ t
  have hs1 : t ≤ ‖sp σ t - 1‖ := by
    have := Complex.abs_im_le_norm (sp σ t - 1); simp at this; rwa [abs_of_pos ht0] at this
  -- |w| ≤ t u
  have hw0 : 0 < ‖w‖ := by have := w_norm_ge (t := t) h1; rw [← hw] at this; linarith
  have hw1 : 1 ≤ ‖w‖ := by have := w_norm_ge (t := t) h1; rw [← hw] at this; linarith
  have htu : t * u = t + 84.5 / t := by rw [hu]; field_simp
  have hwle : ‖w‖ ≤ t * u := by
    have a : ‖w‖ ^ 2 ≤ (t * u) ^ 2 := by
      rw [norm_sq, htu, hw]; simp
      have : 0 ≤ (84.5 / t) ^ 2 := sq_nonneg _
      have e : (t + 84.5 / t) ^ 2 = t ^ 2 + 169 + (84.5 / t) ^ 2 := by field_simp; ring
      rw [e]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 a
  -- u ≤ u0
  have hu1 : 1 ≤ u := by
    rw [hu]
    have : 0 ≤ 84.5 / t ^ 2 := by positivity
    linarith
  have hu0 : u ≤ 1 + 84.5 / 9604 := by
    rw [hu]
    have : 84.5 / t ^ 2 ≤ 84.5 / 9604 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
    linarith
  -- |w|^{1+g} ≤ t^{1+g} * Cu
  have hpow : ‖w‖ ^ (1 + g) ≤ t ^ (1 + g) * (u * (1 + 27/164 * (u - 1))) := by
    have a1 : ‖w‖ ^ (1 + g) ≤ (t * u) ^ (1 + g) := Real.rpow_le_rpow hw0.le hwle (by linarith)
    rw [Real.mul_rpow ht0.le (by linarith)] at a1
    have a2 : u ^ (1 + g) ≤ u ^ ((1 : ℝ) + 27/164) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have a3 : u ^ ((1 : ℝ) + 27/164) = u * u ^ ((27 : ℝ)/164) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have a4 : u ^ ((27 : ℝ)/164) ≤ 1 + 27/164 * (u - 1) := by
      have := rpow_one_add_le_one_add_mul_self (s := u - 1) (by linarith) (p := 27/164)
        (by norm_num) (by norm_num)
      simpa using this
    have a5 : u ^ (1 + g) ≤ u * (1 + 27/164 * (u - 1)) := by
      rw [a3] at a2; nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ u) ((27 : ℝ)/164)]
    have tp : 0 ≤ t ^ (1 + g) := by positivity
    calc ‖w‖ ^ (1 + g) ≤ t ^ (1 + g) * u ^ (1 + g) := a1
      _ ≤ t ^ (1 + g) * (u * (1 + 27/164 * (u - 1))) := by gcongr
  -- |Log w| ≤ log t + c
  have hlog : ‖Complex.log w‖ ≤ Real.log t + (84.5 / 9604 + 1.5707965) := by
    have a1 := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
    rw [Complex.log_re, Complex.log_im] at a1
    have hre : 0 ≤ w.re := by rw [hw]; simp; linarith
    have a2 : |Complex.arg w| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.2 hre
    have hpi := Real.pi_lt_d6
    have a3 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw1
    have a4 : Real.log ‖w‖ ≤ Real.log t + Real.log u := by
      rw [← Real.log_mul ht0.ne' (by linarith)]
      exact Real.log_le_log hw0 hwle
    have a5 : Real.log u ≤ 84.5 / 9604 := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < u); linarith
    rw [abs_of_nonneg a3] at a1
    linarith
  -- assemble
  have hL : 4.5747 ≤ Real.log t := le_trans log_98 (Real.log_le_log (by norm_num) ht)
  have hL0 : 0 < Real.log t := by linarith
  have hc : Real.log t + (84.5 / 9604 + 1.5707965)
      ≤ Real.log t * (1 + (84.5 / 9604 + 1.5707965) / 4.5747) := by
    have : (84.5 / 9604 + 1.5707965) ≤ Real.log t * ((84.5 / 9604 + 1.5707965) / 4.5747) := by
      rw [mul_div_assoc']; rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  have hCu : u * (1 + 27/164 * (u - 1)) ≤ (1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604)) := by
    have : 0 ≤ u - 1 := by linarith
    nlinarith
  have hζ : ‖riemannZeta (sp σ t)‖ * t ≤ 2 * ‖w‖ ^ (1 + g) * ‖Complex.log w‖ := by
    have : ‖Xi (sp σ t)‖ = ‖sp σ t - 1‖ * ‖riemannZeta (sp σ t)‖ := by unfold Xi; rw [norm_mul]
    rw [this] at hX
    nlinarith [norm_nonneg (riemannZeta (sp σ t))]
  have tg : t ^ (1 + g) = t * t ^ g := by rw [Real.rpow_add ht0, Real.rpow_one]
  have tgp : 0 ≤ t ^ g := by positivity
  have hlogn : 0 ≤ ‖Complex.log w‖ := norm_nonneg _
  have step : 2 * ‖w‖ ^ (1 + g) * ‖Complex.log w‖
      ≤ 2 * (t * t ^ g * ((1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604))))
          * (Real.log t * (1 + (84.5 / 9604 + 1.5707965) / 4.5747)) := by
    have b1 : ‖w‖ ^ (1 + g) ≤ t * t ^ g * ((1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604))) := by
      rw [← tg]
      calc ‖w‖ ^ (1 + g) ≤ t ^ (1 + g) * (u * (1 + 27/164 * (u - 1))) := hpow
        _ ≤ t ^ (1 + g) * ((1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604))) := by gcongr
    have b2 : ‖Complex.log w‖ ≤ Real.log t * (1 + (84.5 / 9604 + 1.5707965) / 4.5747) :=
      le_trans hlog hc
    have b0 : 0 ≤ ‖w‖ ^ (1 + g) := by positivity
    have := mul_le_mul b1 b2 hlogn (by positivity)
    nlinarith
  have hnum : 2 * ((1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604)))
      * (1 + (84.5 / 9604 + 1.5707965) / 4.5747) ≤ (2.7185 : ℝ) := by norm_num
  have final : ‖riemannZeta (sp σ t)‖ * t ≤ (2.7185 * t ^ g * Real.log t) * t := by
    have e : 2 * (t * t ^ g * ((1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604))))
        * (Real.log t * (1 + (84.5 / 9604 + 1.5707965) / 4.5747))
        = (2 * ((1 + 84.5 / 9604) * (1 + 27/164 * (84.5 / 9604)))
          * (1 + (84.5 / 9604 + 1.5707965) / 4.5747)) * (t ^ g * Real.log t) * t := by ring
    have hq : 0 ≤ t ^ g * Real.log t * t := by positivity
    calc ‖riemannZeta (sp σ t)‖ * t ≤ _ := le_trans hζ step
      _ = _ := e
      _ ≤ 2.7185 * (t ^ g * Real.log t) * t := by
        have := mul_le_mul_of_nonneg_right hnum hq; nlinarith
      _ = (2.7185 * t ^ g * Real.log t) * t := by ring
  exact le_of_mul_le_mul_right final ht0

/-- **Lemma 4.4.** -/
theorem lemma_4_4 (I : ExplicitInputs) (chi : ℂ → ℂ)
    (hFE : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      riemannZeta (sp σ t) = chi (sp σ t) * riemannZeta (1 - sp σ t))
    (hchi : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      ‖chi (sp σ t)‖ ≤ 1.0070 * (t / (2 * Real.pi)) ^ (1/2 - σ)) :
    ∀ σ ∈ Set.Icc (-0.01 : ℝ) 3, ∀ t : ℝ, 98 ≤ t →
      ‖riemannZeta (sp σ t)‖ ≤ 2.74 * t ^ eStar σ * Real.log t := by
  intro σ hσ t ht
  obtain ⟨h1, h2⟩ := hσ
  have ht0 : 0 < t := by linarith
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  rcases le_or_gt (1/2) σ with hs | hs
  · rw [eStar_of_half_le hs]
    have := right_half I ⟨hs, h2⟩ ht
    have : 0 ≤ t ^ gE σ * Real.log t := by positivity
    nlinarith
  · have hsσ : σ ∈ Set.Icc (-0.01 : ℝ) (1/2) := ⟨h1, hs.le⟩
    rw [eStar_of_le_half hs.le]
    have hz := hFE σ hsσ t ht
    have hc := hchi σ hsσ t ht
    have hconj : (starRingEnd ℂ) (1 - sp σ t) = sp (1 - σ) t := by
      apply Complex.ext <;> simp [sp]
    have hr := right_half I (σ := 1 - σ) ⟨by linarith, by linarith⟩ ht
    have h1z : ‖riemannZeta (1 - sp σ t)‖ ≤ 2.7185 * t ^ gE (1 - σ) * Real.log t := by
      rw [zeta_conj_norm', hconj]; exact hr
    have hpi := Real.pi_gt_three
    have hq : (t / (2 * Real.pi)) ^ (1/2 - σ) ≤ t ^ (1/2 - σ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e : t ^ (1/2 - σ + gE (1 - σ)) = t ^ (1/2 - σ) * t ^ gE (1 - σ) := Real.rpow_add ht0 _ _
    rw [hz, norm_mul, e]
    have p1 : 0 ≤ t ^ (1/2 - σ) := by positivity
    have p2 : 0 ≤ t ^ gE (1 - σ) := by positivity
    have c1 : ‖chi (sp σ t)‖ ≤ 1.0070 * t ^ (1/2 - σ) := by nlinarith
    have := mul_le_mul c1 h1z (norm_nonneg _) (by positivity)
    have : 0 ≤ t ^ (1/2 - σ) * t ^ gE (1 - σ) * Real.log t := by positivity
    nlinarith

end RvmClock.ZetaLines
