import PaperMath.Papers.RvmClock.ZetaLines

/-!
# Lemma 4.4, second part: the boundary bounds (4.4) on the nine lines and the interpolation on `[1/2, 3]`
-/

namespace RvmClock.ZetaLines

open Complex RvmClock.Profile

lemma exp_105_492 : Real.exp (105 / 492) ≤ 2.7182818286 := by
  have h1 : Real.exp (105 / 492) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
  have h2 := Real.exp_one_lt_d9
  linarith

/-- the line `σ = 1/2` -/
lemma H_half (I : ExplicitInputs) (t : ℝ) (ht : 3 < |t|) :
    ‖riemannZeta (sp (1/2) t)‖ ≤ 2 * |t| ^ ((27 : ℝ) / 164) * Real.log |t| := by
  have ht0 : 0 < |t| := by linarith
  have hl0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  have hp0 : 0 ≤ |t| ^ ((27 : ℝ) / 164) := by positivity
  rcases le_or_gt |t| (Real.exp 105) with h | h
  · have hz := I.hpy t ht h
    have e1 : |t| ^ ((1 : ℝ) / 6) = |t| ^ ((27 : ℝ) / 164) * |t| ^ ((1 : ℝ) / 492) := by
      rw [← Real.rpow_add ht0]; norm_num
    have e2 : |t| ^ ((1 : ℝ) / 492) ≤ 2.7182818286 := by
      calc |t| ^ ((1 : ℝ) / 492) ≤ (Real.exp 105) ^ ((1 : ℝ) / 492) :=
            Real.rpow_le_rpow ht0.le h (by norm_num)
        _ = Real.exp (105 / 492) := by rw [← Real.exp_mul]; norm_num
        _ ≤ 2.7182818286 := exp_105_492
    rw [e1] at hz
    have : 0.618 * (|t| ^ ((27 : ℝ) / 164) * |t| ^ ((1 : ℝ) / 492)) * Real.log |t|
        ≤ 2 * |t| ^ ((27 : ℝ) / 164) * Real.log |t| := by
      have hq : 0 ≤ |t| ^ ((27 : ℝ) / 164) * Real.log |t| := mul_nonneg hp0 hl0
      have : 0.618 * |t| ^ ((1 : ℝ) / 492) ≤ 2 := by nlinarith
      nlinarith
    linarith
  · have hz := I.py t h
    have hl : 105 < Real.log |t| := by rwa [Real.lt_log_iff_exp_lt ht0]
    have : 66.7 * |t| ^ ((27 : ℝ) / 164) ≤ 2 * |t| ^ ((27 : ℝ) / 164) * Real.log |t| := by
      nlinarith
    linarith

lemma L_half (I : ExplicitInputs) (t : ℝ) :
    ‖Xi (sp (1/2) t)‖ ≤ 2 * ‖(10 : ℂ) + sp (1/2) t‖ ^ (1 + 27/164 : ℝ) * ‖Complex.log (10 + sp (1/2) t)‖ :=
  line_bound I ⟨le_refl _, by norm_num⟩ (by norm_num) (H_half I) t

/-- the lines `σ = σ_m`, `4 ≤ m ≤ 9` -/
lemma H_yang (I : ExplicitInputs) (m : ℕ) (hm4 : 4 ≤ m) (hm9 : m ≤ 9) {σ0 e : ℝ}
    (hσ : (1 - (m : ℝ) / (2 ^ m - 2)) = σ0) (he : (1 : ℝ) / (2 ^ m - 2) = e)
    (t : ℝ) (ht : 3 < |t|) : ‖riemannZeta (sp σ0 t)‖ ≤ 2 * |t| ^ e * Real.log |t| := by
  have := I.yang m hm4 hm9 t ht.le
  rwa [hσ, he] at this

lemma L_m (I : ExplicitInputs) (m : ℕ) (hm4 : 4 ≤ m) (hm9 : m ≤ 9) {σ0 e : ℝ}
    (hσ : (1 - (m : ℝ) / (2 ^ m - 2)) = σ0) (he : (1 : ℝ) / (2 ^ m - 2) = e)
    (hσ0 : σ0 ∈ Set.Icc (1/2 : ℝ) 3) (he0 : 0 ≤ e) (t : ℝ) :
    ‖Xi (sp σ0 t)‖ ≤ 2 * ‖(10 : ℂ) + sp σ0 t‖ ^ (1 + e) * ‖Complex.log (10 + sp σ0 t)‖ :=
  line_bound I hσ0 he0 (H_yang I m hm4 hm9 hσ he) t

lemma L_one (I : ExplicitInputs) (t : ℝ) :
    ‖Xi (sp 1 t)‖ ≤ 2 * ‖(10 : ℂ) + sp 1 t‖ ^ (1 + 0 : ℝ) * ‖Complex.log (10 + sp 1 t)‖ := by
  apply line_bound I ⟨by norm_num, by norm_num⟩ (le_refl 0)
  intro t ht
  have := I.patel t ht.le
  have hl0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  rw [Real.rpow_zero]; linarith

lemma L_three (I : ExplicitInputs) (t : ℝ) :
    ‖Xi (sp 3 t)‖ ≤ 2 * ‖(10 : ℂ) + sp 3 t‖ ^ (1 + 0 : ℝ) * ‖Complex.log (10 + sp 3 t)‖ := by
  apply line_bound I ⟨by norm_num, le_refl _⟩ (le_refl 0)
  intro t ht
  have := I.zeta3 t
  have hl : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht.le
  have := log_three_gt_one
  rw [Real.rpow_zero]; linarith

/-- (4.4) interpolated: `|Ξ(s)| ≤ 2 |Q+s|^{1+𝔢_E(σ)} |Log(Q+s)|` for `1/2 ≤ σ ≤ 3`, all `t`. -/
theorem half_three (I : ExplicitInputs) (σ : ℝ) (hσ : σ ∈ Set.Icc (1/2 : ℝ) 3) (t : ℝ) :
    ‖Xi (sp σ t)‖ ≤ 2 * ‖(10 : ℂ) + sp σ t‖ ^ (1 + gE σ) * ‖Complex.log (10 + sp σ t)‖ := by
  obtain ⟨h1, h2⟩ := hσ
  have L4 := L_m I 4 (le_refl _) (by norm_num) (σ0 := 5/7) (e := 1/14) (by norm_num) (by norm_num)
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  have L5 := L_m I 5 (by norm_num) (by norm_num) (σ0 := 5/6) (e := 1/30) (by norm_num) (by norm_num)
    ⟨by norm_num, by norm_num⟩ (by norm_num)
  have L6 := L_m I 6 (by norm_num) (by norm_num) (σ0 := 28/31) (e := 1/62) (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)
  have L7 := L_m I 7 (by norm_num) (by norm_num) (σ0 := 17/18) (e := 1/126) (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)
  have L8 := L_m I 8 (by norm_num) (by norm_num) (σ0 := 123/127) (e := 1/254) (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)
  have L9 := L_m I 9 (by norm_num) (le_refl _) (σ0 := 167/170) (e := 1/510) (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)
  have L1 := L_one I
  have L3 := L_three I
  have LH := L_half I
  rcases le_or_gt σ (5/7) with a | a
  · exact strip I (by norm_num) (le_refl _) (by norm_num) (by norm_num) LH L4
      (fun x hx => gE_strip0 hx.1 hx.2) σ ⟨h1, a⟩ t
  rcases le_or_gt σ (5/6) with b | b
  · exact strip I (by norm_num) (by norm_num) (by norm_num) (by norm_num) L4 L5
      (fun x hx => gE_strip1 hx.1 hx.2) σ ⟨a.le, b⟩ t
  rcases le_or_gt σ (28/31) with c | c
  · exact strip I (by norm_num) (by norm_num) (by norm_num) (by norm_num) L5 L6
      (fun x hx => gE_strip2 hx.1 hx.2) σ ⟨b.le, c⟩ t
  rcases le_or_gt σ (17/18) with d | d
  · exact strip I (by norm_num) (by norm_num) (by norm_num) (by norm_num) L6 L7
      (fun x hx => gE_strip3 hx.1 hx.2) σ ⟨c.le, d⟩ t
  rcases le_or_gt σ (123/127) with e | e
  · exact strip I (by norm_num) (by norm_num) (by norm_num) (by norm_num) L7 L8
      (fun x hx => gE_strip4 hx.1 hx.2) σ ⟨d.le, e⟩ t
  rcases le_or_gt σ (167/170) with f | f
  · exact strip I (by norm_num) (by norm_num) (by norm_num) (by norm_num) L8 L9
      (fun x hx => gE_strip5 hx.1 hx.2) σ ⟨e.le, f⟩ t
  rcases le_or_gt σ 1 with g | g
  · exact strip I (by norm_num) (by norm_num) (le_refl 0) (by norm_num) L9 L1
      (fun x hx => by rw [gE_strip6 hx.1 hx.2]; rfl) σ ⟨f.le, g⟩ t
  · exact strip I (by norm_num) (by norm_num) (le_refl 0) (le_refl 0) L1 L3
      (fun x hx => by rw [gE_strip7 hx.1]; unfold sl; ring) σ ⟨g.le, h2⟩ t

end RvmClock.ZetaLines
