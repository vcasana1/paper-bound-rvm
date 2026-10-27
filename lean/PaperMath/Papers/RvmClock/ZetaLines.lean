import PaperMath.Papers.RvmClock.Profile
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4.4, first part: `|Ξ(s)| ≤ 2 |Q+s|^{1+𝔢_E(σ)} |Log(Q+s)|` on `1/2 ≤ σ ≤ 3` (`Q = 10`)

`Ξ(s) = (s-1) ζ(s)` with Mathlib's `riemannZeta`. The explicit bounds of Theorem 3.3, the consequence
`|Ξ(s)| ≤ |s| + 2|s||s-1|` of Titchmarsh (2.1.4) and the Phragmén–Lindelöf principle (Theorem 3.4) for `Ξ`
are the hypotheses `ExplicitInputs`.
-/

namespace RvmClock.ZetaLines

open Complex RvmClock.Profile

noncomputable def Xi (s : ℂ) : ℂ := (s - 1) * riemannZeta s

/-- `σ + i t` -/
noncomputable def sp (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

@[simp] lemma sp_re (σ t : ℝ) : (sp σ t).re = σ := by simp [sp]
@[simp] lemma sp_im (σ t : ℝ) : (sp σ t).im = t := by simp [sp]

/-- The inputs of Lemma 4.4. Literal: HPY and Patel–Yang on `σ = 1/2`, Patel on `σ = 1`.
Not literal:
* `yang` uses constant `2` instead of Yang's `1.546` (justified in Remark 4.5(ii));
* `zeta3` is the trivial bound `|ζ(3+it)| ≤ ζ(3) < 1.21`;
* `small` is the consequence `|Ξ(s)| ≤ |s| + 2|s||s-1|` of Titchmarsh (2.1.4), not the formula itself;
* `pl` is Theorem 3.4 (Fiori Cor. 3) instantiated for `Ξ`, `Q = 10`, `A = B = 2`, `α₂ = 1`; its hypotheses on `Ξ`
  (holomorphy in the strip, growth) are classical facts not checked here. -/
structure ExplicitInputs : Prop where
  hpy : ∀ t : ℝ, 3 < |t| → |t| ≤ Real.exp 105 →
    ‖riemannZeta (sp (1/2) t)‖ ≤ 0.618 * |t| ^ ((1 : ℝ) / 6) * Real.log |t|
  py : ∀ t : ℝ, Real.exp 105 < |t| → ‖riemannZeta (sp (1/2) t)‖ ≤ 66.7 * |t| ^ ((27 : ℝ) / 164)
  /-- Yang's bound with constant `2` (Remark 4.5(ii)). -/
  yang : ∀ m : ℕ, 4 ≤ m → m ≤ 9 → ∀ t : ℝ, 3 ≤ |t| →
    ‖riemannZeta (sp (1 - (m : ℝ) / (2 ^ m - 2)) t)‖ ≤ 2 * |t| ^ ((1 : ℝ) / (2 ^ m - 2)) * Real.log |t|
  patel : ∀ t : ℝ, 3 ≤ |t| → ‖riemannZeta (sp 1 t)‖ ≤ Real.log |t|
  zeta3 : ∀ t : ℝ, ‖riemannZeta (sp 3 t)‖ ≤ 1.21
  small : ∀ σ ∈ Set.Icc (1/2 : ℝ) 3, ∀ t : ℝ,
    ‖Xi (sp σ t)‖ ≤ ‖sp σ t‖ + 2 * ‖sp σ t‖ * ‖sp σ t - 1‖
  pl : ∀ a b α β : ℝ, a < b → 1 - a < 10 → β ≤ α → 0 ≤ β →
    (∀ t : ℝ, ‖Xi (sp a t)‖ ≤ 2 * ‖(10 : ℂ) + sp a t‖ ^ α * ‖Complex.log (10 + sp a t)‖) →
    (∀ t : ℝ, ‖Xi (sp b t)‖ ≤ 2 * ‖(10 : ℂ) + sp b t‖ ^ β * ‖Complex.log (10 + sp b t)‖) →
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, ‖Xi (sp σ t)‖ ≤
      (2 * ‖(10 : ℂ) + sp σ t‖ ^ α) ^ ((b - σ) / (b - a))
        * (2 * ‖(10 : ℂ) + sp σ t‖ ^ β) ^ ((σ - a) / (b - a)) * ‖Complex.log (10 + sp σ t)‖

lemma norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma w_norm_ge {σ t : ℝ} (hσ : 1/2 ≤ σ) : 10 + σ ≤ ‖(10 : ℂ) + sp σ t‖ := by
  have := Complex.re_le_norm ((10 : ℂ) + sp σ t)
  simpa using this

lemma log_8 : (2.0794 : ℝ) ≤ Real.log 8 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9; linarith

lemma log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

/-- `Re Log w = log |w| ≤ |Log w|`. -/
lemma log_norm_le (w : ℂ) : Real.log ‖w‖ ≤ ‖Complex.log w‖ := by
  have := Complex.re_le_norm (Complex.log w)
  rwa [Complex.log_re] at this

/-- A boundary line: from `|ζ(σ₀+it)| ≤ 2|t|^e log|t|` for `|t| > 3` to (4.4). -/
lemma line_bound (I : ExplicitInputs) {σ0 e : ℝ} (hσ0 : σ0 ∈ Set.Icc (1/2 : ℝ) 3) (he : 0 ≤ e)
    (H : ∀ t : ℝ, 3 < |t| → ‖riemannZeta (sp σ0 t)‖ ≤ 2 * |t| ^ e * Real.log |t|) (t : ℝ) :
    ‖Xi (sp σ0 t)‖ ≤ 2 * ‖(10 : ℂ) + sp σ0 t‖ ^ (1 + e) * ‖Complex.log (10 + sp σ0 t)‖ := by
  obtain ⟨h1, h2⟩ := hσ0
  set w := (10 : ℂ) + sp σ0 t with hw
  have hw1 : 10.5 ≤ ‖w‖ := by have := w_norm_ge (t := t) h1; linarith
  have hw0 : 0 < ‖w‖ := by linarith
  have hL8 : 2.0794 ≤ Real.log ‖w‖ :=
    le_trans log_8 (Real.log_le_log (by norm_num) (by linarith))
  have hLL : Real.log ‖w‖ ≤ ‖Complex.log w‖ := log_norm_le w
  have hpow1 : ‖w‖ ≤ ‖w‖ ^ (1 + e) := by
    calc ‖w‖ = ‖w‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ‖w‖ ^ (1 + e) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpos : 0 ≤ ‖w‖ ^ (1 + e) := by positivity
  have key : ‖Xi (sp σ0 t)‖ ≤ 2 * ‖w‖ ^ (1 + e) * Real.log ‖w‖ := by
    rcases le_or_gt |t| 3 with ht | ht
    · -- small |t|
      have hs := I.small σ0 ⟨h1, h2⟩ t
      have n1 : ‖sp σ0 t‖ ≤ 4.2427 := by
        have : ‖sp σ0 t‖ ^ 2 ≤ 4.2427 ^ 2 := by
          rw [norm_sq]; simp
          nlinarith [abs_nonneg t, sq_abs t]
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 this
      have n2 : ‖sp σ0 t - 1‖ ≤ 3.6056 := by
        have : ‖sp σ0 t - 1‖ ^ 2 ≤ 3.6056 ^ 2 := by
          rw [norm_sq]; simp
          nlinarith [abs_nonneg t, sq_abs t]
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 this
      have hX : ‖Xi (sp σ0 t)‖ ≤ 34.9 := by
        have := mul_le_mul n1 n2 (norm_nonneg _) (by norm_num)
        nlinarith [norm_nonneg (sp σ0 t)]
      have hprod := mul_le_mul hw1 hL8 (by norm_num) hw0.le
      have : (34.9 : ℝ) ≤ 2 * ‖w‖ * Real.log ‖w‖ := by nlinarith
      have hmono := mul_le_mul_of_nonneg_right hpow1 (by linarith : (0:ℝ) ≤ Real.log ‖w‖)
      nlinarith
    · -- |t| > 3
      have ht0 : 0 < |t| := by linarith
      have hz := H t ht
      have hs1 : ‖sp σ0 t - 1‖ ≤ ‖w‖ := by
        have a : ‖sp σ0 t - 1‖ ^ 2 ≤ ‖w‖ ^ 2 := by
          rw [norm_sq, norm_sq, hw]; simp; nlinarith
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 a
      have htw : |t| ≤ ‖w‖ := by
        have := Complex.abs_im_le_norm w; simpa [hw] using this
      have hte : |t| ^ e ≤ ‖w‖ ^ e := Real.rpow_le_rpow ht0.le htw he
      have hlt : Real.log |t| ≤ Real.log ‖w‖ := Real.log_le_log ht0 htw
      have hl0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hz2 : ‖riemannZeta (sp σ0 t)‖ ≤ 2 * ‖w‖ ^ e * Real.log ‖w‖ := by
        calc ‖riemannZeta (sp σ0 t)‖ ≤ 2 * |t| ^ e * Real.log |t| := hz
          _ ≤ 2 * ‖w‖ ^ e * Real.log ‖w‖ := by gcongr
      have e1 : ‖w‖ ^ (1 + e) = ‖w‖ * ‖w‖ ^ e := by
        rw [Real.rpow_add hw0, Real.rpow_one]
      unfold Xi; rw [norm_mul, e1]
      have : 0 ≤ 2 * ‖w‖ ^ e * Real.log ‖w‖ := by positivity
      calc ‖sp σ0 t - 1‖ * ‖riemannZeta (sp σ0 t)‖ ≤ ‖w‖ * (2 * ‖w‖ ^ e * Real.log ‖w‖) :=
            mul_le_mul hs1 hz2 (norm_nonneg _) hw0.le
        _ = 2 * (‖w‖ * ‖w‖ ^ e) * Real.log ‖w‖ := by ring
  calc ‖Xi (sp σ0 t)‖ ≤ 2 * ‖w‖ ^ (1 + e) * Real.log ‖w‖ := key
    _ ≤ 2 * ‖w‖ ^ (1 + e) * ‖Complex.log w‖ := by gcongr

/-- `(2x^α)^λ (2x^β)^μ = 2 x^{αλ+βμ}` when `λ + μ = 1`. -/
lemma interp {x α β l m : ℝ} (hx : 0 < x) (hlm : l + m = 1) :
    (2 * x ^ α) ^ l * (2 * x ^ β) ^ m = 2 * x ^ (α * l + β * m) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le]
  have h2 : (2 : ℝ) ^ l * (2 : ℝ) ^ m = 2 := by
    rw [← Real.rpow_add (by norm_num), hlm, Real.rpow_one]
  have hx2 : x ^ (α * l) * x ^ (β * m) = x ^ (α * l + β * m) := (Real.rpow_add hx _ _).symm
  calc 2 ^ l * x ^ (α * l) * (2 ^ m * x ^ (β * m))
      = (2 ^ l * 2 ^ m) * (x ^ (α * l) * x ^ (β * m)) := by ring
    _ = 2 * x ^ (α * l + β * m) := by rw [h2, hx2]

/-- One strip of the interpolation. -/
lemma strip (I : ExplicitInputs) {a b ea eb : ℝ} (hab : a < b) (ha : 1/2 ≤ a) (heb : 0 ≤ eb)
    (hle : eb ≤ ea)
    (La : ∀ t : ℝ, ‖Xi (sp a t)‖ ≤ 2 * ‖(10 : ℂ) + sp a t‖ ^ (1 + ea) * ‖Complex.log (10 + sp a t)‖)
    (Lb : ∀ t : ℝ, ‖Xi (sp b t)‖ ≤ 2 * ‖(10 : ℂ) + sp b t‖ ^ (1 + eb) * ‖Complex.log (10 + sp b t)‖)
    (hg : ∀ σ ∈ Set.Icc a b, gE σ = ea + sl a b ea eb * (σ - a)) :
    ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖Xi (sp σ t)‖ ≤ 2 * ‖(10 : ℂ) + sp σ t‖ ^ (1 + gE σ) * ‖Complex.log (10 + sp σ t)‖ := by
  intro σ hσ t
  have hP := I.pl a b (1 + ea) (1 + eb) hab (by linarith) (by linarith) (by linarith) La Lb σ hσ t
  have hx : 0 < ‖(10 : ℂ) + sp σ t‖ := by
    have h1 := hσ.1
    have := w_norm_ge (t := t) (le_trans ha h1); linarith
  have hba : b - a ≠ 0 := by linarith
  rw [interp hx (by field_simp; ring)] at hP
  have hexp : (1 + ea) * ((b - σ) / (b - a)) + (1 + eb) * ((σ - a) / (b - a)) = 1 + gE σ := by
    rw [hg σ hσ]; unfold sl; field_simp; ring
  rwa [hexp] at hP

end RvmClock.ZetaLines
