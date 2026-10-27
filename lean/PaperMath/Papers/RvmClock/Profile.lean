import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The explicit profile `𝔢_E` and its reflection `𝔢_E^*` (Section 4.1, Lemma 4.4)

Nodes `ς₀ < … < ς₈ = 1/2, σ₄, …, σ₉, 1, 3`, `σ_m = 1 - m/(2^m - 2)`, values
`e₀ = 27/164`, `e_i = 1/(2^{i+3} - 2)` (`1 ≤ i ≤ 6`), `e₇ = e₈ = 0`.
`gE` is the linear interpolation on `[1/2, ∞)` (constant `0` after `1`), written with hinges so that
it is visibly continuous; `eStar` is the reflected extension (1.4).
-/

namespace RvmClock.Profile

/-- slope on `[ς_i, ς_{i+1}]` -/
noncomputable def sl (a b ea eb : ℝ) : ℝ := (eb - ea) / (b - a)

noncomputable def s0 : ℝ := sl (1/2) (5/7) (27/164) (1/14)
noncomputable def s1 : ℝ := sl (5/7) (5/6) (1/14) (1/30)
noncomputable def s2 : ℝ := sl (5/6) (28/31) (1/30) (1/62)
noncomputable def s3 : ℝ := sl (28/31) (17/18) (1/62) (1/126)
noncomputable def s4 : ℝ := sl (17/18) (123/127) (1/126) (1/254)
noncomputable def s5 : ℝ := sl (123/127) (167/170) (1/254) (1/510)
noncomputable def s6 : ℝ := sl (167/170) 1 (1/510) 0

/-- The profile on `[1/2, ∞)`. -/
noncomputable def gE (σ : ℝ) : ℝ :=
  27/164 + s0 * (σ - 1/2) + (s1 - s0) * max 0 (σ - 5/7) + (s2 - s1) * max 0 (σ - 5/6)
    + (s3 - s2) * max 0 (σ - 28/31) + (s4 - s3) * max 0 (σ - 17/18)
    + (s5 - s4) * max 0 (σ - 123/127) + (s6 - s5) * max 0 (σ - 167/170) + (0 - s6) * max 0 (σ - 1)

/-- The reflected profile `𝔢_E^*`. -/
noncomputable def eStar (σ : ℝ) : ℝ := if σ ≤ 1/2 then 1/2 - σ + gE (1 - σ) else gE σ

lemma gE_continuous : Continuous gE := by
  unfold gE; fun_prop

lemma eStar_continuous : Continuous eStar := by
  unfold eStar
  apply Continuous.if_le
  · exact continuous_const.sub continuous_id |>.add (gE_continuous.comp (continuous_const.sub continuous_id))
  · exact gE_continuous
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    have hx' : x = 1/2 := hx
    subst hx'; norm_num

/-- `gE` on each strip: the linear interpolation `e_i + s_i (σ - ς_i)`. -/
lemma gE_strip0 {σ : ℝ} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 5/7) : gE σ = 27/164 + s0 * (σ - 1/2) := by
  unfold gE
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  ring

lemma gE_strip1 {σ : ℝ} (h1 : 5/7 ≤ σ) (h2 : σ ≤ 5/6) : gE σ = 1/14 + s1 * (σ - 5/7) := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  unfold s0 s1 sl; ring

lemma gE_strip2 {σ : ℝ} (h1 : 5/6 ≤ σ) (h2 : σ ≤ 28/31) : gE σ = 1/30 + s2 * (σ - 5/6) := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  unfold s0 s1 s2 sl; ring

lemma gE_strip3 {σ : ℝ} (h1 : 28/31 ≤ σ) (h2 : σ ≤ 17/18) : gE σ = 1/62 + s3 * (σ - 28/31) := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  unfold s0 s1 s2 s3 sl; ring

lemma gE_strip4 {σ : ℝ} (h1 : 17/18 ≤ σ) (h2 : σ ≤ 123/127) :
    gE σ = 1/126 + s4 * (σ - 17/18) := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith), max_eq_left (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  unfold s0 s1 s2 s3 s4 sl; ring

lemma gE_strip5 {σ : ℝ} (h1 : 123/127 ≤ σ) (h2 : σ ≤ 167/170) :
    gE σ = 1/254 + s5 * (σ - 123/127) := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
    max_eq_left (by linarith)]
  unfold s0 s1 s2 s3 s4 s5 sl; ring

lemma gE_strip6 {σ : ℝ} (h1 : 167/170 ≤ σ) (h2 : σ ≤ 1) :
    gE σ = 1/510 + s6 * (σ - 167/170) := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_left (by linarith)]
  unfold s0 s1 s2 s3 s4 s5 s6 sl; ring

lemma gE_strip7 {σ : ℝ} (h1 : 1 ≤ σ) : gE σ = 0 := by
  unfold gE
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
    max_eq_right (by linarith)]
  unfold s0 s1 s2 s3 s4 s5 s6 sl; ring

lemma gE_bounds {σ : ℝ} (h1 : 1/2 ≤ σ) : 0 ≤ gE σ ∧ gE σ ≤ 27/164 := by
  rcases le_or_gt σ (5/7) with a | a
  · rw [gE_strip0 h1 a]; unfold s0 sl; constructor <;> nlinarith
  rcases le_or_gt σ (5/6) with b | b
  · rw [gE_strip1 a.le b]; unfold s1 sl; constructor <;> nlinarith
  rcases le_or_gt σ (28/31) with c | c
  · rw [gE_strip2 b.le c]; unfold s2 sl; constructor <;> nlinarith
  rcases le_or_gt σ (17/18) with d | d
  · rw [gE_strip3 c.le d]; unfold s3 sl; constructor <;> nlinarith
  rcases le_or_gt σ (123/127) with e | e
  · rw [gE_strip4 d.le e]; unfold s4 sl; constructor <;> nlinarith
  rcases le_or_gt σ (167/170) with f | f
  · rw [gE_strip5 e.le f]; unfold s5 sl; constructor <;> nlinarith
  rcases le_or_gt σ 1 with g | g
  · rw [gE_strip6 f.le g]; unfold s6 sl; constructor <;> nlinarith
  · rw [gE_strip7 g.le]; norm_num

lemma eStar_nonneg {σ : ℝ} (h : σ ≤ 3) : 0 ≤ eStar σ := by
  unfold eStar
  split_ifs with hs
  · have := (gE_bounds (σ := 1 - σ) (by linarith)).1; linarith
  · exact (gE_bounds (by linarith)).1

lemma eStar_of_le_half {σ : ℝ} (h : σ ≤ 1/2) : eStar σ = 1/2 - σ + gE (1 - σ) := by
  unfold eStar; rw [if_pos h]

lemma eStar_of_half_le {σ : ℝ} (h : 1/2 ≤ σ) : eStar σ = gE σ := by
  unfold eStar
  split_ifs with hs
  · have : σ = 1/2 := le_antisymm hs h
    subst this; norm_num
  · rfl

end RvmClock.Profile
