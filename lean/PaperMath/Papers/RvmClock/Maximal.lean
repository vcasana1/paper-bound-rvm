import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Int.Interval

/-!
# Discrete maximal inequality (Lemma 7.2 of *The Riemann–von Mangoldt clock*, v6)

Windows are half-open integer intervals `[A, B)`; the closed interval `[a, b]` is `Ico a (b+1)`.
-/

open Finset

namespace RvmClock

lemma sum_Ico_split {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℤ → ℝ) :
    ∑ r ∈ Ico a c, f r = ∑ r ∈ Ico a b, f r + ∑ r ∈ Ico b c, f r := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc,
    Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c)]

/-- Right rising-sun set: `j ∈ [A,B)` from which some `[j,b] ⊆ [A,B)` has nonnegative `f`-sum. -/
noncomputable def RS (f : ℤ → ℝ) (A B : ℤ) : Finset ℤ :=
  (Ico A B).filter (fun j => ∃ b ∈ Ico j B, 0 ≤ ∑ r ∈ Ico j (b + 1), f r)

/-- Rising-sun lemma (right version). -/
theorem rising_sun_right (f : ℤ → ℝ) (B : ℤ) :
    ∀ n : ℕ, ∀ A : ℤ, (B - A).toNat = n → 0 ≤ ∑ j ∈ RS f A B, f j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn
  classical
  by_cases hAB : B ≤ A
  · simp [RS, Finset.Ico_eq_empty_of_le hAB]
  push Not at hAB
  by_cases hA : A ∈ RS f A B
  · obtain ⟨b0, hb0, hb0s⟩ := (Finset.mem_filter.mp hA).2
    obtain ⟨bs, hbs, hmax⟩ := Finset.exists_max_image (Ico A B)
      (fun b => ∑ r ∈ Ico A (b + 1), f r) ⟨A, by simp [hAB]⟩
    have hbs' := Finset.mem_Ico.mp hbs
    have hb0' := Finset.mem_Ico.mp hb0
    have hS0 : 0 ≤ ∑ r ∈ Ico A (bs + 1), f r := le_trans hb0s (hmax b0 (by simp at hb0 ⊢; omega))
    have hsub : Ico A (bs + 1) ⊆ RS f A B := by
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hj'.1, by omega⟩, bs, Finset.mem_Ico.mpr ⟨by omega, hbs'.2⟩, ?_⟩
      rcases eq_or_lt_of_le hj'.1 with h | h
      · subst h; exact hS0
      · have hsplit := sum_Ico_split (a := A) (b := j) (c := bs + 1) (by omega) (by omega) f
        have hle : ∑ r ∈ Ico A (j - 1 + 1), f r ≤ ∑ r ∈ Ico A (bs + 1), f r :=
          hmax (j - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rw [show j - 1 + 1 = j by ring] at hle
        linarith
    have hrest : RS f A B = Ico A (bs + 1) ∪ RS f (bs + 1) B := by
      ext j
      constructor
      · intro hj
        rcases lt_or_ge j (bs + 1) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1, h⟩)
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h, (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2⟩, (Finset.mem_filter.mp hj).2⟩)
      · intro hj
        rcases Finset.mem_union.mp hj with h | h
        · exact hsub h
        · have h1 := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by have := Finset.mem_Ico.mp h1.1; omega, (Finset.mem_Ico.mp h1.1).2⟩, h1.2⟩
    have hdisj : Disjoint (Ico A (bs + 1)) (RS f (bs + 1) B) := by
      rw [Finset.disjoint_left]
      intro j hj hj2
      have := Finset.mem_Ico.mp (Finset.mem_filter.mp hj2).1
      have := Finset.mem_Ico.mp hj
      omega
    rw [hrest, Finset.sum_union hdisj]
    have := ih (B - (bs + 1)).toNat (by omega) (bs + 1) rfl
    linarith
  · have hrest : RS f A B = RS f (A + 1) B := by
      ext j
      simp only [RS, Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases eq_or_lt_of_le h1 with h | h
        · subst h
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_refl _, h2⟩, by simpa using h3⟩) hA
        · exact ⟨⟨by omega, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by omega, h2⟩, h3⟩
    rw [hrest]
    exact ih (B - (A + 1)).toNat (by omega) (A + 1) rfl

/-- Left rising-sun set: `l ∈ [A,B)` such that some `[a,l] ⊆ [A,B)` has nonnegative `f`-sum. -/
noncomputable def LS (f : ℤ → ℝ) (A B : ℤ) : Finset ℤ :=
  (Ico A B).filter (fun l : ℤ => ∃ a ∈ Icc A l, 0 ≤ ∑ r ∈ Ico a (l + 1), f r)

/-- Rising-sun lemma (left version). -/
theorem rising_sun_left (f : ℤ → ℝ) (A : ℤ) :
    ∀ n : ℕ, ∀ B : ℤ, (B - A).toNat = n → 0 ≤ ∑ j ∈ LS f A B, f j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hn
  classical
  by_cases hAB : B ≤ A
  · simp [LS, Finset.Ico_eq_empty_of_le hAB]
  push Not at hAB
  by_cases hB : B - 1 ∈ LS f A B
  · obtain ⟨a0, ha0, ha0s⟩ := (Finset.mem_filter.mp hB).2
    obtain ⟨as, has, hmax⟩ := Finset.exists_max_image (Ico A B)
      (fun a => ∑ r ∈ Ico a B, f r) ⟨A, by simp [hAB]⟩
    have has' := Finset.mem_Ico.mp has
    have ha0' := Finset.mem_Icc.mp ha0
    rw [show B - 1 + 1 = B by ring] at ha0s
    have hT0 : 0 ≤ ∑ r ∈ Ico as B, f r := le_trans ha0s (hmax a0 (Finset.mem_Ico.mpr ⟨ha0'.1, by omega⟩))
    have hsub : Ico as B ⊆ LS f A B := by
      intro l hl
      have hl' := Finset.mem_Ico.mp hl
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hl'.2⟩, as, Finset.mem_Icc.mpr ⟨has'.1, by omega⟩, ?_⟩
      rcases eq_or_lt_of_le (show l + 1 ≤ B by omega) with h | h
      · rw [h]; exact hT0
      · have hsplit := sum_Ico_split (a := as) (b := l + 1) (c := B) (by omega) (by omega) f
        have hle : ∑ r ∈ Ico (l + 1) B, f r ≤ ∑ r ∈ Ico as B, f r :=
          hmax (l + 1) (Finset.mem_Ico.mpr ⟨by omega, h⟩)
        linarith
    have hrest : LS f A B = LS f A as ∪ Ico as B := by
      ext l
      constructor
      · intro hl
        rcases lt_or_ge l as with h | h
        · have h1 := Finset.mem_filter.mp hl
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp h1.1).1, h⟩, h1.2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨h, (Finset.mem_Ico.mp (Finset.mem_filter.mp hl).1).2⟩)
      · intro hl
        rcases Finset.mem_union.mp hl with h | h
        · have h1 := Finset.mem_filter.mp h
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp h1.1).1, by have := Finset.mem_Ico.mp h1.1; omega⟩, h1.2⟩
        · exact hsub h
    have hdisj : Disjoint (LS f A as) (Ico as B) := by
      rw [Finset.disjoint_left]
      intro l hl hl2
      have := Finset.mem_Ico.mp (Finset.mem_filter.mp hl).1
      have := Finset.mem_Ico.mp hl2
      omega
    rw [hrest, Finset.sum_union hdisj]
    have := ih (as - A).toNat (by omega) as rfl
    linarith
  · have hrest : LS f A B = LS f A (B - 1) := by
      ext l
      simp only [LS, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases eq_or_lt_of_le (show l ≤ B - 1 by omega) with h | h
        · subst h
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h1, h2⟩, by simpa using h3⟩) hB
        · exact ⟨⟨h1, h⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩
    rw [hrest]
    exact ih (B - 1 - A).toNat (by omega) (B - 1) rfl

/-- From a nonnegative sum of `D - Θ` to a counting bound. -/
lemma card_le_of_sum_sub_nonneg (D : ℤ → ℝ) (Θ : ℝ) (S : Finset ℤ)
    (h : 0 ≤ ∑ j ∈ S, (D j - Θ)) : Θ * S.card ≤ ∑ j ∈ S, D j := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  linarith

lemma card_Ico_real {a b : ℤ} (hab : a ≤ b) :
    ((Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
  rw [Int.card_Ico]
  have h : (((b - a).toNat : ℕ) : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  exact_mod_cast h

/-- Average of `D` over the closed integer interval `[a,b]`. -/
noncomputable def avg (D : ℤ → ℝ) (a b : ℤ) : ℝ :=
  (∑ r ∈ Ico a (b + 1), D r) / ((b + 1 - a : ℤ) : ℝ)

lemma le_avg_iff (D : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) (Θ : ℝ) :
    Θ ≤ avg D a b ↔ Θ * ((b + 1 - a : ℤ) : ℝ) ≤ ∑ r ∈ Ico a (b + 1), D r := by
  have hpos : (0 : ℝ) < ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast (show (0:ℤ) < b + 1 - a by omega)
  unfold avg
  rw [le_div_iff₀ hpos]

lemma sum_sub_nonneg_iff (D : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) (Θ : ℝ) :
    0 ≤ ∑ r ∈ Ico a (b + 1), (D r - Θ) ↔ Θ * ((b + 1 - a : ℤ) : ℝ) ≤ ∑ r ∈ Ico a (b + 1), D r := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_Ico_real (by omega)]
  constructor <;> intro h <;> linarith

lemma pair_nonempty {A B l : ℤ} (hl : l ∈ Ico A B) : ((Icc A l) ×ˢ (Icc l (B - 1))).Nonempty := by
  have := Finset.mem_Ico.mp hl
  exact ⟨(l, l), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨this.1, le_refl _⟩,
    Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩⟩

/-- Discrete (two-sided) maximal function of `D` at `l`, over intervals inside the window `[A,B)`. -/
noncomputable def M (D : ℤ → ℝ) (A B l : ℤ) : ℝ :=
  if h : l ∈ Ico A B then ((Icc A l) ×ˢ (Icc l (B - 1))).sup' (pair_nonempty h) (fun p => avg D p.1 p.2)
  else 0

lemma avg_le_M (D : ℤ → ℝ) {A B l a b : ℤ} (hAa : A ≤ a) (hal : a ≤ l) (hlb : l ≤ b) (hbB : b < B) :
    avg D a b ≤ M D A B l := by
  have hl : l ∈ Ico A B := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hmem : (a, b) ∈ (Icc A l) ×ˢ (Icc l (B - 1)) :=
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hAa, hal⟩, Finset.mem_Icc.mpr ⟨hlb, by omega⟩⟩
  rw [M, dif_pos hl]
  exact Finset.le_sup' (f := fun p : ℤ × ℤ => avg D p.1 p.2) hmem

lemma exists_M (D : ℤ → ℝ) {A B l : ℤ} (hl : l ∈ Ico A B) :
    ∃ a b, A ≤ a ∧ a ≤ l ∧ l ≤ b ∧ b < B ∧ M D A B l = avg D a b := by
  rw [M, dif_pos hl]
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup' (pair_nonempty hl) (fun p : ℤ × ℤ => avg D p.1 p.2)
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  have h1' := Finset.mem_Icc.mp h1
  have h2' := Finset.mem_Icc.mp h2
  exact ⟨p.1, p.2, h1'.1, h1'.2, h2'.1, by omega, hpe⟩

/-- Weak type (1,1) with constant 2, via the two rising-sun lemmas. -/
theorem weak_type (D : ℤ → ℝ) (hD : ∀ r, 0 ≤ D r) {Θ : ℝ} (hΘ : 0 < Θ) (A B : ℤ) :
    Θ * ((Ico A B).filter (fun l => Θ ≤ M D A B l)).card ≤ 2 * ∑ r ∈ Ico A B, D r := by
  classical
  set f : ℤ → ℝ := fun r => D r - Θ with hf
  have hsub : (Ico A B).filter (fun l => Θ ≤ M D A B l) ⊆ LS f A B ∪ (RS f A B).image (fun j => j - 1) := by
    intro l hl
    obtain ⟨hlw, hlM⟩ := Finset.mem_filter.mp hl
    have hlw' := Finset.mem_Ico.mp hlw
    obtain ⟨a, b, hAa, hal, hlb, hbB, hMe⟩ := exists_M D hlw
    rw [hMe, le_avg_iff D (by omega), ← sum_sub_nonneg_iff D (by omega)] at hlM
    have hsplit := sum_Ico_split (a := a) (b := l + 1) (c := b + 1) (by omega) (by omega) f
    by_cases h1 : 0 ≤ ∑ r ∈ Ico a (l + 1), f r
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hlw, a, Finset.mem_Icc.mpr ⟨hAa, hal⟩, h1⟩)
    · push Not at h1
      have h2 : 0 ≤ ∑ r ∈ Ico (l + 1) (b + 1), f r := by
        have : ∑ r ∈ Ico a (b + 1), f r = ∑ r ∈ Ico a (b + 1), (D r - Θ) := rfl
        linarith
      have hlb' : l + 1 ≤ b := by
        by_contra hc
        have : Ico (l + 1) (b + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
        rw [this, Finset.sum_empty] at h2
        have : ∑ r ∈ Ico a (b + 1), f r = ∑ r ∈ Ico a (b + 1), (D r - Θ) := rfl
        rw [show b + 1 = l + 1 by omega] at hlM hsplit
        rw [Finset.Ico_self, Finset.sum_empty] at hsplit
        linarith
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l + 1, Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, b, Finset.mem_Ico.mpr ⟨hlb', hbB⟩, h2⟩, by ring⟩)
  have hL : Θ * (LS f A B).card ≤ ∑ r ∈ Ico A B, D r := by
    have h := card_le_of_sum_sub_nonneg D Θ (LS f A B) (rising_sun_left f A _ B rfl)
    have : ∑ j ∈ LS f A B, D j ≤ ∑ r ∈ Ico A B, D r :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hD i)
    linarith
  have hR : Θ * (RS f A B).card ≤ ∑ r ∈ Ico A B, D r := by
    have h := card_le_of_sum_sub_nonneg D Θ (RS f A B) (rising_sun_right f B _ A rfl)
    have : ∑ j ∈ RS f A B, D j ≤ ∑ r ∈ Ico A B, D r :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hD i)
    linarith
  have hcard : (((Ico A B).filter (fun l => Θ ≤ M D A B l)).card : ℝ) ≤ (LS f A B).card + (RS f A B).card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (LS f A B) ((RS f A B).image (fun j => j - 1))
    have h3 := Finset.card_image_le (s := RS f A B) (f := fun j => j - 1)
    exact_mod_cast (show _ ≤ _ by omega)
  nlinarith

/-- Splitting `D` at height `Θ/2`: weak bound with the large values only. -/
theorem weak_split (D : ℤ → ℝ) (hD : ∀ r, 0 ≤ D r) {Θ : ℝ} (hΘ : 0 < Θ) (A B : ℤ) :
    Θ * ((Ico A B).filter (fun l => Θ ≤ M D A B l)).card
      ≤ 4 * ∑ r ∈ Ico A B, (if Θ ≤ 2 * D r then D r else 0) := by
  classical
  set D2 : ℤ → ℝ := fun r => if Θ ≤ 2 * D r then D r else 0 with hD2def
  have hD2 : ∀ r, 0 ≤ D2 r := fun r => by simp only [hD2def]; split_ifs <;> linarith [hD r]
  have hsub : (Ico A B).filter (fun l => Θ ≤ M D A B l) ⊆ (Ico A B).filter (fun l => Θ / 2 ≤ M D2 A B l) := by
    intro l hl
    obtain ⟨hlw, hlM⟩ := Finset.mem_filter.mp hl
    refine Finset.mem_filter.mpr ⟨hlw, ?_⟩
    obtain ⟨a, b, hAa, hal, hlb, hbB, hMe⟩ := exists_M D hlw
    rw [hMe, le_avg_iff D (by omega)] at hlM
    have hsplit : ∑ r ∈ Ico a (b + 1), D r
        = ∑ r ∈ Ico a (b + 1), D2 r + ∑ r ∈ Ico a (b + 1), (if Θ ≤ 2 * D r then 0 else D r) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [hD2def]; split_ifs <;> ring
    have hsmall : ∑ r ∈ Ico a (b + 1), (if Θ ≤ 2 * D r then 0 else D r) ≤ Θ / 2 * ((b + 1 - a : ℤ) : ℝ) := by
      calc ∑ r ∈ Ico a (b + 1), (if Θ ≤ 2 * D r then 0 else D r)
          ≤ ∑ r ∈ Ico a (b + 1), Θ / 2 := Finset.sum_le_sum (fun r _ => by
            split_ifs with h
            · linarith
            · push Not at h; linarith)
        _ = Θ / 2 * ((b + 1 - a : ℤ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, card_Ico_real (by omega)]; ring
    have h2 : Θ / 2 ≤ avg D2 a b := by
      rw [le_avg_iff D2 (by omega)]
      linarith
    exact le_trans h2 (avg_le_M D2 hAa hal hlb hbB)
  have hw := weak_type D2 hD2 (half_pos hΘ) A B
  have hc : (((Ico A B).filter (fun l => Θ ≤ M D A B l)).card : ℝ)
      ≤ ((Ico A B).filter (fun l => Θ / 2 ≤ M D2 A B l)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have : ∑ r ∈ Ico A B, D2 r = ∑ r ∈ Ico A B, (if Θ ≤ 2 * D r then D r else 0) := rfl
  nlinarith

/-! ### Layer-cake integrals -/

open MeasureTheory intervalIntegral

lemma ii_ind (g : ℝ → ℝ) (hg : Continuous g) (a u v : ℝ) :
    IntervalIntegrable ((Set.Iic a).indicator g) volume u v := by
  have h := hg.intervalIntegrable (μ := volume) u v
  exact ⟨h.1.indicator measurableSet_Iic, h.2.indicator measurableSet_Iic⟩

lemma int_ind (g : ℝ → ℝ) (hg : Continuous g) {a K : ℝ} (ha : 0 ≤ a) (haK : a ≤ K) :
    ∫ x in (0:ℝ)..K, (Set.Iic a).indicator g x = ∫ x in (0:ℝ)..a, g x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_ind g hg a 0 a) (ii_ind g hg a a K)]
  have h1 : ∫ x in (0:ℝ)..a, (Set.Iic a).indicator g x = ∫ x in (0:ℝ)..a, g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ha] at hx
    exact Set.indicator_of_mem (show x ∈ Set.Iic a from hx.2) g
  have h2 : ∫ x in a..K, (Set.Iic a).indicator g x = ∫ x in a..K, (0:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le haK] at hx
    exact Set.indicator_of_notMem (show x ∉ Set.Iic a from by simp only [Set.mem_Iic, not_le]; exact hx.1) g
  rw [h1, h2, intervalIntegral.integral_zero, add_zero]

lemma int_cube {a K : ℝ} (ha : 0 ≤ a) (haK : a ≤ K) :
    ∫ x in (0:ℝ)..K, (Set.Iic a).indicator (fun x => 3 * x ^ 2) x = a ^ 3 := by
  rw [int_ind _ (by fun_prop) ha haK, intervalIntegral.integral_const_mul, integral_pow]
  ring

lemma int_lin (c : ℝ) {a K : ℝ} (ha : 0 ≤ a) (haK : a ≤ K) :
    ∫ x in (0:ℝ)..K, (Set.Iic a).indicator (fun x => c * x) x = c * a ^ 2 / 2 := by
  rw [int_ind _ (by fun_prop) ha haK, intervalIntegral.integral_const_mul]
  have := integral_pow (a := (0:ℝ)) (b := a) 1
  simp only [pow_one] at this
  rw [this]
  ring

lemma M_nonneg (D : ℤ → ℝ) (hD : ∀ r, 0 ≤ D r) {A B l : ℤ} (hl : l ∈ Ico A B) : 0 ≤ M D A B l := by
  have hl' := Finset.mem_Ico.mp hl
  have h := avg_le_M D (le_refl l |>.trans' hl'.1) (le_refl l) (le_refl l) hl'.2
  have h0 : 0 ≤ avg D l l := by
    unfold avg
    apply div_nonneg (Finset.sum_nonneg (fun r _ => hD r))
    exact_mod_cast (show (0:ℤ) ≤ l + 1 - l by omega)
  linarith

lemma M_le_sum (D : ℤ → ℝ) (hD : ∀ r, 0 ≤ D r) {A B l : ℤ} (hl : l ∈ Ico A B) :
    M D A B l ≤ ∑ r ∈ Ico A B, D r := by
  obtain ⟨a, b, hAa, hal, hlb, hbB, hMe⟩ := exists_M D hl
  rw [hMe]
  unfold avg
  have hS : 0 ≤ ∑ r ∈ Ico a (b + 1), D r := Finset.sum_nonneg (fun r _ => hD r)
  have h1 : (1:ℝ) ≤ ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast (show (1:ℤ) ≤ b + 1 - a by omega)
  calc (∑ r ∈ Ico a (b + 1), D r) / ((b + 1 - a : ℤ) : ℝ) ≤ ∑ r ∈ Ico a (b + 1), D r := div_le_self hS h1
    _ ≤ ∑ r ∈ Ico A B, D r := Finset.sum_le_sum_of_subset_of_nonneg
        (fun r hr => by have := Finset.mem_Ico.mp hr; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        (fun i _ _ => hD i)

/-- **Discrete maximal inequality**, constant 24. -/
theorem maximal_cube (D : ℤ → ℝ) (hD : ∀ r, 0 ≤ D r) (A B : ℤ) :
    ∑ l ∈ Ico A B, (M D A B l) ^ 3 ≤ 24 * ∑ r ∈ Ico A B, (D r) ^ 3 := by
  classical
  set W := Ico A B with hW
  set K : ℝ := 2 * ∑ r ∈ W, D r with hK
  have hS0 : 0 ≤ ∑ r ∈ W, D r := Finset.sum_nonneg (fun r _ => hD r)
  have hm0 : ∀ l ∈ W, 0 ≤ M D A B l := fun l hl => M_nonneg D hD hl
  have hmK : ∀ l ∈ W, M D A B l ≤ K := fun l hl => by have := M_le_sum D hD hl; linarith
  have hDK : ∀ r ∈ W, 2 * D r ≤ K := fun r hr => by
    have := Finset.single_le_sum (fun i _ => hD i) hr; linarith
  -- left side as an integral
  have hL : ∑ l ∈ W, (M D A B l) ^ 3
      = ∫ x in (0:ℝ)..K, ∑ l ∈ W, (Set.Iic (M D A B l)).indicator (fun x => 3 * x ^ 2) x := by
    rw [intervalIntegral.integral_finsetSum (fun l _ => ii_ind _ (by fun_prop) _ _ _)]
    exact Finset.sum_congr rfl (fun l hl => (int_cube (hm0 l hl) (hmK l hl)).symm)
  have hR : ∫ x in (0:ℝ)..K, ∑ r ∈ W, (Set.Iic (2 * D r)).indicator (fun x => 12 * D r * x) x
      = 24 * ∑ r ∈ W, (D r) ^ 3 := by
    rw [intervalIntegral.integral_finsetSum (fun r _ => ii_ind _ (by fun_prop) _ _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [int_lin (12 * D r) (by linarith [hD r]) (hDK r hr)]
    ring
  rw [hL, ← hR]
  have hK0 : 0 ≤ K := by linarith
  apply intervalIntegral.integral_mono_on hK0
  · have := IntervalIntegrable.sum W (f := fun l => (Set.Iic (M D A B l)).indicator (fun x : ℝ => 3 * x ^ 2))
      (μ := volume) (a := 0) (b := K) (fun l _ => ii_ind _ (by fun_prop) _ _ _)
    convert this using 1
    ext u
    simp only [Finset.sum_apply]
  · have := IntervalIntegrable.sum W (f := fun r => (Set.Iic (2 * D r)).indicator (fun x : ℝ => 12 * D r * x))
      (μ := volume) (a := 0) (b := K) (fun r _ => ii_ind _ (by fun_prop) _ _ _)
    convert this using 1
    ext u
    simp only [Finset.sum_apply]
  intro x hx
  have hLx : ∑ l ∈ W, (Set.Iic (M D A B l)).indicator (fun x => 3 * x ^ 2) x
      = 3 * x ^ 2 * (W.filter (fun l => x ≤ M D A B l)).card := by
    simp only [Set.indicator_apply, Set.mem_Iic]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    ring
  have hRx : ∑ r ∈ W, (Set.Iic (2 * D r)).indicator (fun x => 12 * D r * x) x
      = 12 * x * ∑ r ∈ W, (if x ≤ 2 * D r then D r else 0) := by
    simp only [Set.indicator_apply, Set.mem_Iic]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    split_ifs <;> ring
  rw [hLx, hRx]
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · subst h0; simp
  · have hw := weak_split D hD hpos A B
    have hx0 : 0 ≤ 3 * x := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hw hx0]

/-- **Lemma 7.2**, windowed form (constant 36): the maximal function is taken over intervals inside the
window `[A,B)` and the outer sum runs over the window. The article states it for the sequence extended by
zero to `ℤ`, with the outer sum over `ℤ`; that version is stronger. This windowed form is the one used in
Theorem 7.3 (`transfer`), where only indices in the window occur. -/
theorem maximal_cube_36 (D : ℤ → ℝ) (hD : ∀ r, 0 ≤ D r) (A B : ℤ) :
    ∑ l ∈ Ico A B, (M D A B l) ^ 3 ≤ 36 * ∑ r ∈ Ico A B, (D r) ^ 3 := by
  have h := maximal_cube D hD A B
  have h0 : 0 ≤ ∑ r ∈ Ico A B, (D r) ^ 3 := Finset.sum_nonneg (fun r _ => pow_nonneg (hD r) 3)
  linarith

end RvmClock
