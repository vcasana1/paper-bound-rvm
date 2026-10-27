import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lemma 7.5 (third moment of the gaps) — combinatorial part

If the gaps `D_ℓ ∈ [0,1]` satisfy, for every `j` with `2^{j+1} ≤ L`,
`Σ_{D_ℓ ≥ 2^{j+1}/L} D_ℓ ≤ M (j+2)² / 16^j`, then `Σ D_ℓ³ ≤ (4 Σ D_ℓ + 256 M) / L²`.
-/

open Finset

namespace RvmClock

lemma sq_le_four_mul_three_pow (j : ℕ) : ((j : ℝ) + 2) ^ 2 ≤ 4 * 3 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    push_cast
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : ((j : ℝ) + 1 + 2) ^ 2 ≤ 3 * ((j : ℝ) + 2) ^ 2 := by nlinarith
    calc ((j : ℝ) + 1 + 2) ^ 2 ≤ 3 * ((j : ℝ) + 2) ^ 2 := this
      _ ≤ 3 * (4 * 3 ^ j) := by linarith
      _ = 4 * 3 ^ (j + 1) := by ring

lemma geom_sum_bound (J : ℕ) : ∑ j ∈ range J, ((j : ℝ) + 2) ^ 2 / 4 ^ j ≤ 16 := by
  calc ∑ j ∈ range J, ((j : ℝ) + 2) ^ 2 / 4 ^ j ≤ ∑ j ∈ range J, 4 * (3 / 4 : ℝ) ^ j := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [div_le_iff₀ (by positivity), div_pow, mul_assoc, div_mul_cancel₀ _ (by positivity)]
        exact sq_le_four_mul_three_pow j
    _ = 4 * ∑ j ∈ range J, (3 / 4 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 4 * 4 := by
        gcongr
        rw [geom_sum_eq (by norm_num : (3/4 : ℝ) ≠ 1)]
        have : 0 ≤ (3 / 4 : ℝ) ^ J := by positivity
        rw [div_le_iff_of_neg (by norm_num)]
        linarith
    _ = 16 := by norm_num

/-- The dyadic class of a gap `D ≥ 2/L`: `2^{j+1}/L ≤ D < 2^{j+2}/L` with `j < ⌈L⌉₊`. -/
lemma exists_dyadic {D L : ℝ} (hL : 1 ≤ L) (hD1 : D ≤ 1) (hD2 : 2 / L ≤ D) :
    ∃ j : ℕ, j < ⌈L⌉₊ ∧ (2 : ℝ) ^ (j + 1) / L ≤ D ∧ D < (2 : ℝ) ^ (j + 2) / L := by
  have hL0 : 0 < L := by linarith
  have hex : ∃ j : ℕ, D < (2 : ℝ) ^ (j + 2) / L := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D * L) (by norm_num : (1:ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hL0]
    calc D * L < 2 ^ n := hn
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  classical
  set j := Nat.find hex with hj
  have hjspec : D < (2 : ℝ) ^ (j + 2) / L := Nat.find_spec hex
  have hlow : (2 : ℝ) ^ (j + 1) / L ≤ D := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; simpa using hD2
    · have := Nat.find_min hex (show j - 1 < j by omega)
      push Not at this
      rw [show j - 1 + 2 = j + 1 by omega] at this
      exact this
  refine ⟨j, ?_, hlow, hjspec⟩
  have h1 : (2 : ℝ) ^ (j + 1) ≤ L := by
    have := (div_le_iff₀ hL0).mp hlow
    nlinarith
  have h2 : ((j : ℝ) + 1) < (2 : ℝ) ^ (j + 1) := by
    have := Nat.lt_two_pow_self (n := j + 1)
    exact_mod_cast this
  have h3 : (j : ℝ) + 1 ≤ ⌈L⌉₊ := by
    have := Nat.le_ceil L
    linarith
  have : (j : ℝ) < ⌈L⌉₊ := by linarith
  exact_mod_cast this

/-- **Lemma 7.5, combinatorial core.** -/
theorem sum_cube_le {ι : Type*} (Λ : Finset ι) (D : ι → ℝ) (hD0 : ∀ ℓ ∈ Λ, 0 ≤ D ℓ)
    (hD1 : ∀ ℓ ∈ Λ, D ℓ ≤ 1) {L M : ℝ} (hL : 1 ≤ L) (hM : 0 ≤ M)
    (hyp : ∀ j : ℕ, (2 : ℝ) ^ (j + 1) ≤ L →
      ∑ ℓ ∈ Λ.filter (fun ℓ => (2 : ℝ) ^ (j + 1) / L ≤ D ℓ), D ℓ ≤ M * ((j : ℝ) + 2) ^ 2 / 16 ^ j) :
    ∑ ℓ ∈ Λ, D ℓ ^ 3 ≤ (4 * ∑ ℓ ∈ Λ, D ℓ + 256 * M) / L ^ 2 := by
  classical
  have hL0 : 0 < L := by linarith
  set J := ⌈L⌉₊
  -- pointwise bound
  have hpt : ∀ ℓ ∈ Λ, D ℓ ^ 3 ≤ 4 * D ℓ / L ^ 2 +
      ∑ j ∈ range J, 16 * 4 ^ j / L ^ 2 * (if (2 : ℝ) ^ (j + 1) / L ≤ D ℓ then D ℓ else 0) := by
    intro ℓ hℓ
    have h0 := hD0 ℓ hℓ
    have hsum0 : 0 ≤ ∑ j ∈ range J, 16 * 4 ^ j / L ^ 2 * (if (2 : ℝ) ^ (j + 1) / L ≤ D ℓ then D ℓ else 0) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (by split_ifs <;> linarith))
    by_cases hsmall : D ℓ < 2 / L
    · have : D ℓ ^ 3 ≤ 4 * D ℓ / L ^ 2 := by
        have h2 : D ℓ ^ 2 ≤ 4 / L ^ 2 := by
          have := pow_le_pow_left₀ h0 hsmall.le 2
          rw [div_pow] at this; norm_num at this; linarith
        calc D ℓ ^ 3 = D ℓ * D ℓ ^ 2 := by ring
          _ ≤ D ℓ * (4 / L ^ 2) := mul_le_mul_of_nonneg_left h2 h0
          _ = 4 * D ℓ / L ^ 2 := by ring
      linarith
    · push Not at hsmall
      obtain ⟨j, hjJ, hlo, hhi⟩ := exists_dyadic hL (hD1 ℓ hℓ) hsmall
      have hterm : D ℓ ^ 3 ≤ 16 * 4 ^ j / L ^ 2 * (if (2 : ℝ) ^ (j + 1) / L ≤ D ℓ then D ℓ else 0) := by
        rw [if_pos hlo]
        have h2 : D ℓ ^ 2 ≤ 16 * 4 ^ j / L ^ 2 := by
          have := pow_le_pow_left₀ h0 hhi.le 2
          rw [div_pow, ← pow_mul] at this
          rw [show (2 : ℝ) ^ ((j + 2) * 2) = 16 * 4 ^ j by
            rw [show (j + 2) * 2 = 2 * j + 4 by ring, pow_add, pow_mul]; norm_num; ring] at this
          exact this
        calc D ℓ ^ 3 = D ℓ ^ 2 * D ℓ := by ring
          _ ≤ 16 * 4 ^ j / L ^ 2 * D ℓ := mul_le_mul_of_nonneg_right h2 h0
      have hle := Finset.single_le_sum (f := fun j => 16 * 4 ^ j / L ^ 2 *
        (if (2 : ℝ) ^ (j + 1) / L ≤ D ℓ then D ℓ else 0))
        (fun j _ => mul_nonneg (by positivity) (by split_ifs <;> linarith)) (Finset.mem_range.mpr hjJ)
      have : 0 ≤ 4 * D ℓ / L ^ 2 := by positivity
      linarith
  -- sum the pointwise bound
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have hj : ∀ j ∈ range J, ∑ ℓ ∈ Λ, 16 * 4 ^ j / L ^ 2 * (if (2 : ℝ) ^ (j + 1) / L ≤ D ℓ then D ℓ else 0)
      ≤ 16 * M / L ^ 2 * (((j : ℝ) + 2) ^ 2 / 4 ^ j) := by
    intro j _
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    by_cases hjL : (2 : ℝ) ^ (j + 1) ≤ L
    · have h := hyp j hjL
      calc 16 * 4 ^ j / L ^ 2 * ∑ ℓ ∈ Λ.filter (fun ℓ => (2 : ℝ) ^ (j + 1) / L ≤ D ℓ), D ℓ
          ≤ 16 * 4 ^ j / L ^ 2 * (M * ((j : ℝ) + 2) ^ 2 / 16 ^ j) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 16 * M / L ^ 2 * (((j : ℝ) + 2) ^ 2 / 4 ^ j) := by
            rw [show (16 : ℝ) ^ j = 4 ^ j * 4 ^ j by rw [← mul_pow]; norm_num]
            field_simp
    · push Not at hjL
      have hempty : Λ.filter (fun ℓ => (2 : ℝ) ^ (j + 1) / L ≤ D ℓ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ hℓ hc
        have : 1 < (2 : ℝ) ^ (j + 1) / L := by rw [one_lt_div hL0]; exact hjL
        linarith [hD1 ℓ hℓ]
      rw [hempty, Finset.sum_empty, mul_zero]
      positivity
  have hJ := Finset.sum_le_sum hj
  rw [← Finset.mul_sum] at hJ
  have hg := geom_sum_bound J
  have h16 : 16 * M / L ^ 2 * ∑ j ∈ range J, ((j : ℝ) + 2) ^ 2 / 4 ^ j ≤ 16 * M / L ^ 2 * 16 :=
    mul_le_mul_of_nonneg_left hg (by positivity)
  have e12 : ∑ ℓ ∈ Λ, 4 * D ℓ / L ^ 2 = 4 * (∑ ℓ ∈ Λ, D ℓ) / L ^ 2 := by
    simp only [div_eq_mul_inv]; rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [e12] at hsum
  rw [add_div]
  have e3 : 16 * M / L ^ 2 * 16 = 256 * M / L ^ 2 := by ring
  linarith

/-! ### Abstract ordinates and their counting function -/

open MeasureTheory Set

/-- A nondecreasing unbounded sequence of ordinates `γ_0 ≤ γ_1 ≤ ⋯` (listed with multiplicity). -/
structure Ordinates where
  γ : ℕ → ℝ
  mono : Monotone γ
  unbounded : ∀ t : ℝ, ∃ k, t < γ k

namespace Ordinates

variable (Z : Ordinates)

/-- `N(t) = #{k : γ_k ≤ t}`. -/
noncomputable def N (t : ℝ) : ℕ := by
  classical exact Nat.find (Z.unbounded t)

lemma lt_N_iff (t : ℝ) (k : ℕ) : k < Z.N t ↔ Z.γ k ≤ t := by
  classical
  unfold N
  constructor
  · intro h
    have := Nat.find_min (Z.unbounded t) h
    push Not at this; exact this
  · intro h
    by_contra hc
    push Not at hc
    have h1 := Nat.find_spec (Z.unbounded t)
    have h2 := Z.mono hc
    linarith

lemma N_eq_of_mem {ℓ : ℕ} {t : ℝ} (h1 : Z.γ ℓ ≤ t) (h2 : t < Z.γ (ℓ + 1)) : Z.N t = ℓ + 1 := by
  have a : ℓ < Z.N t := (Z.lt_N_iff t ℓ).mpr h1
  have b : ¬ (ℓ + 1 < Z.N t) := fun h => absurd ((Z.lt_N_iff t (ℓ + 1)).mp h) (not_le.mpr h2)
  omega

/-- Gaps `D_ℓ = γ_{ℓ+1} − γ_ℓ`. -/
def D (ℓ : ℕ) : ℝ := Z.γ (ℓ + 1) - Z.γ ℓ

lemma D_nonneg (ℓ : ℕ) : 0 ≤ Z.D ℓ := by
  unfold D; linarith [Z.mono (show ℓ ≤ ℓ + 1 by omega)]

/-- The set `𝒜_h = {t ∈ [T, 4T] : N(t+h) = N(t)}`. -/
def Aset (T h : ℝ) : Set ℝ := {t ∈ Icc T (4 * T) | Z.N (t + h) = Z.N t}

/-- **Lemma 7.5, disjoint intervals**: if `D_ℓ ≤ 1` on `Λ ⊆ {ℓ : T < γ_ℓ ≤ 2T}`, then
`Σ_{ℓ ∈ Λ, D_ℓ ≥ 2h} D_ℓ ≤ 2 |𝒜_h|`. -/
theorem sum_D_le_two_vol {T h : ℝ} (hT : 1 ≤ T) (hh : 0 < h) (Λ : Finset ℕ)
    (hΛ : ∀ ℓ ∈ Λ, T < Z.γ ℓ ∧ Z.γ ℓ ≤ 2 * T) (hD1 : ∀ ℓ ∈ Λ, Z.D ℓ ≤ 1) :
    ∑ ℓ ∈ Λ.filter (fun ℓ => 2 * h ≤ Z.D ℓ), Z.D ℓ ≤ 2 * volume.real (Z.Aset T h) := by
  classical
  set Λ' := Λ.filter (fun ℓ => 2 * h ≤ Z.D ℓ)
  set I : ℕ → Set ℝ := fun ℓ => Ioo (Z.γ ℓ) (Z.γ (ℓ + 1) - h)
  have hsub : ∀ ℓ ∈ Λ', I ℓ ⊆ Z.Aset T h := by
    intro ℓ hℓ t ht
    obtain ⟨hℓΛ, _⟩ := Finset.mem_filter.mp hℓ
    obtain ⟨hT1, hT2⟩ := hΛ ℓ hℓΛ
    have hd := hD1 ℓ hℓΛ
    unfold D at hd
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have ht1 : Z.γ ℓ < t := ht.1
    have ht2 : t < Z.γ (ℓ + 1) - h := ht.2
    rw [Z.N_eq_of_mem (ℓ := ℓ) (t := t + h) (by linarith) (by linarith),
      Z.N_eq_of_mem (ℓ := ℓ) (t := t) ht1.le (by linarith)]
  have hdisj : (Λ' : Set ℕ).PairwiseDisjoint I := by
    intro ℓ _ ℓ' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro t h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := Z.mono (show ℓ + 1 ≤ ℓ' by omega)
      linarith [h1.2, h2.1]
    · have := Z.mono (show ℓ' + 1 ≤ ℓ by omega)
      linarith [h1.1, h2.2]
  have hU : (⋃ ℓ ∈ Λ', I ℓ) ⊆ Z.Aset T h := Set.iUnion₂_subset hsub
  have hfinA : volume (Z.Aset T h) ≠ ⊤ :=
    measure_ne_top_of_subset (fun t ht => ht.1) (by simp)
  have hvolU : volume (⋃ ℓ ∈ Λ', I ℓ) = ∑ ℓ ∈ Λ', volume (I ℓ) :=
    measure_biUnion_finset hdisj (fun ℓ _ => measurableSet_Ioo)
  have hI : ∀ ℓ ∈ Λ', volume (I ℓ) = ENNReal.ofReal (Z.D ℓ - h) := by
    intro ℓ _; simp only [I, Real.volume_Ioo, D]; congr 1; ring
  have h1 : ∑ ℓ ∈ Λ', (Z.D ℓ - h) ≤ volume.real (Z.Aset T h) := by
    have hle := measure_mono (μ := volume) hU
    rw [hvolU, Finset.sum_congr rfl hI] at hle
    have := ENNReal.toReal_mono hfinA hle
    rw [ENNReal.toReal_sum (fun ℓ _ => ENNReal.ofReal_ne_top)] at this
    have e : ∀ ℓ ∈ Λ', (ENNReal.ofReal (Z.D ℓ - h)).toReal = Z.D ℓ - h := by
      intro ℓ hℓ
      have := (Finset.mem_filter.mp hℓ).2
      exact ENNReal.toReal_ofReal (by linarith)
    rw [Finset.sum_congr rfl e] at this
    exact this
  have h2 : ∑ ℓ ∈ Λ', Z.D ℓ ≤ 2 * ∑ ℓ ∈ Λ', (Z.D ℓ - h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
    have := (Finset.mem_filter.mp hℓ).2
    linarith
  linarith

end Ordinates

end RvmClock
