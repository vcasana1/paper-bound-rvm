import PaperMath.Papers.RvmClock.Maximal
import PaperMath.Papers.RvmClock.Bathtub
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Theorem 7.3 (sublevel transfer) of *The Riemann–von Mangoldt clock*, v6

Setting.  `γ : ℤ → ℝ` is monotone; `ℓ₀ ≤ ℓ₁` and `a < b` with
`γ ℓ₀ ≤ a < γ (ℓ₀+1)` and `γ ℓ₁ ≤ b < γ (ℓ₁+1)`.  Then `{k : a < γ k ≤ b} = (ℓ₀, ℓ₁]`,
and on `(a, b]` the counting function is `N t = ℓ₀ + #{k ∈ (ℓ₀,ℓ₁] : γ k ≤ t}`.
-/

open Finset MeasureTheory Set

namespace RvmClock

/-- Counting function inside the window. -/
noncomputable def Ncnt (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) (t : ℝ) : ℤ :=
  ℓ₀ + ((Finset.Ioc ℓ₀ ℓ₁).filter (fun k => γ k ≤ t)).card

lemma le_Ncnt_iff {γ : ℤ → ℝ} (hγ : Monotone γ) {ℓ₀ ℓ₁ k : ℤ} (hk : k ∈ Finset.Ioc ℓ₀ ℓ₁) (t : ℝ) :
    k ≤ Ncnt γ ℓ₀ ℓ₁ t ↔ γ k ≤ t := by
  have hk' := Finset.mem_Ioc.mp hk
  unfold Ncnt
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hsub : (Finset.Ioc ℓ₀ ℓ₁).filter (fun j => γ j ≤ t) ⊆ Finset.Ioc ℓ₀ (k - 1) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
      have hj1' := Finset.mem_Ioc.mp hj1
      refine Finset.mem_Ioc.mpr ⟨hj1'.1, ?_⟩
      by_contra hc2
      push Not at hc2
      have := hγ (show k ≤ j by omega)
      linarith
    have hc := Finset.card_le_card hsub
    rw [Int.card_Ioc] at hc
    omega
  · intro h
    have hsub : Finset.Ioc ℓ₀ k ⊆ (Finset.Ioc ℓ₀ ℓ₁).filter (fun j => γ j ≤ t) := by
      intro j hj
      have hj' := Finset.mem_Ioc.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hj'.1, by omega⟩, le_trans (hγ hj'.2) h⟩
    have hc := Finset.card_le_card hsub
    rw [Int.card_Ioc] at hc
    omega

lemma Ncnt_bounds (γ : ℤ → ℝ) {ℓ₀ ℓ₁ : ℤ} (h01 : ℓ₀ ≤ ℓ₁) (t : ℝ) :
    ℓ₀ ≤ Ncnt γ ℓ₀ ℓ₁ t ∧ Ncnt γ ℓ₀ ℓ₁ t ≤ ℓ₁ := by
  unfold Ncnt
  have hc := Finset.card_le_card (Finset.filter_subset (fun k => γ k ≤ t) (Finset.Ioc ℓ₀ ℓ₁))
  rw [Int.card_Ioc] at hc
  omega

/-- Window hypotheses. -/
structure Window (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) (a b : ℝ) : Prop where
  mono : Monotone γ
  h01 : ℓ₀ ≤ ℓ₁
  hab : a < b
  ha0 : γ ℓ₀ ≤ a
  ha1 : a < γ (ℓ₀ + 1)
  hb0 : γ ℓ₁ ≤ b
  hb1 : b < γ (ℓ₁ + 1)

lemma Window.mem_k {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b)
    {k : ℤ} (hk : k ∈ Finset.Ioc ℓ₀ ℓ₁) : a < γ k ∧ γ k ≤ b := by
  have hk' := Finset.mem_Ioc.mp hk
  exact ⟨lt_of_lt_of_le W.ha1 (W.mono (by omega)), le_trans (W.mono hk'.2) W.hb0⟩

lemma Window.Ncnt_mem {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b)
    {t : ℝ} (ht : t ∈ Ioc a b) :
    γ (Ncnt γ ℓ₀ ℓ₁ t) ≤ t ∧ t < γ (Ncnt γ ℓ₀ ℓ₁ t + 1) := by
  obtain ⟨hn0, hn1⟩ := Ncnt_bounds γ W.h01 t
  set n := Ncnt γ ℓ₀ ℓ₁ t with hn
  constructor
  · rcases eq_or_lt_of_le hn0 with h | h
    · rw [← h]; exact le_trans W.ha0 ht.1.le
    · exact (le_Ncnt_iff W.mono (Finset.mem_Ioc.mpr ⟨h, hn1⟩) t).mp le_rfl
  · rcases eq_or_lt_of_le hn1 with h | h
    · rw [h]; exact lt_of_le_of_lt ht.2 W.hb1
    · have hk : n + 1 ∈ Finset.Ioc ℓ₀ ℓ₁ := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      by_contra hc
      push Not at hc
      have := (le_Ncnt_iff W.mono hk t).mpr hc
      omega

lemma Ncnt_mono (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) : Monotone (Ncnt γ ℓ₀ ℓ₁) := by
  intro s t hst
  unfold Ncnt
  have : (Finset.Ioc ℓ₀ ℓ₁).filter (fun k => γ k ≤ s) ⊆ (Finset.Ioc ℓ₀ ℓ₁).filter (fun k => γ k ≤ t) :=
    Finset.monotone_filter_right _ (fun k _ hk => le_trans hk hst)
  have := Finset.card_le_card this
  omega

lemma Ncnt_measurable (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) : Measurable (Ncnt γ ℓ₀ ℓ₁) :=
  (Ncnt_mono γ ℓ₀ ℓ₁).measurable

/-- `x_k^f = a + |{t ∈ (a,b] : f t < k - 1/2}|`. -/
noncomputable def xk (f : ℝ → ℝ) (a b : ℝ) (k : ℤ) : ℝ :=
  a + volume.real (Ioc a b ∩ {t | f t < (k : ℝ) - 1 / 2})

/-- `U_k = {t ∈ [c,b] : f t < k - 1/2}` and `V_k = {t ∈ (a,c) : f t ≥ k - 1/2}`, with `c = γ_k`. -/
def Uk (f : ℝ → ℝ) (b c : ℝ) (k : ℤ) : Set ℝ := Icc c b ∩ {t | f t < (k : ℝ) - 1 / 2}
def Vk (f : ℝ → ℝ) (a c : ℝ) (k : ℤ) : Set ℝ := Ioo a c ∩ {t | (k : ℝ) - 1 / 2 ≤ f t}

lemma measurableSet_Uk {f : ℝ → ℝ} (hf : Measurable f) (b c : ℝ) (k : ℤ) : MeasurableSet (Uk f b c k) :=
  measurableSet_Icc.inter (measurableSet_lt hf measurable_const)
lemma measurableSet_Vk {f : ℝ → ℝ} (hf : Measurable f) (a c : ℝ) (k : ℤ) : MeasurableSet (Vk f a c k) :=
  measurableSet_Ioo.inter (measurableSet_le measurable_const hf)

lemma xk_decomp {f : ℝ → ℝ} (hf : Measurable f) {a b c : ℝ} (hac : a < c) (hcb : c ≤ b) (k : ℤ) :
    xk f a b k = c + volume.real (Uk f b c k) - volume.real (Vk f a c k) := by
  set F : Set ℝ := {t | f t < (k : ℝ) - 1 / 2} with hF
  have hFm : MeasurableSet F := measurableSet_lt hf measurable_const
  have hsplit : Ioc a b ∩ F = (Ioo a c ∩ F) ∪ (Icc c b ∩ F) := by
    rw [← Set.union_inter_distrib_right, Set.Ioo_union_Icc_eq_Ioc hac hcb]
  have hdisj : Disjoint (Ioo a c ∩ F) (Icc c b ∩ F) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.1.1 (not_le.mpr h1.1.2)
  have hu : volume.real (Ioc a b ∩ F) = volume.real (Ioo a c ∩ F) + volume.real (Icc c b ∩ F) := by
    rw [hsplit]
    exact measureReal_union hdisj (measurableSet_Icc.inter hFm)
      (measure_ne_top_of_subset Set.inter_subset_left (by simp))
      (measure_ne_top_of_subset Set.inter_subset_left (by simp))
  have hV : Ioo a c \ F = Vk f a c k := by
    ext t; simp [Vk, hF, not_lt]
  have hio : volume.real (Ioo a c ∩ F) + volume.real (Vk f a c k) = c - a := by
    rw [← hV, measureReal_inter_add_sdiff hFm (by simp), Real.volume_real_Ioo_of_le hac.le]
  unfold xk
  rw [hu]
  simp only [Uk]
  linarith

lemma sq_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : (u - v) ^ 2 ≤ u ^ 2 + v ^ 2 := by
  nlinarith [mul_nonneg hu hv]

/-- Per-index bathtub estimate: `(x_k - c)² ≤ 2 ∫_{(a,b]} 1_{E_k} |t - c|`, `E_k = U_k ∪ V_k`. -/
lemma xk_sq_le {f : ℝ → ℝ} (hf : Measurable f) {a b c : ℝ} (hac : a < c) (hcb : c ≤ b) (k : ℤ) :
    (xk f a b k - c) ^ 2 ≤ 2 * ∫ t in Ioc a b, (Uk f b c k ∪ Vk f a c k).indicator (fun t => |t - c|) t := by
  have hUm := measurableSet_Uk hf b c k
  have hVm := measurableSet_Vk hf a c k
  have hU := bathtub_right hUm (show Uk f b c k ⊆ Icc c b from Set.inter_subset_left)
  have hV := bathtub_left hVm (show Vk f a c k ⊆ Icc a c from fun t ht => Set.Ioo_subset_Icc_self ht.1)
  have hUi : ∫ x in Uk f b c k, (x - c) = ∫ x in Uk f b c k, |x - c| :=
    setIntegral_congr_fun hUm (fun x hx => (abs_of_nonneg (by linarith [hx.1.1])).symm)
  have hVi : ∫ x in Vk f a c k, (c - x) = ∫ x in Vk f a c k, |x - c| :=
    setIntegral_congr_fun hVm (fun x hx => by rw [abs_sub_comm]; exact (abs_of_nonneg (by linarith [hx.1.2])).symm)
  have hcont : Continuous fun x : ℝ => |x - c| := by fun_prop
  have hdisj : Disjoint (Uk f b c k) (Vk f a c k) := by
    rw [Set.disjoint_left]; intro t h1 h2; exact absurd h1.1.1 (not_le.mpr h2.1.2)
  have hsubU : Uk f b c k ⊆ Icc a b := fun t ht => ⟨by linarith [ht.1.1], ht.1.2⟩
  have hsubV : Vk f a c k ⊆ Icc a b := fun t ht => ⟨ht.1.1.le, by linarith [ht.1.2]⟩
  have hunion : ∫ x in Uk f b c k ∪ Vk f a c k, |x - c|
      = (∫ x in Uk f b c k, |x - c|) + ∫ x in Vk f a c k, |x - c| :=
    setIntegral_union hdisj hVm (hcont.integrableOn_Icc.mono_set hsubU) (hcont.integrableOn_Icc.mono_set hsubV)
  have hind : ∫ t in Ioc a b, (Uk f b c k ∪ Vk f a c k).indicator (fun t => |t - c|) t
      = ∫ x in Uk f b c k ∪ Vk f a c k, |x - c| := by
    have hss : Uk f b c k ∪ Vk f a c k ⊆ Ioc a b := by
      intro t ht
      rcases ht with ht | ht
      · exact ⟨by linarith [ht.1.1], ht.1.2⟩
      · exact ⟨ht.1.1, by linarith [ht.1.2]⟩
    rw [setIntegral_indicator (hUm.union hVm), Set.inter_eq_right.mpr hss]
  rw [xk_decomp hf hac hcb k]
  have h1 := sq_sub_le (u := volume.real (Uk f b c k)) (v := volume.real (Vk f a c k)) measureReal_nonneg measureReal_nonneg
  rw [hind, hunion, ← hUi, ← hVi]
  have : c + volume.real (Uk f b c k) - volume.real (Vk f a c k) - c
      = volume.real (Uk f b c k) - volume.real (Vk f a c k) := by ring
  rw [this]
  linarith

/-- Gaps `D_ℓ = γ_{ℓ+1} - γ_ℓ`. -/
def Dg (γ : ℤ → ℝ) (ℓ : ℤ) : ℝ := γ (ℓ + 1) - γ ℓ

lemma Dg_nonneg {γ : ℤ → ℝ} (hγ : Monotone γ) (ℓ : ℤ) : 0 ≤ Dg γ ℓ := by
  unfold Dg; linarith [hγ (show ℓ ≤ ℓ + 1 by omega)]

lemma tele (γ : ℤ → ℝ) {n k : ℤ} (hnk : n ≤ k) : ∑ r ∈ Finset.Ico n k, Dg γ r = γ k - γ n := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k = n + d := ⟨(k - n).toNat, by omega⟩
  subst hd
  induction d with
  | zero => simp
  | succ d ih =>
    have e : n + ((d + 1 : ℕ) : ℤ) = (n + d) + 1 := by push_cast; ring
    rw [e, sum_Ico_split (a := n) (b := n + d) (c := n + d + 1) (by omega) (by omega), ih (by omega)]
    have : Finset.Ico (n + (d : ℤ)) (n + d + 1) = {n + (d : ℤ)} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [this, Finset.sum_singleton]
    unfold Dg; ring

lemma sum_eq_avg_mul (D : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    ∑ r ∈ Finset.Ico a (b + 1), D r = avg D a b * ((b + 1 - a : ℤ) : ℝ) := by
  have hpos : (0 : ℝ) < ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast (show (0:ℤ) < b + 1 - a by omega)
  unfold avg
  rw [div_mul_cancel₀ _ hpos.ne']

/-- `E_k`, `q_f` and the maximal function evaluated at `N(t)`. -/
def Ek (f : ℝ → ℝ) (a b : ℝ) (γ : ℤ → ℝ) (k : ℤ) : Set ℝ := Uk f b (γ k) k ∪ Vk f a (γ k) k

noncomputable def qf (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  |((⌊f t + 1 / 2⌋ - Ncnt γ ℓ₀ ℓ₁ t : ℤ) : ℝ)|

noncomputable def Mn (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) (t : ℝ) : ℝ :=
  M (Dg γ) ℓ₀ (ℓ₁ + 1) (Ncnt γ ℓ₀ ℓ₁ t)

lemma Mn_nonneg {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b) (t : ℝ) :
    0 ≤ Mn γ ℓ₀ ℓ₁ t := by
  obtain ⟨h0, h1⟩ := Ncnt_bounds γ W.h01 t
  exact M_nonneg _ (Dg_nonneg W.mono) (Finset.mem_Ico.mpr ⟨h0, by omega⟩)

/-- Pointwise estimate: `Σ_k 1_{E_k}(t) |t - γ_k| ≤ q(t)² M_{N(t)}`. -/
lemma pointwise {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b) (f : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Ioc a b) :
    ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (Ek f a b γ k).indicator (fun t => |t - γ k|) t
      ≤ qf γ ℓ₀ ℓ₁ f t * qf γ ℓ₀ ℓ₁ f t * Mn γ ℓ₀ ℓ₁ t := by
  classical
  set n := Ncnt γ ℓ₀ ℓ₁ t with hn
  set m := ⌊f t + 1 / 2⌋ with hm
  set q := qf γ ℓ₀ ℓ₁ f t with hq
  set Mt := Mn γ ℓ₀ ℓ₁ t with hMt
  have hq' : q = |((m - n : ℤ) : ℝ)| := rfl
  obtain ⟨hn0, hn1⟩ := Ncnt_bounds γ W.h01 t
  obtain ⟨hγn, hγn1⟩ := W.Ncnt_mem ht
  have hM0 : 0 ≤ Mt := Mn_nonneg W t
  have hq0 : 0 ≤ q := abs_nonneg _
  have hqge1 : ((n - m : ℤ) : ℝ) ≤ q := by
    rw [hq']; rw [show ((n - m : ℤ) : ℝ) = -((m - n : ℤ) : ℝ) by push_cast; ring]; exact neg_le_abs _
  have hqge2 : ((m - n : ℤ) : ℝ) ≤ q := le_abs_self _
  set I := Finset.Ioc (min m n) (max m n) with hI
  have hterm : ∀ k ∈ Finset.Ioc ℓ₀ ℓ₁, (Ek f a b γ k).indicator (fun t => |t - γ k|) t
      ≤ if k ∈ I then q * Mt else 0 := by
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    by_cases htE : t ∈ Ek f a b γ k
    · rw [Set.indicator_of_mem htE]
      rcases htE with hU | hV
      · -- t ∈ U_k : γ_k ≤ t, f t < k - 1/2
        have hkn : k ≤ n := (le_Ncnt_iff W.mono hk t).mpr hU.1.1
        have hmk : m < k := Int.floor_lt.mpr (by have := hU.2; simp only [Set.mem_setOf_eq] at this; linarith)
        rw [if_pos (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)]
        rw [abs_of_nonneg (by linarith [hU.1.1])]
        have h1 : t - γ k ≤ γ (n + 1) - γ k := by linarith
        rw [← tele γ (show k ≤ n + 1 by omega), sum_eq_avg_mul (Dg γ) (show k ≤ n by omega)] at h1
        have h2 := avg_le_M (Dg γ) (A := ℓ₀) (B := ℓ₁ + 1) (l := n) (show ℓ₀ ≤ k by omega) hkn le_rfl (by omega)
        have h3 : ((n + 1 - k : ℤ) : ℝ) ≤ q := by
          have : ((n + 1 - k : ℤ) : ℝ) ≤ ((n - m : ℤ) : ℝ) := by exact_mod_cast (show n + 1 - k ≤ n - m by omega)
          linarith
        have h4 : (0 : ℝ) ≤ ((n + 1 - k : ℤ) : ℝ) := by exact_mod_cast (show (0:ℤ) ≤ n + 1 - k by omega)
        calc t - γ k ≤ avg (Dg γ) k n * ((n + 1 - k : ℤ) : ℝ) := h1
          _ ≤ Mt * ((n + 1 - k : ℤ) : ℝ) := mul_le_mul_of_nonneg_right h2 h4
          _ ≤ Mt * q := mul_le_mul_of_nonneg_left h3 hM0
          _ = q * Mt := by ring
      · -- t ∈ V_k : t < γ_k, f t ≥ k - 1/2
        have hnk : n < k := by
          by_contra hc; push Not at hc
          have := (le_Ncnt_iff W.mono hk t).mp hc
          linarith [hV.1.2]
        have hkm : k ≤ m := Int.le_floor.mpr (by have := hV.2; simp only [Set.mem_setOf_eq] at this; linarith)
        rw [if_pos (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)]
        rw [abs_of_neg (by linarith [hV.1.2])]
        have h1 : -(t - γ k) ≤ γ k - γ n := by linarith
        rw [← tele γ (show n ≤ k by omega)] at h1
        have h5 : ∑ r ∈ Finset.Ico n k, Dg γ r = avg (Dg γ) n (k - 1) * ((k - 1 + 1 - n : ℤ) : ℝ) := by
          rw [show Finset.Ico n k = Finset.Ico n (k - 1 + 1) by congr 1; ring]
          exact sum_eq_avg_mul _ (by omega)
        rw [h5] at h1
        have h2 := avg_le_M (Dg γ) (A := ℓ₀) (B := ℓ₁ + 1) (l := n) hn0 le_rfl (show n ≤ k - 1 by omega) (by omega)
        have h3 : ((k - 1 + 1 - n : ℤ) : ℝ) ≤ q := by
          have : ((k - 1 + 1 - n : ℤ) : ℝ) ≤ ((m - n : ℤ) : ℝ) := by exact_mod_cast (show k - 1 + 1 - n ≤ m - n by omega)
          linarith
        have h4 : (0 : ℝ) ≤ ((k - 1 + 1 - n : ℤ) : ℝ) := by exact_mod_cast (show (0:ℤ) ≤ k - 1 + 1 - n by omega)
        calc -(t - γ k) ≤ avg (Dg γ) n (k - 1) * ((k - 1 + 1 - n : ℤ) : ℝ) := h1
          _ ≤ Mt * ((k - 1 + 1 - n : ℤ) : ℝ) := mul_le_mul_of_nonneg_right h2 h4
          _ ≤ Mt * q := mul_le_mul_of_nonneg_left h3 hM0
          _ = q * Mt := by ring
    · rw [Set.indicator_of_notMem htE]
      split_ifs
      · exact mul_nonneg hq0 hM0
      · exact le_rfl
  calc ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (Ek f a b γ k).indicator (fun t => |t - γ k|) t
      ≤ ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (if k ∈ I then q * Mt else 0) := Finset.sum_le_sum hterm
    _ = ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁ ∩ I, q * Mt := Finset.sum_ite_mem _ _ _
    _ ≤ ∑ k ∈ I, q * Mt := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => mul_nonneg hq0 hM0)
    _ = (I.card : ℝ) * (q * Mt) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = q * q * Mt := by
        have hc : (I.card : ℝ) = q := by
          rw [hI, Int.card_Ioc, hq']
          have e : max m n - min m n = |m - n| := by
            rcases le_total m n with h | h
            · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by omega)]; ring
            · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by omega)]
          rw [e]
          have h0 : ((|m - n|).toNat : ℤ) = |m - n| := Int.toNat_of_nonneg (abs_nonneg _)
          have h1 : ((|m - n|).toNat : ℝ) = ((|m - n| : ℤ) : ℝ) := by exact_mod_cast h0
          rw [h1, Int.cast_abs]
        rw [hc]; ring

lemma Mn_measurable (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) : Measurable (Mn γ ℓ₀ ℓ₁) :=
  (Measurable.of_discrete (f := fun n : ℤ => M (Dg γ) ℓ₀ (ℓ₁ + 1) n)).comp (Ncnt_measurable γ ℓ₀ ℓ₁)

lemma Mn_le {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b) (t : ℝ) :
    Mn γ ℓ₀ ℓ₁ t ≤ ∑ r ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), Dg γ r := by
  obtain ⟨h0, h1⟩ := Ncnt_bounds γ W.h01 t
  exact M_le_sum _ (Dg_nonneg W.mono) (Finset.mem_Ico.mpr ⟨h0, by omega⟩)

/-- `∫_{(a,b]} M_{N(t)}² ≤ Σ_ℓ D_ℓ M_ℓ²`. -/
lemma integral_Mn_sq_le {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b) :
    ∫ t in Ioc a b, (Mn γ ℓ₀ ℓ₁ t) ^ 2
      ≤ ∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), Dg γ l * (M (Dg γ) ℓ₀ (ℓ₁ + 1) l) ^ 2 := by
  classical
  set W' := Finset.Ico ℓ₀ (ℓ₁ + 1)
  set g : ℝ → ℝ := fun t => ∑ l ∈ W', (Ico (γ l) (γ (l + 1))).indicator
    (fun _ => (M (Dg γ) ℓ₀ (ℓ₁ + 1) l) ^ 2) t with hg
  have hgi : Integrable g := by
    refine integrable_finsetSum _ (fun l _ => ?_)
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ico
  have hg0 : ∀ t, 0 ≤ g t := fun t => Finset.sum_nonneg (fun l _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) t)
  have hpt : ∀ t ∈ Ioc a b, (Mn γ ℓ₀ ℓ₁ t) ^ 2 ≤ g t := by
    intro t ht
    obtain ⟨h0, h1⟩ := Ncnt_bounds γ W.h01 t
    obtain ⟨hγn, hγn1⟩ := W.Ncnt_mem ht
    have hmem : Ncnt γ ℓ₀ ℓ₁ t ∈ W' := Finset.mem_Ico.mpr ⟨h0, by omega⟩
    have := Finset.single_le_sum (f := fun l => (Ico (γ l) (γ (l + 1))).indicator
      (fun _ => (M (Dg γ) ℓ₀ (ℓ₁ + 1) l) ^ 2) t) (fun l _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) t) hmem
    rw [Set.indicator_of_mem (show t ∈ Ico (γ (Ncnt γ ℓ₀ ℓ₁ t)) (γ (Ncnt γ ℓ₀ ℓ₁ t + 1)) from ⟨hγn, hγn1⟩)] at this
    exact this
  have hMi : IntegrableOn (fun t => (Mn γ ℓ₀ ℓ₁ t) ^ 2) (Ioc a b) := by
    refine IntegrableOn.of_bound (by simp) ((Mn_measurable γ ℓ₀ ℓ₁).pow_const 2).aestronglyMeasurable
      ((∑ r ∈ W', Dg γ r) ^ 2) (Filter.Eventually.of_forall (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (Mn_nonneg W t) (Mn_le W t) 2
  calc ∫ t in Ioc a b, (Mn γ ℓ₀ ℓ₁ t) ^ 2 ≤ ∫ t in Ioc a b, g t :=
        setIntegral_mono_on hMi hgi.integrableOn measurableSet_Ioc hpt
    _ ≤ ∫ t, g t := setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)
    _ = ∑ l ∈ W', Dg γ l * (M (Dg γ) ℓ₀ (ℓ₁ + 1) l) ^ 2 := by
        simp only [hg]
        rw [integral_finsetSum _ (fun l _ => (integrableOn_const (by simp)).integrable_indicator measurableSet_Ico)]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [integral_indicator_const _ measurableSet_Ico, smul_eq_mul,
          Real.volume_real_Ico_of_le (W.mono (show l ≤ l + 1 by omega))]
        rfl

/-- Hölder (3, 3/2) together with the maximal inequality: `Σ D M² ≤ 24^{2/3} Σ D³`. -/
lemma sum_DM2_le {γ : ℤ → ℝ} (hγ : Monotone γ) (A B : ℤ) :
    ∑ l ∈ Finset.Ico A B, Dg γ l * (M (Dg γ) A B l) ^ 2
      ≤ (24 : ℝ) ^ ((2 : ℝ) / 3) * ∑ l ∈ Finset.Ico A B, (Dg γ l) ^ 3 := by
  set W' := Finset.Ico A B
  have hD0 := Dg_nonneg hγ
  have hM0 : ∀ l ∈ W', 0 ≤ M (Dg γ) A B l := fun l hl => M_nonneg _ hD0 hl
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := W') (f := Dg γ) (g := fun l => (M (Dg γ) A B l) ^ 2)
    (p := 3) (q := 3 / 2) ⟨by norm_num, by norm_num, by norm_num⟩ (fun l _ => hD0 l) (fun l _ => sq_nonneg _)
  set X := ∑ l ∈ W', (Dg γ l) ^ 3 with hX
  set Y := ∑ l ∈ W', (M (Dg γ) A B l) ^ 3 with hY
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun l _ => pow_nonneg (hD0 l) 3)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun l hl => pow_nonneg (hM0 l hl) 3)
  have hYX : Y ≤ 24 * X := maximal_cube (Dg γ) hD0 A B
  have e1 : ∑ l ∈ W', (Dg γ l) ^ (3 : ℝ) = X := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact_mod_cast Real.rpow_natCast (Dg γ l) 3
  have e2 : ∑ l ∈ W', ((M (Dg γ) A B l) ^ 2) ^ ((3 : ℝ) / 2) = Y := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hM0 l hl)]
    norm_num
  rw [e1, e2, show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] at hH
  have h1 : Y ^ ((2 : ℝ) / 3) ≤ (24 * X) ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow hY0 hYX (by norm_num)
  have h2 : (24 * X) ^ ((2 : ℝ) / 3) = (24 : ℝ) ^ ((2 : ℝ) / 3) * X ^ ((2 : ℝ) / 3) :=
    Real.mul_rpow (by norm_num) hX0
  have h3 : X ^ ((1 : ℝ) / 3) * X ^ ((2 : ℝ) / 3) = X := by
    rw [← Real.rpow_add' hX0 (by norm_num)]; norm_num
  have h4 : 0 ≤ X ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hX0 _
  calc ∑ l ∈ W', Dg γ l * (M (Dg γ) A B l) ^ 2 ≤ X ^ ((1 : ℝ) / 3) * Y ^ ((2 : ℝ) / 3) := hH
    _ ≤ X ^ ((1 : ℝ) / 3) * ((24 : ℝ) ^ ((2 : ℝ) / 3) * X ^ ((2 : ℝ) / 3)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 h4
    _ = (24 : ℝ) ^ ((2 : ℝ) / 3) * (X ^ ((1 : ℝ) / 3) * X ^ ((2 : ℝ) / 3)) := by ring
    _ = (24 : ℝ) ^ ((2 : ℝ) / 3) * X := by rw [h3]

lemma qf_measurable (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (qf γ ℓ₀ ℓ₁ f) := by
  have h1 : Measurable (fun t => ⌊f t + 1 / 2⌋) := (hf.add_const _).floor
  have h2 : Measurable (fun t => (⌊f t + 1 / 2⌋, Ncnt γ ℓ₀ ℓ₁ t)) := h1.prodMk (Ncnt_measurable γ ℓ₀ ℓ₁)
  exact (Measurable.of_discrete (f := fun z : ℤ × ℤ => |((z.1 - z.2 : ℤ) : ℝ)|)).comp h2

lemma qf_nonneg (γ : ℤ → ℝ) (ℓ₀ ℓ₁ : ℤ) (f : ℝ → ℝ) (t : ℝ) : 0 ≤ qf γ ℓ₀ ℓ₁ f t := abs_nonneg _

/-- **Theorem 7.3 (sublevel transfer)**, final form: constant `2·24^{1/3}` and `∫ q⁴`. -/
theorem transfer {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hQ : IntegrableOn (fun t => (qf γ ℓ₀ ℓ₁ f t) ^ 4) (Ioc a b)) :
    ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (xk f a b k - γ k) ^ 2
      ≤ 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * (∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3) ^ ((1 : ℝ) / 2)
        * (∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 4) ^ ((1 : ℝ) / 2) := by
  classical
  set q := qf γ ℓ₀ ℓ₁ f with hqdef
  set Mt := Mn γ ℓ₀ ℓ₁ with hMtdef
  set X := ∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3 with hX
  set IQ := ∫ t in Ioc a b, (q t) ^ 4 with hIQ
  have hqm : Measurable q := qf_measurable γ ℓ₀ ℓ₁ hf
  have hq0 : ∀ t, 0 ≤ q t := qf_nonneg γ ℓ₀ ℓ₁ f
  have hMm : Measurable Mt := Mn_measurable γ ℓ₀ ℓ₁
  have hM0 : ∀ t, 0 ≤ Mt t := Mn_nonneg W
  set C := ∑ r ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), Dg γ r with hC
  have hMC : ∀ t, Mt t ≤ C := Mn_le W
  -- integrability facts on (a,b]
  have hq4 : IntegrableOn (fun t => (q t * q t) ^ 2) (Ioc a b) := by
    refine hQ.congr_fun (fun t _ => ?_) measurableSet_Ioc
    ring
  have hq2 : IntegrableOn (fun t => q t * q t) (Ioc a b) := by
    refine ((integrableOn_const (C := (1:ℝ)) (by simp)).add hQ).mono' (hqm.mul hqm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 t) (hq0 t))]
    have := hq0 t
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (q t * q t - 1), sq_nonneg (q t)]
  have hqqM : IntegrableOn (fun t => q t * q t * Mt t) (Ioc a b) := by
    refine (hq2.mul_const C).mono' ((hqm.mul hqm).mul hMm).aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hq0 t) (hq0 t)) (hM0 t))]
    exact mul_le_mul_of_nonneg_left (hMC t) (mul_nonneg (hq0 t) (hq0 t))
  have hMsq : IntegrableOn (fun t => (Mt t) ^ 2) (Ioc a b) := by
    refine IntegrableOn.of_bound (by simp) (hMm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hM0 t) (hMC t) 2
  have hind : ∀ k ∈ Finset.Ioc ℓ₀ ℓ₁,
      IntegrableOn ((Ek f a b γ k).indicator (fun t => |t - γ k|)) (Ioc a b) := by
    intro k _
    have hcont : Continuous fun t : ℝ => |t - γ k| := by fun_prop
    exact (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      ((measurableSet_Uk hf b (γ k) k).union (measurableSet_Vk hf a (γ k) k))
  -- Step 1: bathtub for each k, then sum
  have step1 : ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (xk f a b k - γ k) ^ 2
      ≤ 2 * ∫ t in Ioc a b, ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (Ek f a b γ k).indicator (fun t => |t - γ k|) t := by
    rw [integral_finsetSum _ hind, Finset.mul_sum]
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨h1, h2⟩ := W.mem_k hk
    exact xk_sq_le hf h1 h2 k
  -- Step 2: pointwise estimate
  have step2 : ∫ t in Ioc a b, ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (Ek f a b γ k).indicator (fun t => |t - γ k|) t
      ≤ ∫ t in Ioc a b, q t * q t * Mt t :=
    setIntegral_mono_on (integrable_finsetSum _ hind) hqqM measurableSet_Ioc
      (fun t ht => pointwise W f ht)
  -- Step 3: Cauchy–Schwarz
  have hmem1 : MemLp (fun t => q t * q t) (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq (hqm.mul hqm).aestronglyMeasurable).mpr hq4
  have hmem2 : MemLp Mt (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hMm.aestronglyMeasurable).mpr hMsq
  have step3 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc a b)) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => mul_nonneg (hq0 t) (hq0 t)))
    (Filter.Eventually.of_forall hM0) hmem1 hmem2
  have e1 : ∫ t in Ioc a b, (q t * q t) ^ (2 : ℝ) = ∫ t in Ioc a b, (q t * q t) ^ 2 := by
    congr 1; ext t; exact_mod_cast Real.rpow_natCast (q t * q t) 2
  have e2 : ∫ t in Ioc a b, (Mt t) ^ (2 : ℝ) = ∫ t in Ioc a b, (Mt t) ^ 2 := by
    congr 1; ext t; exact_mod_cast Real.rpow_natCast (Mt t) 2
  rw [e1, e2] at step3
  -- Step 4: the two L² norms
  have hA : ∫ t in Ioc a b, (q t * q t) ^ 2 ≤ IQ := by
    refine le_of_eq (setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_))
    ring
  have hB : ∫ t in Ioc a b, (Mt t) ^ 2 ≤ (24 : ℝ) ^ ((2 : ℝ) / 3) * X :=
    le_trans (integral_Mn_sq_le W) (sum_DM2_le W.mono ℓ₀ (ℓ₁ + 1))
  have hA0 : 0 ≤ ∫ t in Ioc a b, (q t * q t) ^ 2 := setIntegral_nonneg measurableSet_Ioc (fun t _ => sq_nonneg _)
  have hB0 : 0 ≤ ∫ t in Ioc a b, (Mt t) ^ 2 := setIntegral_nonneg measurableSet_Ioc (fun t _ => sq_nonneg _)
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun l _ => pow_nonneg (Dg_nonneg W.mono l) 3)
  have hA' := Real.rpow_le_rpow hA0 hA (show (0:ℝ) ≤ 1 / 2 by norm_num)
  have hB' := Real.rpow_le_rpow hB0 hB (show (0:ℝ) ≤ 1 / 2 by norm_num)
  have e3 : ((24 : ℝ) ^ ((2 : ℝ) / 3) * X) ^ ((1 : ℝ) / 2) = (24 : ℝ) ^ ((1 : ℝ) / 3) * X ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) hX0, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [e3] at hB'
  have hIQ0 : 0 ≤ IQ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_trans hA0 hA) _
  have hP1 : 0 ≤ (∫ t in Ioc a b, (q t * q t) ^ 2) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hA0 _
  calc ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (xk f a b k - γ k) ^ 2
      ≤ 2 * ∫ t in Ioc a b, q t * q t * Mt t := le_trans step1 (by linarith [step2])
    _ ≤ 2 * ((∫ t in Ioc a b, (q t * q t) ^ 2) ^ ((1 : ℝ) / 2) * (∫ t in Ioc a b, (Mt t) ^ 2) ^ ((1 : ℝ) / 2)) := by
        have : ∫ t in Ioc a b, q t * q t * Mt t = ∫ t in Ioc a b, (q t * q t) * Mt t := rfl
        linarith [step3]
    _ ≤ 2 * (IQ ^ ((1 : ℝ) / 2) * ((24 : ℝ) ^ ((1 : ℝ) / 3) * X ^ ((1 : ℝ) / 2))) := by
        have := mul_le_mul hA' hB' (Real.rpow_nonneg hB0 _) hIQ0
        linarith
    _ = 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * X ^ ((1 : ℝ) / 2) * IQ ^ ((1 : ℝ) / 2) := by ring

/-- **Theorem 7.3** with `q²(q+1)²` (article v6 form) and constant `2·24^{1/3}`. -/
theorem transfer_24 {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hQ : IntegrableOn (fun t => (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2) (Ioc a b)) :
    ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (xk f a b k - γ k) ^ 2
      ≤ 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * (∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3) ^ ((1 : ℝ) / 2)
        * (∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2) ^ ((1 : ℝ) / 2) := by
  have hqm := qf_measurable γ ℓ₀ ℓ₁ hf
  have hq0 := qf_nonneg γ ℓ₀ ℓ₁ f
  have h4le : ∀ t, (qf γ ℓ₀ ℓ₁ f t) ^ 4 ≤ (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2 := fun t => by
    have := hq0 t; nlinarith [sq_nonneg (qf γ ℓ₀ ℓ₁ f t), mul_nonneg this this, pow_nonneg this 3]
  have hQ4 : IntegrableOn (fun t => (qf γ ℓ₀ ℓ₁ f t) ^ 4) (Ioc a b) := by
    refine hQ.mono' (hqm.pow_const 4).aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hq0 t) 4)]
    exact h4le t
  have h := transfer W hf hQ4
  have hI4 : ∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 4 ≤ ∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2 :=
    setIntegral_mono_on hQ4 hQ measurableSet_Ioc (fun t _ => h4le t)
  have hI40 : 0 ≤ ∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 4 :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => pow_nonneg (hq0 t) 4)
  have hr := Real.rpow_le_rpow hI40 hI4 (show (0:ℝ) ≤ 1 / 2 by norm_num)
  have hc : 0 ≤ 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * (∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3) ^ ((1 : ℝ) / 2) := by
    have h0 : (0:ℝ) ≤ ∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3 :=
      Finset.sum_nonneg (fun l _ => pow_nonneg (Dg_nonneg W.mono l) 3)
    have := Real.rpow_nonneg h0 ((1:ℝ)/2)
    positivity
  exact le_trans h (mul_le_mul_of_nonneg_left hr hc)

/-- **Theorem 7.3** (constant `2·36^{1/3}`), with the maximal function in the windowed form of
`maximal_cube_36`. Besides measurability of `f` (as in the article), Lean needs `q_f^2 (q_f+1)^2`
integrable on `(a,b]`: in Lean a non-integrable integral is `0`, whereas in the article the right side is
then `+∞` and the inequality is trivial. In the application (`Sublevel.lean`) this integrability is proved
from the hypotheses (local boundedness of `S`), not assumed. -/
theorem transfer_36 {γ : ℤ → ℝ} {ℓ₀ ℓ₁ : ℤ} {a b : ℝ} (W : Window γ ℓ₀ ℓ₁ a b)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hQ : IntegrableOn (fun t => (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2) (Ioc a b)) :
    ∑ k ∈ Finset.Ioc ℓ₀ ℓ₁, (xk f a b k - γ k) ^ 2
      ≤ 2 * (36 : ℝ) ^ ((1 : ℝ) / 3) * (∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3) ^ ((1 : ℝ) / 2)
        * (∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2) ^ ((1 : ℝ) / 2) := by
  have h := transfer_24 W hf hQ
  have hX : 0 ≤ (∑ l ∈ Finset.Ico ℓ₀ (ℓ₁ + 1), (Dg γ l) ^ 3) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg
    (Finset.sum_nonneg (fun l _ => pow_nonneg (Dg_nonneg W.mono l) 3)) _
  have hI : 0 ≤ (∫ t in Ioc a b, (qf γ ℓ₀ ℓ₁ f t) ^ 2 * (qf γ ℓ₀ ℓ₁ f t + 1) ^ 2) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (setIntegral_nonneg measurableSet_Ioc (fun t _ => by positivity)) _
  have hc : (24 : ℝ) ^ ((1 : ℝ) / 3) ≤ (36 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 2 by norm_num)) hX) hI
  linarith

end RvmClock
