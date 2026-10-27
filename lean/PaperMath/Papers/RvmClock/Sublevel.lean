import PaperMath.Papers.RvmClock.Fourth
import PaperMath.Papers.RvmClock.Transfer

/-!
# Theorem 1.5 (localisation by primes) and Corollary 1.6

Hypotheses (all explicit): `FujiiA`, `FujiiB` (Theorem 3.8 (a), (b)) and `Titchmarsh`
(Theorem 3.1: `S(t) = O(log t)` and `γ_{k+1} − γ_k → 0`).

Indexing: Lean's `Z.γ ℓ` (`ℓ ≥ 0`) is the article's `γ_{ℓ+1}`; the article's `x_k` is `xClock k`.
-/

open MeasureTheory Set Finset
open scoped Real

namespace RvmClock

namespace ZetaInputs

variable (Z : ZetaInputs)

/-- **Hypothesis (Theorem 3.1, Titchmarsh §§9.4, 9.12):** `S(t) = O(log t)` and the gaps tend to `0`. -/
def Titchmarsh : Prop :=
  (∃ C T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → |Z.S t| ≤ C * Real.log t) ∧
  (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Z.D k ≤ ε)

lemma N_ge (t : ℝ) (ht : 1 ≤ t) : N0 t - |Z.S t| - 1 ≤ (Z.N t : ℝ) := by
  have hv := Z.varpi_bound t ht
  have hpi := Real.pi_pos
  have hv1 : |Z.varpi t / π| ≤ 1 := by
    rw [abs_div, abs_of_pos hpi, div_le_one hpi]
    have : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; exact ht
    linarith [Real.pi_gt_three]
  have hS : (Z.N t : ℝ) = Z.S t + N0 t + Z.varpi t / π := by unfold S; ring
  rw [hS]
  have := neg_abs_le (Z.S t)
  have := neg_abs_le (Z.varpi t / π)
  linarith

lemma N_le (t : ℝ) (ht : 1 ≤ t) : (Z.N t : ℝ) ≤ N0 t + |Z.S t| + 1 := by
  have hv := Z.varpi_bound t ht
  have hpi := Real.pi_pos
  have hv1 : |Z.varpi t / π| ≤ 1 := by
    rw [abs_div, abs_of_pos hpi, div_le_one hpi]
    have : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; exact ht
    linarith [Real.pi_gt_three]
  have hS : (Z.N t : ℝ) = Z.S t + N0 t + Z.varpi t / π := by unfold S; ring
  rw [hS]
  have := le_abs_self (Z.S t)
  have := le_abs_self (Z.varpi t / π)
  linarith

end ZetaInputs

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  linarith

lemma pi_lt_four : π < 4 := by linarith [Real.pi_lt_d2]

/-- The threshold used for the localisation of the sublevel sets. -/
noncomputable def Tbig (C : ℝ) : ℝ := (60 * (1 + 2 * C) + 1) ^ 2

lemma sqrt_ge_of_Tbig {C T : ℝ} (hC : 0 ≤ C) (hT : Tbig C ≤ T) : 60 * (1 + 2 * C) + 1 ≤ Real.sqrt T := by
  have := Real.sqrt_le_sqrt hT
  rwa [Tbig, Real.sqrt_sq (by positivity)] at this

lemma Tbig_ge (C : ℝ) (hC : 0 ≤ C) : 3600 ≤ Tbig C := by
  unfold Tbig; nlinarith

lemma N0_le_7_8 {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 2 * π * Real.exp 1) : N0 t ≤ 7 / 8 := by
  unfold N0
  have hpi := Real.pi_pos
  have : Real.log (t / (2 * π * Real.exp 1)) ≤ 0 :=
    Real.log_nonpos (by positivity) (by rw [div_le_one (by positivity)]; exact ht)
  have : 0 ≤ t / (2 * π) := by positivity
  nlinarith

lemma N0_ge_7_8 {t : ℝ} (ht : 2 * π * Real.exp 1 ≤ t) : 7 / 8 ≤ N0 t := by
  unfold N0
  have hpi := Real.pi_pos
  have h0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have : 0 ≤ Real.log (t / (2 * π * Real.exp 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have : 0 ≤ t / (2 * π) := by positivity
  nlinarith

lemma two_pi_e_lt : 2 * π * Real.exp 1 < 24 := by
  have := Real.exp_one_lt_d9
  have := pi_lt_four
  nlinarith [Real.pi_pos]

/-- `N₀` on `(0, T/2]` is at most `N₀(T/2)`. -/
lemma N0_le_half {T t : ℝ} (hT : 48 ≤ T) (ht0 : 0 < t) (ht : t ≤ T / 2) : N0 t ≤ N0 (T / 2) := by
  have he := two_pi_e_lt
  by_cases h : t ≤ 2 * π * Real.exp 1
  · exact le_trans (N0_le_7_8 ht0 h) (N0_ge_7_8 (by linarith))
  · push Not at h
    have := N0_sub_ge ht0 ht
    have hl : 0 ≤ Real.log (t / (2 * π)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith [Real.pi_pos]
    have : 0 ≤ (T / 2 - t) * Real.log (t / (2 * π)) / (2 * π) := by
      apply div_nonneg (mul_nonneg (by linarith) hl) (by positivity)
    linarith

/-- **Below the window.** For `T` large and `0 < t ≤ T/2`, `𝓕(t) < N(T) + 1/2`. -/
lemma F_lt_low (Z : ZetaInputs) {C T₀ : ℝ} (hC : 0 ≤ C)
    (hS : ∀ t : ℝ, T₀ ≤ t → |Z.S t| ≤ C * Real.log t)
    {T : ℝ} (hT0 : T₀ ≤ T) (hT : Tbig C ≤ T) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ T / 2) :
    F t < Z.N T + 1 / 2 := by
  have hT3600 := Tbig_ge C hC
  have hTpos : 0 < T := by linarith
  have hpi := Real.pi_pos
  have hpi4 := pi_lt_four
  set s := Real.sqrt T with hs
  have hs0 : 60 * (1 + 2 * C) + 1 ≤ s := sqrt_ge_of_Tbig hC hT
  have hsT : s ^ 2 = T := Real.sq_sqrt hTpos.le
  -- 𝓕(t) ≤ N₀(T/2) + √T/4
  have hF : F t ≤ N0 (T / 2) + s / 4 := by
    unfold F
    have h1 := abs_Phi_le_sqrt ht0
    have h2 : Real.sqrt (2 * t) ≤ s := Real.sqrt_le_sqrt (by linarith)
    have h3 := N0_le_half (by linarith) ht0 ht
    have := le_abs_self (Phi t)
    linarith
  -- N(T) ≥ N₀(T) − C log T − 1
  have hN := Z.N_ge T (by linarith)
  have hSb := hS T hT0
  have hlog : Real.log T ≤ 2 * s := log_le_two_sqrt hTpos
  -- N₀(T) − N₀(T/2) ≥ T/(4π)
  have hgain : T / (4 * π) ≤ N0 T - N0 (T / 2) := by
    have := N0_sub_ge (by linarith : (0 : ℝ) < T / 2) (by linarith : T / 2 ≤ T)
    have hl : 1 ≤ Real.log (T / 2 / (2 * π)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      rw [le_div_iff₀ (by positivity)]
      have := Real.exp_one_lt_d9
      nlinarith
    have : (T - T / 2) * 1 / (2 * π) ≤ (T - T / 2) * Real.log (T / 2 / (2 * π)) / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hl (by linarith)
    have e : T / (4 * π) = (T - T / 2) * 1 / (2 * π) := by field_simp; ring
    linarith
  have hT4 : T / 16 < T / (4 * π) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hCl : C * Real.log T ≤ C * (2 * s) := mul_le_mul_of_nonneg_left hlog hC
  have hs1 : 1 ≤ s := by nlinarith
  have hbig : s / 4 + C * (2 * s) + 1 / 2 < T / 16 := by
    rw [← hsT]; nlinarith
  linarith

/-- **Above the window.** For `T` large and `t ≥ 3T`, `𝓕(t) > N(2T)`. -/
lemma F_gt_high (Z : ZetaInputs) {C T₀ : ℝ} (hC : 0 ≤ C)
    (hS : ∀ t : ℝ, T₀ ≤ t → |Z.S t| ≤ C * Real.log t)
    {T : ℝ} (hT0 : T₀ ≤ T) (hT : Tbig C ≤ T) {t : ℝ} (ht : 3 * T ≤ t) :
    (Z.N (2 * T) : ℝ) < F t := by
  have hT3600 := Tbig_ge C hC
  have hTpos : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hpi := Real.pi_pos
  have hpi4 := pi_lt_four
  set u := Real.sqrt t with hu
  have hut : u ^ 2 = t := Real.sq_sqrt ht0.le
  have hu0 : 60 * (1 + 2 * C) + 1 ≤ u :=
    le_trans (sqrt_ge_of_Tbig hC hT) (Real.sqrt_le_sqrt (by linarith))
  have hF : N0 t - u / 2 ≤ F t := by
    unfold F
    have h1 := abs_Phi_le_sqrt ht0
    have h2 : Real.sqrt (2 * t) ≤ 2 * u := by
      rw [show 2 * u = Real.sqrt (4 * t) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have := neg_abs_le (Phi t)
    linarith
  have hN := Z.N_le (2 * T) (by linarith)
  have hSb := hS (2 * T) (by linarith)
  have hlog : Real.log (2 * T) ≤ 2 * u :=
    le_trans (Real.log_le_log (by linarith) (by linarith)) (log_le_two_sqrt ht0)
  have hgain : t / (6 * π) ≤ N0 t - N0 (2 * T) := by
    have := N0_sub_ge (by linarith : (0 : ℝ) < 2 * T) (by linarith : 2 * T ≤ t)
    have hl : 1 ≤ Real.log (2 * T / (2 * π)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      rw [le_div_iff₀ (by positivity)]
      have := Real.exp_one_lt_d9
      nlinarith
    have : t / 3 * 1 / (2 * π) ≤ (t - 2 * T) * Real.log (2 * T / (2 * π)) / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (by linarith) hl (by norm_num) (by linarith)
    have e : t / (6 * π) = t / 3 * 1 / (2 * π) := by field_simp; ring
    linarith
  have ht24 : t / 24 < t / (6 * π) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hCl : C * Real.log (2 * T) ≤ C * (2 * u) := mul_le_mul_of_nonneg_left hlog hC
  have hbig : u / 2 + C * (2 * u) + 1 < t / 24 := by
    rw [← hut]; nlinarith
  linarith

/-- `𝓕` extended continuously to all of `ℝ` (equal to `𝓕` on `[1, ∞)`). -/
noncomputable def Fx (t : ℝ) : ℝ := F (max t 1)

lemma continuous_Fx : Continuous Fx :=
  continuousOn_F.comp_continuous (continuous_id.max continuous_const)
    (fun t => show max t 1 ∈ Ioi (0 : ℝ) from Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos (le_max_right t 1)))

lemma Fx_eq {t : ℝ} (ht : 1 ≤ t) : Fx t = F t := by unfold Fx; rw [max_eq_left ht]

/-- The ordinates with the article's indexing: `γ' k = γ_k` for `k ≥ 1`. -/
def gam (Z : ZetaInputs) (k : ℤ) : ℝ := Z.γ (k - 1).toNat

lemma gam_mono (Z : ZetaInputs) : Monotone (gam Z) := by
  intro a b h; unfold gam; exact Z.mono (Int.toNat_le_toNat (by omega))

lemma gam_natCast (Z : ZetaInputs) {k : ℕ} (hk : 1 ≤ k) : gam Z k = Z.γ (k - 1) := by
  unfold gam; congr 1; omega

lemma gam_le_iff (Z : ZetaInputs) {k : ℤ} (hk : 1 ≤ k) (t : ℝ) : gam Z k ≤ t ↔ k ≤ Z.N t := by
  unfold gam
  rw [← Z.lt_N_iff t]
  omega

lemma window (Z : ZetaInputs) {a b : ℝ} (hab : a < b) (ha : 1 ≤ Z.N a) :
    Window (gam Z) (Z.N a) (Z.N b) a b := by
  have hNab : Z.N a ≤ Z.N b := Z.N_mono hab.le
  refine ⟨gam_mono Z, by exact_mod_cast hNab, hab, ?_, ?_, ?_, ?_⟩
  · exact (gam_le_iff Z (by exact_mod_cast ha) a).mpr le_rfl
  · have := (gam_le_iff Z (by omega : (1 : ℤ) ≤ (Z.N a : ℤ) + 1) a).not.mpr (by omega)
    exact lt_of_not_ge this
  · exact (gam_le_iff Z (by exact_mod_cast (le_trans ha hNab)) b).mpr le_rfl
  · have := (gam_le_iff Z (by omega : (1 : ℤ) ≤ (Z.N b : ℤ) + 1) b).not.mpr (by omega)
    exact lt_of_not_ge this

lemma Ncnt_eq (Z : ZetaInputs) {a b t : ℝ} (ha : 1 ≤ Z.N a) (hat : a < t) (htb : t ≤ b) :
    Ncnt (gam Z) (Z.N a) (Z.N b) t = Z.N t := by
  classical
  have hNat : Z.N a ≤ Z.N t := Z.N_mono hat.le
  have hNtb : Z.N t ≤ Z.N b := Z.N_mono htb
  have hfil : (Finset.Ioc (Z.N a : ℤ) (Z.N b)).filter (fun k => gam Z k ≤ t)
      = Finset.Ioc (Z.N a : ℤ) (Z.N t) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (gam_le_iff Z (by omega) t).mp h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, (gam_le_iff Z (by omega) t).mpr h2⟩
  unfold Ncnt
  rw [hfil, Int.card_Ioc]
  omega

lemma qf_le (Z : ZetaInputs) {a b t : ℝ} (ha : 1 ≤ Z.N a) (ha1 : 1 ≤ a) (hat : a < t) (htb : t ≤ b) :
    qf (gam Z) (Z.N a) (Z.N b) Fx t ≤ |F t - Z.N t| + 1 := by
  unfold qf
  rw [Ncnt_eq Z ha hat htb, Fx_eq (by linarith)]
  have h1 := Int.floor_le (F t + 1 / 2)
  have h2 := Int.lt_floor_add_one (F t + 1 / 2)
  push_cast
  rw [abs_le]
  constructor
  · have := neg_abs_le (F t - Z.N t); linarith
  · have := le_abs_self (F t - Z.N t); linarith

/-- For `k ∈ 𝒦_T`, the sublevel point `x_k` is computed inside the window `[T/2, 3T]`. -/
lemma xClock_eq (Z : ZetaInputs) {C T₀ : ℝ} (hC : 0 ≤ C)
    (hS : ∀ t : ℝ, T₀ ≤ t → |Z.S t| ≤ C * Real.log t)
    {T : ℝ} (hT0 : T₀ ≤ T) (hT : Tbig C ≤ T) {k : ℕ} (hk1 : Z.N T < k) (hk2 : k ≤ Z.N (2 * T)) :
    xClock k = xk Fx (T / 2) (3 * T) k := by
  have hT3600 := Tbig_ge C hC
  have hset : {t ∈ Ioi (0 : ℝ) | F t < (k : ℝ) - 1 / 2}
      = Ioc 0 (T / 2) ∪ (Ioc (T / 2) (3 * T) ∩ {t | Fx t < ((k : ℤ) : ℝ) - 1 / 2}) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_union, Set.mem_Ioc, Set.mem_inter_iff, Int.cast_natCast]
    constructor
    · rintro ⟨ht0, hF⟩
      by_cases h : t ≤ T / 2
      · exact Or.inl ⟨ht0, h⟩
      · push Not at h
        right
        have htb : t ≤ 3 * T := by
          by_contra hc; push Not at hc
          have := F_gt_high Z hC hS hT0 hT hc.le
          have : (k : ℝ) ≤ Z.N (2 * T) := by exact_mod_cast hk2
          linarith
        refine ⟨⟨h, htb⟩, ?_⟩
        rw [Fx_eq (by linarith)]; exact hF
    · rintro (⟨ht0, h⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · refine ⟨ht0, ?_⟩
        have := F_lt_low Z hC hS hT0 hT ht0 h
        have : (Z.N T : ℝ) + 1 ≤ k := by exact_mod_cast hk1
        linarith
      · refine ⟨by linarith, ?_⟩
        rw [← Fx_eq (by linarith)]; exact h3
  unfold xClock xk
  have hd : Disjoint (Ioc (0 : ℝ) (T / 2)) (Ioc (T / 2) (3 * T) ∩ {t | Fx t < ((k : ℤ) : ℝ) - 1 / 2}) :=
    Set.disjoint_left.mpr (fun t h1 h2 => by linarith [h1.2, h2.1.1])
  have hm : MeasurableSet (Ioc (T / 2) (3 * T) ∩ {t | Fx t < ((k : ℤ) : ℝ) - 1 / 2}) :=
    measurableSet_Ioc.inter (measurableSet_lt continuous_Fx.measurable measurable_const)
  have h1 : volume (Ioc (0 : ℝ) (T / 2)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have h2 : volume (Ioc (T / 2) (3 * T) ∩ {t | Fx t < ((k : ℤ) : ℝ) - 1 / 2}) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top).ne
  rw [hset, measureReal_union hd hm h1 h2, Real.volume_real_Ioc_of_le (by linarith)]
  ring

/-- Four consecutive dyadic blocks: integrability and the bound `∫_u^{16u} |𝓕 − N|⁴ ≤ 15 B u`. -/
lemma four_blocks (Z : ZetaInputs) {B : ℝ} {j₀ : ℤ}
    (hblk : ∀ j : ℤ, j₀ ≤ j →
      IntegrableOn (fun t => |F t - Z.N t| ^ 4) (Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) ∧
      ∫ t in Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), |F t - Z.N t| ^ 4 ≤ B * (2 : ℝ) ^ j)
    {j : ℤ} (hj : j₀ ≤ j) :
    IntegrableOn (fun t => |F t - Z.N t| ^ 4) (Icc ((2 : ℝ) ^ j) (16 * (2 : ℝ) ^ j)) ∧
    ∫ t in Icc ((2 : ℝ) ^ j) (16 * (2 : ℝ) ^ j), |F t - Z.N t| ^ 4 ≤ 15 * B * (2 : ℝ) ^ j := by
  set g := fun t => |F t - (Z.N t : ℝ)| ^ 4
  set u := (2 : ℝ) ^ j
  have hu : 0 < u := two_zpow_pos j
  have e1 : (2 : ℝ) ^ (j + 1) = 2 * u := by rw [zpow_add_one₀ (by norm_num)]; ring
  have e2 : (2 : ℝ) ^ (j + 2) = 4 * u := by
    rw [show j + 2 = (j + 1) + 1 by ring, zpow_add_one₀ (by norm_num), e1]; ring
  have e3 : (2 : ℝ) ^ (j + 3) = 8 * u := by
    rw [show j + 3 = (j + 2) + 1 by ring, zpow_add_one₀ (by norm_num), e2]; ring
  obtain ⟨i0, b0⟩ := hblk j hj
  obtain ⟨i1, b1⟩ := hblk (j + 1) (by omega)
  obtain ⟨i2, b2⟩ := hblk (j + 2) (by omega)
  obtain ⟨i3, b3⟩ := hblk (j + 3) (by omega)
  rw [e1] at i1 b1; rw [e2] at i2 b2; rw [e3] at i3 b3
  have I0 : IntervalIntegrable g volume u (2 * u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr i0
  have I1 : IntervalIntegrable g volume (2 * u) (4 * u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr (by
      have := i1; rwa [show 2 * (2 * u) = 4 * u by ring] at this)
  have I2 : IntervalIntegrable g volume (4 * u) (8 * u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr (by
      have := i2; rwa [show 2 * (4 * u) = 8 * u by ring] at this)
  have I3 : IntervalIntegrable g volume (8 * u) (16 * u) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr (by
      have := i3; rwa [show 2 * (8 * u) = 16 * u by ring] at this)
  have Iall : IntervalIntegrable g volume u (16 * u) := ((I0.trans I1).trans I2).trans I3
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp Iall, ?_⟩
  have conv : ∀ {x y : ℝ}, x ≤ y → ∫ t in Icc x y, g t = ∫ t in x..y, g t := by
    intro x y hxy
    rw [intervalIntegral.integral_of_le hxy, integral_Icc_eq_integral_Ioc]
  rw [conv (by linarith), ← intervalIntegral.integral_add_adjacent_intervals ((I0.trans I1).trans I2) I3,
    ← intervalIntegral.integral_add_adjacent_intervals (I0.trans I1) I2,
    ← intervalIntegral.integral_add_adjacent_intervals I0 I1]
  rw [← conv (by linarith), ← conv (by linarith), ← conv (by linarith), ← conv (by linarith)]
  have b1' : ∫ t in Icc (2 * u) (4 * u), g t ≤ B * (2 * u) := by
    have := b1; rwa [show 2 * (2 * u) = 4 * u by ring] at this
  have b2' : ∫ t in Icc (4 * u) (8 * u), g t ≤ B * (4 * u) := by
    have := b2; rwa [show 2 * (4 * u) = 8 * u by ring] at this
  have b3' : ∫ t in Icc (8 * u) (16 * u), g t ≤ B * (8 * u) := by
    have := b3; rwa [show 2 * (8 * u) = 16 * u by ring] at this
  linarith

/-- **Fourth moment of `q_f` on the window `(T/2, 3T]`.** -/
lemma Q_bound (Z : ZetaInputs) (hFA : Z.FujiiA) :
    ∃ B T₂ : ℝ, 0 ≤ B ∧ 2 ≤ T₂ ∧ ∀ T : ℝ, T₂ ≤ T → 1 ≤ Z.N (T / 2) →
      IntegrableOn (fun t => (qf (gam Z) (Z.N (T / 2)) (Z.N (3 * T)) Fx t) ^ 4) (Ioc (T / 2) (3 * T)) ∧
      ∫ t in Ioc (T / 2) (3 * T), (qf (gam Z) (Z.N (T / 2)) (Z.N (3 * T)) Fx t) ^ 4 ≤ B * T := by
  obtain ⟨B, j₀, hB, hblk⟩ := fourth_moment Z hFA
  refine ⟨60 * B + 20, max 2 (4 * (2 : ℝ) ^ j₀), by positivity, le_max_left _ _, ?_⟩
  intro T hT hNa
  have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hT
  have hTj : 4 * (2 : ℝ) ^ j₀ ≤ T := le_trans (le_max_right _ _) hT
  set a := T / 2 with ha
  set b := 3 * T with hb
  have ha0 : 0 < a := by positivity
  obtain ⟨hu1, hu2⟩ := mem_blk ha0
  set j := blk a
  set u := (2 : ℝ) ^ j
  have hu2' : a < 2 * u := by rw [zpow_add_one₀ (by norm_num)] at hu2; linarith
  have hj : j₀ ≤ j := by
    have : (2 : ℝ) ^ j₀ < (2 : ℝ) ^ j := by linarith
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
    omega
  obtain ⟨hint, hI⟩ := four_blocks Z hblk hj
  set g := fun t => |F t - (Z.N t : ℝ)| ^ 4
  have hsub : Ioc a b ⊆ Icc u (16 * u) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgi : IntegrableOn g (Ioc a b) := hint.mono_set hsub
  have hmaj : ∀ t ∈ Ioc a b, (qf (gam Z) (Z.N a) (Z.N b) Fx t) ^ 4 ≤ 8 * (g t + 1) := by
    intro t ht
    have hq := qf_le Z hNa (by linarith) ht.1 ht.2
    have hq0 : 0 ≤ qf (gam Z) (Z.N a) (Z.N b) Fx t := qf_nonneg _ _ _ _ _
    have h1 : (qf (gam Z) (Z.N a) (Z.N b) Fx t) ^ 4 ≤ (|F t - Z.N t| + 1) ^ 4 :=
      pow_le_pow_left₀ hq0 hq 4
    have h2 := abs_add_pow4_le (|F t - Z.N t|) 1
    rw [abs_abs, abs_one, one_pow] at h2
    have h3 : |(|F t - (Z.N t : ℝ)|) + 1| = |F t - Z.N t| + 1 := abs_of_nonneg (by positivity)
    rw [h3] at h2
    show _ ≤ 8 * (|F t - (Z.N t : ℝ)| ^ 4 + 1)
    linarith
  have hmi : IntegrableOn (fun t => 8 * (g t + 1)) (Ioc a b) :=
    (hgi.add (integrableOn_const (by simp))).const_mul 8
  have hqm : Measurable (fun t => (qf (gam Z) (Z.N a) (Z.N b) Fx t) ^ 4) :=
    (qf_measurable _ _ _ continuous_Fx.measurable).pow_const 4
  have hqi : IntegrableOn (fun t => (qf (gam Z) (Z.N a) (Z.N b) Fx t) ^ 4) (Ioc a b) := by
    refine Integrable.mono' hmi hqm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmaj t ht
  refine ⟨hqi, ?_⟩
  have hg0 : ∀ t, 0 ≤ g t := fun t => by positivity
  have hIoc : ∫ t in Ioc a b, g t ≤ ∫ t in Icc u (16 * u), g t :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hsub)
  calc ∫ t in Ioc a b, (qf (gam Z) (Z.N a) (Z.N b) Fx t) ^ 4
      ≤ ∫ t in Ioc a b, 8 * (g t + 1) := setIntegral_mono_on hqi hmi measurableSet_Ioc hmaj
    _ = 8 * ((∫ t in Ioc a b, g t) + (b - a)) := by
        rw [integral_const_mul, integral_add hgi (integrableOn_const (by simp)), setIntegral_const,
          Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul, mul_one]
    _ ≤ (60 * B + 20) * T := by
        have : 15 * B * u ≤ 15 * B * a := mul_le_mul_of_nonneg_left hu1 (by positivity)
        nlinarith

lemma Dg_gam (Z : ZetaInputs) {l : ℤ} (hl : 1 ≤ l) : Dg (gam Z) l = Z.D (l - 1).toNat := by
  unfold Dg gam Ordinates.D
  congr 2; omega

/-- Reindexing the gap sum of Theorem 7.3 to `ℕ`. -/
lemma gap_sum_reindex (Z : ZetaInputs) {ℓ₀ ℓ₁ : ℕ} (h0 : 1 ≤ ℓ₀) :
    ∑ l ∈ Finset.Ico (ℓ₀ : ℤ) ((ℓ₁ : ℤ) + 1), (Dg (gam Z) l) ^ 3
      = ∑ i ∈ Finset.Ico (ℓ₀ - 1) ℓ₁, Z.D i ^ 3 := by
  refine Finset.sum_nbij' (fun l => (l - 1).toNat) (fun i => (i : ℤ) + 1) ?_ ?_ ?_ ?_ ?_
  · intro l hl; simp only [Finset.mem_Ico] at hl ⊢; omega
  · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
  · intro l hl; simp only [Finset.mem_Ico] at hl; omega
  · intro i hi; omega
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    rw [Dg_gam Z (by omega)]

/-- **Gap sum on the window**: `Σ_{l} D_l³ ≤ (15/4) B T / log²(T/8π)` over the gaps meeting `(T/2, 3T]`. -/
lemma gap_window (Z : ZetaInputs) {Bg T₁ : ℝ} (hBg : 0 ≤ Bg)
    (hG3 : ∀ T : ℝ, T₁ ≤ T → ∑ ℓ ∈ Finset.Ico (Z.N T) (Z.N (2 * T)), Z.D ℓ ^ 3
      ≤ Bg * T / (Real.log (T / (2 * π))) ^ 2)
    {k₀ : ℕ} (hk₀ : ∀ k : ℕ, k₀ ≤ k → Z.D k ≤ 1)
    {T : ℝ} (hT : 4 * T₁ ≤ T) (hTg : 4 * Z.γ k₀ ≤ T) (hT4 : 3600 ≤ T) :
    ∑ l ∈ Finset.Ico (Z.N (T / 2) : ℤ) ((Z.N (3 * T) : ℤ) + 1), (Dg (gam Z) l) ^ 3
      ≤ 4 * Bg * T / (Real.log (T / (8 * π))) ^ 2 := by
  have hpi := Real.pi_pos
  have hpi4 := pi_lt_four
  -- an ordinate in (T/4, T/2]
  have hNq : Z.N (T / 4) + 1 ≤ Z.N (T / 2) := by
    set i := Z.N (T / 4)
    have hi : k₀ < i := (Z.lt_N_iff (T / 4) k₀).mpr (by linarith)
    have h1 : Z.γ (i - 1) ≤ T / 4 := (Z.lt_N_iff (T / 4) (i - 1)).mp (by omega)
    have h2 : Z.D (i - 1) ≤ 1 := hk₀ (i - 1) (by omega)
    have h3 : Z.γ i ≤ T / 2 := by
      have : Z.D (i - 1) = Z.γ i - Z.γ (i - 1) := by
        unfold Ordinates.D; congr 2; omega
      linarith
    exact (Z.lt_N_iff (T / 2) i).mpr h3
  have hNa : 1 ≤ Z.N (T / 2) := by omega
  rw [gap_sum_reindex Z hNa]
  have hD0 : ∀ i, 0 ≤ Z.D i ^ 3 := fun i => pow_nonneg (Z.D_nonneg i) 3
  have hsub : Finset.Ico (Z.N (T / 2) - 1) (Z.N (3 * T)) ⊆ Finset.Ico (Z.N (T / 4)) (Z.N (4 * T)) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    have := Z.N_mono (show 3 * T ≤ 4 * T by linarith)
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hD0 i)) ?_
  have m1 : Z.N (T / 4) ≤ Z.N (T / 2) := Z.N_mono (by linarith)
  have m2 : Z.N (T / 2) ≤ Z.N T := Z.N_mono (by linarith)
  have m3 : Z.N T ≤ Z.N (2 * T) := Z.N_mono (by linarith)
  have m4 : Z.N (2 * T) ≤ Z.N (4 * T) := Z.N_mono (by linarith)
  rw [← Finset.sum_Ico_consecutive _ m1 (le_trans m2 (le_trans m3 m4)),
    ← Finset.sum_Ico_consecutive _ m2 (le_trans m3 m4), ← Finset.sum_Ico_consecutive _ m3 m4]
  set L := Real.log (T / (8 * π))
  have hL1 : 1 ≤ L := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hL : 0 < L := by linarith
  have piece : ∀ T' : ℝ, T / 4 ≤ T' → T₁ ≤ T' →
      ∑ ℓ ∈ Finset.Ico (Z.N T') (Z.N (2 * T')), Z.D ℓ ^ 3 ≤ Bg * T' / L ^ 2 := by
    intro T' h1 h2
    refine le_trans (hG3 T' h2) ?_
    have hT' : 0 < T' := by linarith
    have hl : L ≤ Real.log (T' / (2 * π)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hL.le hl 2
  have p1 := piece (T / 4) le_rfl (by linarith)
  have p2 := piece (T / 2) (by linarith) (by linarith)
  have p3 := piece T (by linarith) (by linarith)
  have p4 := piece (2 * T) (by linarith) (by linarith)
  rw [show 2 * (T / 4) = T / 2 by ring] at p1
  rw [show 2 * (T / 2) = T by ring] at p2
  rw [show 2 * (2 * T) = 4 * T by ring] at p4
  have e : Bg * (T / 4) / L ^ 2 + Bg * (T / 2) / L ^ 2 + Bg * T / L ^ 2 + Bg * (2 * T) / L ^ 2
      = 15 / 4 * (Bg * T / L ^ 2) := by field_simp; ring
  have h15 : 15 / 4 * (Bg * T / L ^ 2) ≤ 4 * Bg * T / L ^ 2 := by
    rw [show 4 * Bg * T / L ^ 2 = 4 * (Bg * T / L ^ 2) by ring]
    have : 0 ≤ Bg * T / L ^ 2 := by positivity
    linarith
  linarith

lemma sqrt_bound {G Q c d T L : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hT : 0 ≤ T) (hL : 0 < L)
    (hG0 : 0 ≤ G) (hQ0 : 0 ≤ Q) (hG : G ≤ c * T / L ^ 2) (hQ : Q ≤ d * T) :
    G ^ ((1 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2) ≤ Real.sqrt (c * d) * T / L := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hG0]
  have h : G * Q ≤ (Real.sqrt (c * d) * T / L) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc G * Q ≤ (c * T / L ^ 2) * (d * T) := mul_le_mul hG hQ hQ0 (by positivity)
      _ = c * d * T ^ 2 / L ^ 2 := by field_simp
  calc Real.sqrt (G * Q) ≤ Real.sqrt ((Real.sqrt (c * d) * T / L) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (c * d) * T / L := Real.sqrt_sq (by positivity)

/-- **Theorem 1.5 (localisation by primes)**, mean-square part, under the explicit hypotheses
`FujiiA`, `FujiiB`, `Titchmarsh`:
`Σ_{T < γ_k ≤ 2T} (x_k − γ_k)² ≤ C · T / log T` for `T ≥ T₀`. -/
theorem sublevel_mean_square (Z : ZetaInputs) (hA : Z.FujiiA) (hB : Z.FujiiB) (hTi : Z.Titchmarsh) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (xClock k - Z.γ (k - 1)) ^ 2 ≤ C * T / Real.log T := by
  obtain ⟨⟨CS, TS, hS0⟩, hgap0⟩ := hTi
  set C := max CS 0
  have hC : 0 ≤ C := le_max_right _ _
  have hS : ∀ t : ℝ, max TS 1 ≤ t → |Z.S t| ≤ C * Real.log t := by
    intro t ht
    refine le_trans (hS0 t (le_trans (le_max_left _ _) ht)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (le_trans (le_max_right _ _) ht))
  obtain ⟨k₀, hk₀⟩ := hgap0 1 one_pos
  have hgap : ∃ G : ℝ, ∀ ℓ, G ≤ Z.γ ℓ → Z.D ℓ ≤ 1 := by
    refine ⟨Z.γ k₀ + 1, fun ℓ hℓ => hk₀ ℓ ?_⟩
    by_contra h; push Not at h
    have := Z.mono h.le; linarith
  obtain ⟨Bg, T₁, hBg, hG3⟩ := Z.gaps_third_moment hB hgap
  obtain ⟨BQ, T₂, hBQ, hT₂, hQ⟩ := Q_bound Z hA
  set K := 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * Real.sqrt (4 * Bg * BQ)
  refine ⟨2 * K, max (max (max (max TS 1) (Tbig C)) (max (4 * T₁) (4 * |Z.γ k₀|))) T₂, by positivity, ?_⟩
  intro T hT
  have hTS : max TS 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hT
  have hTb : Tbig C ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hT
  have hT1 : 4 * T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hT
  have hTg' : 4 * |Z.γ k₀| ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hT
  have hTg : 4 * Z.γ k₀ ≤ T := le_trans (by linarith [le_abs_self (Z.γ k₀)]) hTg'
  have hT2 : T₂ ≤ T := le_trans (le_max_right _ _) hT
  have hT3600 : 3600 ≤ T := le_trans (Tbig_ge C hC) hTb
  have hpi := Real.pi_pos
  have hpi4 := pi_lt_four
  set a := T / 2 with ha
  set b := 3 * T with hb
  -- N(a) ≥ 1
  have hNa : 1 ≤ Z.N a := by
    have : 0 < Z.N a := (Z.lt_N_iff a 0).mpr (by have := Z.mono (Nat.zero_le k₀); linarith)
    omega
  have W := window Z (show a < b by simp only [a, b]; linarith) hNa
  obtain ⟨hQi, hQb⟩ := hQ T hT2 hNa
  have htr := transfer W continuous_Fx.measurable hQi
  have hGw := gap_window Z hBg hG3 hk₀ hT1 hTg hT3600
  -- the left-hand side is a sub-sum of the transfer sum
  have hsum : ∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (xClock k - Z.γ (k - 1)) ^ 2
      ≤ ∑ k ∈ Finset.Ioc (Z.N a : ℤ) (Z.N b), (xk Fx a b k - gam Z k) ^ 2 := by
    have e : ∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (xClock k - Z.γ (k - 1)) ^ 2
        = ∑ k ∈ (Finset.Ioc (Z.N T) (Z.N (2 * T))).map Nat.castEmbedding, (xk Fx a b k - gam Z k) ^ 2 := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_Ioc.mp hk
      simp only [Nat.castEmbedding_apply]
      rw [xClock_eq Z hC hS hTS hTb hk'.1 hk'.2, gam_natCast Z (by omega)]
    rw [e]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
    intro l hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hl
    have hk' := Finset.mem_Ioc.mp hk
    have h1 : Z.N a ≤ Z.N T := Z.N_mono (by simp only [a]; linarith)
    have h2 : Z.N (2 * T) ≤ Z.N b := Z.N_mono (by simp only [b]; linarith)
    simp only [Nat.castEmbedding_apply, Finset.mem_Ioc]
    omega
  -- assemble
  set L := Real.log (T / (8 * π))
  have hL1 : 1 ≤ L := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hG0 : 0 ≤ ∑ l ∈ Finset.Ico (Z.N a : ℤ) ((Z.N b : ℤ) + 1), (Dg (gam Z) l) ^ 3 :=
    Finset.sum_nonneg (fun l _ => pow_nonneg (Dg_nonneg (gam_mono Z) l) 3)
  have hQ0 : 0 ≤ ∫ t in Ioc a b, (qf (gam Z) (Z.N a) (Z.N b) Fx t) ^ 4 :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => by positivity)
  have hsq := sqrt_bound (c := 4 * Bg) (d := BQ) (by positivity) hBQ (by linarith) (by linarith)
    hG0 hQ0 (by rw [show 4 * Bg * T / L ^ 2 = 4 * Bg * T / L ^ 2 from rfl]; exact hGw) hQb
  have hcst : 0 ≤ 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have step : ∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (xClock k - Z.γ (k - 1)) ^ 2 ≤ K * T / L := by
    refine le_trans hsum (le_trans htr ?_)
    rw [mul_assoc]
    calc 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * (_ ^ ((1 : ℝ) / 2) * _ ^ ((1 : ℝ) / 2))
        ≤ 2 * (24 : ℝ) ^ ((1 : ℝ) / 3) * (Real.sqrt (4 * Bg * BQ) * T / L) :=
          mul_le_mul_of_nonneg_left hsq hcst
      _ = K * T / L := by simp only [K]; ring
  -- log(T/8π) ≥ log T / 2
  have hLT : Real.log T / 2 ≤ L := by
    have hs : 8 * π ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by positivity) (by linarith)]; nlinarith
    have : Real.sqrt T ≤ T / (8 * π) := by
      rw [le_div_iff₀ (by positivity)]
      have := Real.sq_sqrt (show 0 ≤ T by linarith)
      nlinarith [Real.sqrt_nonneg T]
    have h := Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) this
    rw [Real.log_sqrt (by linarith)] at h
    exact h
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hK0 : 0 ≤ K * T := by positivity
  calc _ ≤ K * T / L := step
    _ ≤ K * T / (Real.log T / 2) := div_le_div_of_nonneg_left hK0 (by positivity) hLT
    _ = 2 * K * T / Real.log T := by field_simp

/-- `#𝒦_T = N(2T) − N(T) ≥ T log T / (8π)` for `T` large (from `S = O(log t)`). -/
lemma card_KT_ge (Z : ZetaInputs) {C T₀ : ℝ} (hC : 0 ≤ C)
    (hS : ∀ t : ℝ, T₀ ≤ t → |Z.S t| ≤ C * Real.log t) {T : ℝ} (hT0 : T₀ ≤ T) (hT : Tbig C ≤ T) :
    T * Real.log T / (8 * π) ≤ ((Finset.Ioc (Z.N T) (Z.N (2 * T))).card : ℝ) := by
  have hT3600 := Tbig_ge C hC
  have hpi := Real.pi_pos
  have hpi4 := pi_lt_four
  have hTp : 0 < T := by linarith
  have hmono : Z.N T ≤ Z.N (2 * T) := Z.N_mono (by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hmono]
  have h1 := Z.N_ge (2 * T) (by linarith)
  have h2 := Z.N_le T (by linarith)
  have s1 := hS (2 * T) (by linarith)
  have s2 := hS T hT0
  have hgain := N0_sub_ge hTp (by linarith : T ≤ 2 * T)
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTp]; have := Real.exp_one_lt_d9; linarith
  have hl2 : Real.log (2 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) hTp.ne']
    have : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hhalf : Real.log T / 2 ≤ Real.log (T / (2 * π)) := by
    have hs : 2 * π ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by positivity) hTp.le]; nlinarith
    have : Real.sqrt T ≤ T / (2 * π) := by
      rw [le_div_iff₀ (by positivity)]
      have := Real.sq_sqrt hTp.le
      nlinarith [Real.sqrt_nonneg T]
    have h := Real.log_le_log (Real.sqrt_pos.mpr hTp) this
    rw [Real.log_sqrt hTp.le] at h
    exact h
  have hmain : T * Real.log T / (4 * π) ≤ (2 * T - T) * Real.log (T / (2 * π)) / (2 * π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : T * (Real.log T / 2) ≤ T * Real.log (T / (2 * π)) := mul_le_mul_of_nonneg_left hhalf hTp.le
    nlinarith
  have hC4 : C * Real.log (2 * T) + C * Real.log T + 2 ≤ T * Real.log T / (8 * π) := by
    have hc1 : C * Real.log (2 * T) ≤ C * (2 * Real.log T) := mul_le_mul_of_nonneg_left hl2 hC
    have hTC : 64 * (1 + 2 * C) ≤ T := by
      have : 64 * (1 + 2 * C) ≤ Tbig C := by unfold Tbig; nlinarith
      linarith
    have : (3 * C + 2) * Real.log T ≤ T * Real.log T / (8 * π) := by
      rw [le_div_iff₀ (by positivity)]
      have : (3 * C + 2) * (8 * π) ≤ T := by nlinarith
      nlinarith
    nlinarith
  have e : T * Real.log T / (8 * π) = T * Real.log T / (4 * π) - T * Real.log T / (8 * π) := by
    field_simp; ring
  linarith

/-- **Theorem 1.5**, both forms: `Σ_{𝒦_T} (x_k − γ_k)² ≤ C T / log T` and the mean `≤ C' / log² T`. -/
theorem sublevel (Z : ZetaInputs) (hA : Z.FujiiA) (hB : Z.FujiiB) (hTi : Z.Titchmarsh) :
    ∃ C C' T₀ : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ T : ℝ, T₀ ≤ T →
      ∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (xClock k - Z.γ (k - 1)) ^ 2 ≤ C * T / Real.log T ∧
      (∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (xClock k - Z.γ (k - 1)) ^ 2)
          / (Finset.Ioc (Z.N T) (Z.N (2 * T))).card ≤ C' / (Real.log T) ^ 2 ∧
      T * Real.log T / (8 * π) ≤ ((Finset.Ioc (Z.N T) (Z.N (2 * T))).card : ℝ) := by
  obtain ⟨C, T₀, hC, hmain⟩ := sublevel_mean_square Z hA hB hTi
  obtain ⟨⟨CS, TS, hS0⟩, -⟩ := hTi
  set CS' := max CS 0
  have hCS : 0 ≤ CS' := le_max_right _ _
  have hS : ∀ t : ℝ, max TS 1 ≤ t → |Z.S t| ≤ CS' * Real.log t := by
    intro t ht
    refine le_trans (hS0 t (le_trans (le_max_left _ _) ht)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (le_trans (le_max_right _ _) ht))
  refine ⟨C, 8 * π * C, max (max T₀ (max TS 1)) (Tbig CS'), hC, by positivity, fun T hT => ?_⟩
  have hT0 : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTS : max TS 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTb : Tbig CS' ≤ T := le_trans (le_max_right _ _) hT
  have hT3600 := le_trans (Tbig_ge CS' hCS) hTb
  have hpi := Real.pi_pos
  have h1 := hmain T hT0
  have hK := card_KT_ge Z hCS hS hTS hTb
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  refine ⟨h1, ?_, hK⟩
  have hKpos : 0 < ((Finset.Ioc (Z.N T) (Z.N (2 * T))).card : ℝ) :=
    lt_of_lt_of_le (by positivity) hK
  rw [div_le_iff₀ hKpos]
  calc _ ≤ C * T / Real.log T := h1
    _ = 8 * π * C / Real.log T ^ 2 * (T * Real.log T / (8 * π)) := by field_simp
    _ ≤ 8 * π * C / Real.log T ^ 2 * ((Finset.Ioc (Z.N T) (Z.N (2 * T))).card : ℝ) :=
        mul_le_mul_of_nonneg_left hK (by positivity)

/-- **Corollary 1.6.** `#{k ∈ 𝒦_T : |x_k − γ_k| > A·2π/log T} ≤ (C''/A²) #𝒦_T`. -/
theorem proportion (Z : ZetaInputs) (hA : Z.FujiiA) (hB : Z.FujiiB) (hTi : Z.Titchmarsh) :
    ∃ C'' T₀ : ℝ, 0 ≤ C'' ∧ ∀ A : ℝ, 0 < A → ∀ T : ℝ, T₀ ≤ T →
      (((Finset.Ioc (Z.N T) (Z.N (2 * T))).filter
          (fun k => A * (2 * π / Real.log T) < |xClock k - Z.γ (k - 1)|)).card : ℝ)
        ≤ C'' / A ^ 2 * (Finset.Ioc (Z.N T) (Z.N (2 * T))).card := by
  obtain ⟨C, C', T₀, hC, hC', hmain⟩ := sublevel Z hA hB hTi
  refine ⟨C' / (4 * π ^ 2), max T₀ 3, by positivity, fun A hA0 T hT => ?_⟩
  have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨-, hmean, -⟩ := hmain T hT0
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hpi := Real.pi_pos
  set K := Finset.Ioc (Z.N T) (Z.N (2 * T))
  set c := A * (2 * π / Real.log T)
  have hc : 0 < c := by positivity
  set E := K.filter (fun k => c < |xClock k - Z.γ (k - 1)|)
  have hE : (E.card : ℝ) * c ^ 2 ≤ ∑ k ∈ K, (xClock k - Z.γ (k - 1)) ^ 2 := by
    calc (E.card : ℝ) * c ^ 2 = ∑ k ∈ E, c ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ E, (xClock k - Z.γ (k - 1)) ^ 2 := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have := (Finset.mem_filter.mp hk).2
          rw [← sq_abs (xClock k - Z.γ (k - 1))]
          exact pow_le_pow_left₀ hc.le this.le 2
      _ ≤ ∑ k ∈ K, (xClock k - Z.γ (k - 1)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  by_cases hK0 : (K.card : ℝ) = 0
  · have : E.card = 0 := by
      have : K.card = 0 := by exact_mod_cast hK0
      exact Nat.eq_zero_of_le_zero (this ▸ Finset.card_filter_le _ _)
    rw [this, hK0]; simp
  have hKpos : 0 < (K.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hK0)
  have hsum : ∑ k ∈ K, (xClock k - Z.γ (k - 1)) ^ 2 ≤ C' / Real.log T ^ 2 * K.card := by
    rwa [div_le_iff₀ hKpos] at hmean
  have hc2 : c ^ 2 = A ^ 2 * (4 * π ^ 2) / Real.log T ^ 2 := by simp only [c]; field_simp; ring
  rw [hc2] at hE
  have : (E.card : ℝ) * (A ^ 2 * (4 * π ^ 2)) ≤ C' * K.card := by
    have h := le_trans hE hsum
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)] at h
    linarith
  rw [div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Theorem 1.5 for Casaña's method**: the same statement as `sublevel`, written with `casanya_method`. -/
theorem casanya_method_sublevel (Z : ZetaInputs) (hA : Z.FujiiA) (hB : Z.FujiiB) (hTi : Z.Titchmarsh) :
    ∃ C C' T₀ : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ T : ℝ, T₀ ≤ T →
      ∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (casanya_method k - Z.γ (k - 1)) ^ 2
          ≤ C * T / Real.log T ∧
      (∑ k ∈ Finset.Ioc (Z.N T) (Z.N (2 * T)), (casanya_method k - Z.γ (k - 1)) ^ 2)
          / (Finset.Ioc (Z.N T) (Z.N (2 * T))).card ≤ C' / (Real.log T) ^ 2 ∧
      T * Real.log T / (8 * π) ≤ ((Finset.Ioc (Z.N T) (Z.N (2 * T))).card : ℝ) := by
  exact sublevel Z hA hB hTi

end RvmClock
