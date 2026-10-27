import PaperMath.Papers.RvmClock.Phase
import PaperMath.Papers.RvmClock.Inputs

/-!
# Lemma 7.6: fourth moment of the counting error

`∫_U^{2U} |𝓕(t) − N(t)|⁴ dt ≪ U` for `U = 2^j`, `j ≥ j₀`, under the hypothesis `FujiiA`
(Theorem 3.8(a) of the article: Selberg's approximation in Fujii's form, `k = 2`, `α_F = 1/5`,
`H = T = U`, `Y = U^{1/200}`).
-/

open MeasureTheory Set Complex Finset
open scoped Real

namespace RvmClock

/-- The primes `p < Y`. -/
noncomputable def primesLt (Y : ℝ) : Finset ℕ := Nat.primesBelow ⌈Y⌉₊

lemma mem_primesLt {Y : ℝ} {p : ℕ} : p ∈ primesLt Y ↔ p.Prime ∧ (p : ℝ) < Y := by
  unfold primesLt
  rw [Nat.mem_primesBelow, Nat.lt_ceil, and_comm]

namespace ZetaInputs

variable (Z : ZetaInputs)

/-- **Hypothesis (Fujii, Theorem 3.8(a), `k = 2`, `α_F = 1/5`, `H = T = U`, `Y = U^{1/200}`).**
`∫_U^{2U} |S(t) − (1/π) Im Σ_{p<Y} p^{-1/2-it}|⁴ dt ≤ A·U` for `U ≥ U₀`. -/
def FujiiA : Prop :=
  ∃ A U₀ : ℝ, 0 ≤ A ∧ ∀ U : ℝ, U₀ ≤ U →
    ∫ t in Icc U (2 * U),
      |Z.S t - 1 / π * (∑ p ∈ primesLt (U ^ (1 / 200 : ℝ)), zp p t).im| ^ 4 ≤ A * U

end ZetaInputs

lemma abs_add_pow4_le (x y : ℝ) : |x + y| ^ 4 ≤ 8 * (|x| ^ 4 + |y| ^ 4) := by
  have h := abs_add_le x y
  have ha := abs_nonneg x
  have hb := abs_nonneg y
  have h1 : |x + y| ^ 4 ≤ (|x| + |y|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) h 4
  have h2 : (|x| + |y|) ^ 4 ≤ 8 * (|x| ^ 4 + |y| ^ 4) := by
    nlinarith [sq_nonneg (|x| - |y|), sq_nonneg (|x| + |y|), sq_nonneg (|x| ^ 2 - |y| ^ 2),
      mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (|x| - |y|))]
  linarith

lemma abs_add4_pow4_le (a b c d : ℝ) :
    |a + b + c + d| ^ 4 ≤ 64 * (|a| ^ 4 + |b| ^ 4 + |c| ^ 4 + |d| ^ 4) := by
  have e : a + b + c + d = (a + b) + (c + d) := by ring
  rw [e]
  have := abs_add_pow4_le (a + b) (c + d)
  have := abs_add_pow4_le a b
  have := abs_add_pow4_le c d
  linarith

/-- The primes `p_ν`, `ν < m`. -/
noncomputable def Pm (m : ℕ) : Finset ℕ := (Finset.range m).image prime

/-- `𝒟₁` and `𝒟₂` as Dirichlet polynomials in the form of `prime_fourth_moment`. -/
noncomputable def D1 (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * ex (t * Real.log ((p : ℝ) ^ 1))

noncomputable def D2 (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, (((1 / (p : ℝ)) : ℝ) : ℂ) * ex (t * Real.log ((p : ℝ) ^ 2))

lemma sum_range_prime (m : ℕ) (f : ℕ → ℝ) :
    ∑ ν ∈ Finset.range m, f (prime ν) = ∑ p ∈ Pm m, f p := by
  unfold Pm; rw [Finset.sum_image (fun a _ b _ h => prime_injective h)]

lemma prime_of_mem_Pm {m p : ℕ} (h : p ∈ Pm m) : p.Prime := by
  obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp h; exact Nat.prime_nth_prime ν

lemma im_D1 (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (D1 P t).im = ∑ p ∈ P, (zp p t).im := by
  unfold D1; rw [Complex.im_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [pow_one, zp_eq (hP p hp).pos]

lemma im_D2 (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (D2 P t).im = ∑ p ∈ P, (zp p t ^ 2).im := by
  unfold D2; rw [Complex.im_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [zp_sq (hP p hp).pos]

/-- If every prime `< Y` is among `p_0, …, p_{m-1}`, the first-order sum splits. -/
lemma split_first {m : ℕ} {Y : ℝ} (hY : primesLt Y ⊆ Pm m) (t : ℝ) :
    ∑ ν ∈ Finset.range m, (zp (prime ν) t).im
      = (∑ p ∈ primesLt Y, zp p t).im + (D1 ((Pm m).filter (fun p => ¬ (p : ℝ) < Y)) t).im := by
  classical
  rw [sum_range_prime m (fun p => (zp p t).im), im_D1 _ (fun p hp => prime_of_mem_Pm (Finset.mem_filter.mp hp).1),
    Complex.im_sum, ← Finset.sum_filter_add_sum_filter_not (Pm m) (fun p => (p : ℝ) < Y)]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩; exact mem_primesLt.mpr ⟨prime_of_mem_Pm h1, h2⟩
  · intro h; exact ⟨hY h, (mem_primesLt.mp h).2⟩

lemma split_second (m : ℕ) (t : ℝ) :
    ∑ ν ∈ Finset.range m, (zp (prime ν) t ^ 2).im = (D2 (Pm m) t).im := by
  rw [sum_range_prime m (fun p => (zp p t ^ 2).im), im_D2 _ (fun p hp => prime_of_mem_Pm hp)]

lemma abs_im_div_le (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1) (w : ℂ) : |c * w.im| ≤ ‖w‖ := by
  rw [abs_mul, abs_of_nonneg hc0]
  calc c * |w.im| ≤ 1 * |w.im| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ ‖w‖ := by rw [one_mul]; exact Complex.abs_im_le_norm w

lemma pi_inv_le_one : 1 / π ≤ 1 := by
  rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]

/-- Pointwise bound for `N₀ + Φ_m − N` (the five pieces of the proof of Lemma 7.6). -/
lemma pointwise_A (Z : ZetaInputs) {K : ℝ}
    (hK : ∀ (m : ℕ) (t : ℝ), |PhiM m t - (1 / π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t).im
        - 1 / (2 * π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t ^ 2).im| ≤ K)
    {m : ℕ} {Y t : ℝ} (hY : primesLt Y ⊆ Pm m) (ht : 1 ≤ t) :
    |N0 t + PhiM m t - Z.N t| ^ 4 ≤
      64 * (|Z.S t - 1 / π * (∑ p ∈ primesLt Y, zp p t).im| ^ 4
        + ‖D1 ((Pm m).filter (fun p => ¬ (p : ℝ) < Y)) t‖ ^ 4 + ‖D2 (Pm m) t‖ ^ 4 + (K + 1) ^ 4) := by
  set R := PhiM m t - (1 / π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t).im
        - 1 / (2 * π) * ∑ ν ∈ Finset.range m, (zp (prime ν) t ^ 2).im with hR
  set sel := (∑ p ∈ primesLt Y, zp p t).im
  set E1 := D1 ((Pm m).filter (fun p => ¬ (p : ℝ) < Y)) t
  set E2 := D2 (Pm m) t
  have h1 := split_first hY t
  have h2 := split_second m t
  have hdec : N0 t + PhiM m t - Z.N t
      = (1 / π * sel - Z.S t) + 1 / π * E1.im + 1 / (2 * π) * E2.im + (R - Z.varpi t / π) := by
    have hS : Z.S t = (Z.N t : ℝ) - N0 t - Z.varpi t / π := rfl
    rw [hS, hR, h1, h2]; ring
  rw [hdec]
  refine le_trans (abs_add4_pow4_le _ _ _ _) ?_
  have hpi := Real.pi_pos
  have b1 : |1 / π * sel - Z.S t| ^ 4 = |Z.S t - 1 / π * sel| ^ 4 := by rw [abs_sub_comm]
  have b2 : |1 / π * E1.im| ^ 4 ≤ ‖E1‖ ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_im_div_le _ (by positivity) pi_inv_le_one E1) 4
  have b3 : |1 / (2 * π) * E2.im| ^ 4 ≤ ‖E2‖ ^ 4 := by
    refine pow_le_pow_left₀ (abs_nonneg _) (abs_im_div_le _ (by positivity) ?_ E2) 4
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have b4 : |R - Z.varpi t / π| ^ 4 ≤ (K + 1) ^ 4 := by
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
    have hv := Z.varpi_bound t ht
    have hv1 : |Z.varpi t / π| ≤ 1 := by
      rw [abs_div, abs_of_pos hpi, div_le_one hpi]
      have : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; exact ht
      linarith [Real.pi_gt_three]
    have := abs_sub R (Z.varpi t / π)
    have := hK m t
    linarith
  rw [b1]
  linarith

lemma Icc_eq_interval (f : ℝ → ℝ) {U : ℝ} (hU : 0 ≤ U) :
    ∫ t in Icc U (2 * U), f t = ∫ t in U..2 * U, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

lemma sum_card_bound (P : Finset ℕ) (k : ℕ) (c : ℕ → ℝ)
    (hc : ∀ p ∈ P, ((p : ℝ) ^ k + 1) * c p ≤ 2) :
    ∑ p ∈ P, ((p : ℝ) ^ k + 1) * c p ≤ 2 * P.card := by
  calc ∑ p ∈ P, ((p : ℝ) ^ k + 1) * c p ≤ ∑ p ∈ P, (2 : ℝ) := Finset.sum_le_sum hc
    _ = 2 * P.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Fourth moments of `𝒟₁` and `𝒟₂` over `[U, 2U]`. -/
theorem D_moments :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ U : ℝ, 0 ≤ U →
      (∫ t in Icc U (2 * U), ‖D1 P t‖ ^ 4 ≤ 2 * U * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 + 2 * C * (2 * (P.card : ℝ)) ^ 2) ∧
      (∫ t in Icc U (2 * U), ‖D2 P t‖ ^ 4 ≤ 2 * U * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ^ 2 + 2 * C * (2 * (P.card : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hM⟩ := prime_fourth_moment
  refine ⟨C, hC, fun P hP U hU => ⟨?_, ?_⟩⟩
  · rw [Icc_eq_interval (fun t => ‖D1 P t‖ ^ 4) hU]
    have h := hM P hP 1 le_rfl (fun p => (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) U hU
    have e1 : ∀ p ∈ P, ‖((((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))‖ ^ 2 = 1 / (p : ℝ) := by
      intro p hp
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), rpow_half_sq']
      exact_mod_cast (hP p hp).pos
    rw [Finset.sum_congr rfl e1] at h
    have hW : ∑ p ∈ P, ((p : ℝ) ^ 1 + 1) * ‖((((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))‖ ^ 2 ≤ 2 * (P.card : ℝ) := by
      refine sum_card_bound P 1 _ (fun p hp => ?_)
      rw [e1 p hp, pow_one]
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
      rw [show ((p : ℝ) + 1) * (1 / p) = 1 + 1 / p by field_simp]
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hW0 : 0 ≤ ∑ p ∈ P, ((p : ℝ) ^ 1 + 1) * ‖((((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => by positivity)
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW 2) (by positivity : (0:ℝ) ≤ 2 * C)
    unfold D1; linarith
  · rw [Icc_eq_interval (fun t => ‖D2 P t‖ ^ 4) hU]
    have h := hM P hP 2 (by norm_num) (fun p => (((1 / (p : ℝ)) : ℝ) : ℂ)) U hU
    have e1 : ∀ p ∈ P, ‖((((1 / (p : ℝ)) : ℝ) : ℂ))‖ ^ 2 = 1 / (p : ℝ) ^ 2 := by
      intro p hp
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    rw [Finset.sum_congr rfl e1] at h
    have hW : ∑ p ∈ P, ((p : ℝ) ^ 2 + 1) * ‖((((1 / (p : ℝ)) : ℝ) : ℂ))‖ ^ 2 ≤ 2 * (P.card : ℝ) := by
      refine sum_card_bound P 2 _ (fun p hp => ?_)
      rw [e1 p hp]
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
      have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      rw [show ((p : ℝ) ^ 2 + 1) * (1 / (p : ℝ) ^ 2) = 1 + 1 / (p : ℝ) ^ 2 by field_simp]
      have : 1 / (p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one hp2]; nlinarith
      linarith
    have hW0 : 0 ≤ ∑ p ∈ P, ((p : ℝ) ^ 2 + 1) * ‖((((1 / (p : ℝ)) : ℝ) : ℂ))‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => by positivity)
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW 2) (by positivity : (0:ℝ) ≤ 2 * C)
    unfold D2; linarith

lemma rpow_two_sq_half (J : ℝ) : ((2 : ℝ) ^ (J / 4)) ^ 2 = (2 : ℝ) ^ (J / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num; ring_nf

lemma Y_eq (J : ℝ) : ((2 : ℝ) ^ J) ^ (1 / 200 : ℝ) = (2 : ℝ) ^ (J / 200) := by
  rw [← Real.rpow_mul (by norm_num)]; ring_nf

/-- Arithmetic of a block: `Y = U^{1/200} ≤ m`, the primes `< Y` are among the first `m`,
and `Σ_{Y ≤ p ≤ p_{m-1}} 1/p ≤ 400`. -/
lemma block_arith {J : ℝ} (hJ : 8 ≤ J) {m : ℕ} (hlo : (2 : ℝ) ^ (J / 2) - 1 ≤ m)
    (hhi : (m : ℝ) ^ 2 ≤ (2 : ℝ) ^ (J + 1)) :
    primesLt (((2 : ℝ) ^ J) ^ (1 / 200 : ℝ)) ⊆ Pm m ∧
    ∑ p ∈ (Pm m).filter (fun p : ℕ => ¬ (p : ℝ) < ((2 : ℝ) ^ J) ^ (1 / 200 : ℝ)), 1 / (p : ℝ) ≤ 400 ∧
    (Pm m).card ≤ m := by
  classical
  rw [Y_eq]
  set Y := (2 : ℝ) ^ (J / 200)
  set r := (2 : ℝ) ^ (J / 4)
  have hr4 : 4 ≤ r := by
    have : (2 : ℝ) ^ (2 : ℝ) ≤ r := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at this; linarith
  have hYr : Y ≤ r := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hr2 : r ^ 2 = (2 : ℝ) ^ (J / 2) := rpow_two_sq_half J
  have hYm : Y ≤ m := by nlinarith
  have hm8 : 8 ≤ m := by
    have : (8 : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  have hY1 : 1 < Y := Real.one_lt_rpow (by norm_num) (by linarith)
  refine ⟨?_, ?_, Finset.card_image_le.trans (by simp)⟩
  · intro p hp
    obtain ⟨hpp, hpY⟩ := mem_primesLt.mp hp
    have hpm : p < m := by
      have : (p : ℝ) < m := lt_of_lt_of_le hpY hYm
      exact_mod_cast this
    refine Finset.mem_image.mpr ⟨Nat.count Nat.Prime p, Finset.mem_range.mpr ?_, Nat.nth_count hpp⟩
    exact lt_of_le_of_lt (Nat.count_le Nat.Prime) hpm
  · have hsub : (Pm m).filter (fun p : ℕ => ¬ (p : ℝ) < Y)
        ⊆ (Nat.primesLE (m ^ 2)).filter (fun p : ℕ => Y ≤ (p : ℝ)) := by
      intro p hp
      obtain ⟨hpP, hpY⟩ := Finset.mem_filter.mp hp
      obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hpP
      have hν' : ν ≤ m - 1 := by have := Finset.mem_range.mp hν; omega
      refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, Nat.prime_nth_prime ν⟩, not_lt.mp hpY⟩
      exact le_trans (Nat.nth_monotone Nat.infinite_setOf_prime hν') (nth_prime_le_sq hm8)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) ?_
    refine le_trans (sum_inv_prime_le (Nat.one_le_iff_ne_zero.mpr (by positivity)) hY1) ?_
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hlY : Real.log Y = J / 200 * Real.log 2 := Real.log_rpow (by norm_num) _
    have hlm : Real.log ((m ^ 2 : ℕ) : ℝ) ≤ (J + 1) * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      push_cast
      exact Real.log_le_log (by positivity) hhi
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [hlY, hl4, div_le_iff₀ (by positivity)]
    nlinarith

lemma continuous_D1 (P : Finset ℕ) : Continuous (D1 P) := by
  unfold D1
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_ex_mul _))

lemma continuous_D2 (P : Finset ℕ) : Continuous (D2 P) := by
  unfold D2
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_ex_mul _))

lemma sel_eq (Y t : ℝ) : (∑ p ∈ primesLt Y, zp p t).im = (D1 (primesLt Y) t).im := by
  rw [im_D1 _ (fun p hp => (mem_primesLt.mp hp).1), Complex.im_sum]

lemma integrableOn_f1 (Z : ZetaInputs) {U Y : ℝ} (hU : 1 ≤ U) :
    IntegrableOn (fun t => |Z.S t - 1 / π * (∑ p ∈ primesLt Y, zp p t).im| ^ 4) (Icc U (2 * U)) := by
  simp_rw [sel_eq]
  obtain ⟨B, hB⟩ := Z.S_bounded (a := U) (b := 2 * U) hU
  obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_D1 (primesLt Y)).continuousOn (s := Icc U (2 * U))
  have hmeas : Measurable (fun t => |Z.S t - 1 / π * (D1 (primesLt Y) t).im| ^ 4) := by
    have h1 : Measurable (fun t => (D1 (primesLt Y) t).im) :=
      Complex.continuous_im.measurable.comp (continuous_D1 _).measurable
    exact (continuous_abs.measurable.comp (Z.S_measurable.sub (h1.const_mul _))).pow_const 4
  refine IntegrableOn.of_bound (by simp) hmeas.aestronglyMeasurable ((B + B') ^ 4) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_pow, abs_abs]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
  have h1 := hB t ht
  have h2 : |1 / π * (D1 (primesLt Y) t).im| ≤ B' :=
    le_trans (abs_im_div_le _ (by positivity) pi_inv_le_one _) (hB' t ht)
  have := abs_sub (Z.S t) (1 / π * (D1 (primesLt Y) t).im)
  linarith

lemma sum_inv_sq_le (m : ℕ) :
    ∑ p ∈ Pm m, 1 / (p : ℝ) ^ 2 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  rw [← sum_range_prime m (fun p => 1 / (p : ℝ) ^ 2)]
  refine le_trans (Finset.sum_le_sum (fun ν _ => ?_)) (sum_prime_rpow32_le m)
  have hp : (1 : ℝ) ≤ (prime ν : ℕ) := by exact_mod_cast (Nat.prime_nth_prime ν).one_lt.le
  have : (1 : ℝ) / ((prime ν : ℕ) : ℝ) ^ 2 = ((prime ν : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), one_div]; norm_cast
  rw [this]
  exact Real.rpow_le_rpow_of_exponent_le hp (by norm_num)

/-- **Integrable majorant of `|N₀ + Φ_m − N|⁴` on `[U, 2U]`**, `U = 2^J`, with integral `≤ B·U`. -/
theorem A_moment (Z : ZetaInputs) (hFA : Z.FujiiA) :
    ∃ B U₁ : ℝ, 0 ≤ B ∧ ∀ J : ℝ, 8 ≤ J → U₁ ≤ (2 : ℝ) ^ J → ∀ m : ℕ,
      (2 : ℝ) ^ (J / 2) - 1 ≤ m → (m : ℝ) ^ 2 ≤ (2 : ℝ) ^ (J + 1) →
      ∃ g : ℝ → ℝ, IntegrableOn g (Icc ((2 : ℝ) ^ J) (2 * (2 : ℝ) ^ J)) ∧
        (∀ t ∈ Icc ((2 : ℝ) ^ J) (2 * (2 : ℝ) ^ J), |N0 t + PhiM m t - Z.N t| ^ 4 ≤ g t) ∧
        ∫ t in Icc ((2 : ℝ) ^ J) (2 * (2 : ℝ) ^ J), g t ≤ B * (2 : ℝ) ^ J := by
  obtain ⟨K, hK0, hK⟩ := PhiM_expand
  obtain ⟨C, hC0, hD⟩ := D_moments
  obtain ⟨A, U₀, hA0, hA⟩ := hFA
  set Z32 := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ)
  have hZ32 : 0 ≤ Z32 := tsum_nonneg (fun n => by positivity)
  refine ⟨64 * (A + 320000 + 32 * C + 2 * Z32 ^ 2 + (K + 1) ^ 4), U₀, by positivity, ?_⟩
  intro J hJ hU₀ m hlo hhi
  set U := (2 : ℝ) ^ J with hUdef
  have hU1 : 1 ≤ U := Real.one_le_rpow (by norm_num) (by linarith)
  have hU0 : 0 ≤ U := by linarith
  have h2U : (2 : ℝ) ^ (J + 1) = 2 * U := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  rw [h2U] at hhi
  obtain ⟨hsub, hV, hcard⟩ := block_arith hJ hlo (by rw [h2U]; exact hhi)
  set Y := U ^ (1 / 200 : ℝ)
  set P1 := (Pm m).filter (fun p : ℕ => ¬ (p : ℝ) < Y)
  have hP1 : ∀ p ∈ P1, p.Prime := fun p hp => prime_of_mem_Pm (Finset.mem_filter.mp hp).1
  have hPm : ∀ p ∈ Pm m, p.Prime := fun p hp => prime_of_mem_Pm hp
  set f1 := fun t => |Z.S t - 1 / π * (∑ p ∈ primesLt Y, zp p t).im| ^ 4
  set f2 := fun t => ‖D1 P1 t‖ ^ 4
  set f3 := fun t => ‖D2 (Pm m) t‖ ^ 4
  have i1 : IntegrableOn f1 (Icc U (2 * U)) := integrableOn_f1 Z hU1
  have i2 : IntegrableOn f2 (Icc U (2 * U)) :=
    ((continuous_D1 P1).norm.pow 4).integrableOn_Icc
  have i3 : IntegrableOn f3 (Icc U (2 * U)) :=
    ((continuous_D2 (Pm m)).norm.pow 4).integrableOn_Icc
  have ic : IntegrableOn (fun _ : ℝ => (K + 1) ^ 4) (Icc U (2 * U)) := integrableOn_const (by simp)
  refine ⟨fun t => 64 * (f1 t + f2 t + f3 t + (K + 1) ^ 4), ?_, ?_, ?_⟩
  · exact (((i1.add i2).add i3).add ic).const_mul 64
  · intro t ht
    exact pointwise_A Z hK hsub (le_trans hU1 ht.1)
  · rw [integral_const_mul,
      integral_add (f := fun a => f1 a + f2 a + f3 a) (g := fun _ => (K + 1) ^ 4) ((i1.add i2).add i3) ic,
      integral_add (f := fun a => f1 a + f2 a) (g := f3) (i1.add i2) i3,
      integral_add (f := f1) (g := f2) i1 i2, setIntegral_const, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul]
    have e1 : ∫ t in Icc U (2 * U), f1 t ≤ A * U := hA U hU₀
    obtain ⟨d1, d2⟩ := hD P1 hP1 U hU0
    obtain ⟨-, d3⟩ := hD (Pm m) hPm U hU0
    have hc1 : (P1.card : ℝ) ≤ m := by
      have : P1.card ≤ m := le_trans (Finset.card_filter_le _ _) hcard
      exact_mod_cast this
    have hc2 : ((Pm m).card : ℝ) ≤ m := by exact_mod_cast hcard
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have q1 : (2 * (P1.card : ℝ)) ^ 2 ≤ 8 * U := by nlinarith
    have q2 : (2 * ((Pm m).card : ℝ)) ^ 2 ≤ 8 * U := by nlinarith
    have hV0 : 0 ≤ ∑ p ∈ P1, 1 / (p : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    have q3 : (∑ p ∈ P1, 1 / (p : ℝ)) ^ 2 ≤ 160000 := by nlinarith
    have hW0 : 0 ≤ ∑ p ∈ Pm m, 1 / (p : ℝ) ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have q4 : (∑ p ∈ Pm m, 1 / (p : ℝ) ^ 2) ^ 2 ≤ Z32 ^ 2 :=
      pow_le_pow_left₀ hW0 (sum_inv_sq_le m) 2
    have r1 := mul_le_mul_of_nonneg_left q1 (by positivity : (0 : ℝ) ≤ 2 * C)
    have r2 := mul_le_mul_of_nonneg_left q2 (by positivity : (0 : ℝ) ≤ 2 * C)
    have r3 := mul_le_mul_of_nonneg_left q3 (by positivity : (0 : ℝ) ≤ 2 * U)
    have r4 := mul_le_mul_of_nonneg_left q4 (by positivity : (0 : ℝ) ≤ 2 * U)
    have hK4 : 0 ≤ (K + 1) ^ 4 := by positivity
    nlinarith

lemma F_sub_N_pointwise (Z : ZetaInputs) {j : ℤ} {t : ℝ} (h1 : (2 : ℝ) ^ j ≤ t) (h2 : t ≤ 2 * (2 : ℝ) ^ j) :
    |F t - Z.N t| ^ 4 ≤ 8 * (|N0 t + PhiM (budget j) t - Z.N t| ^ 4
      + |N0 t + PhiM (budget (j + 1)) t - Z.N t| ^ 4) := by
  have hU := two_zpow_pos j
  have h2' : t ≤ (2 : ℝ) ^ (j + 1) := by rw [zpow_add_one₀ (by norm_num)]; linarith
  set a := N0 t + PhiM (budget j) t - Z.N t
  set b := N0 t + PhiM (budget (j + 1)) t - Z.N t
  set w1 := 2 - t / (2 : ℝ) ^ j
  set w2 := t / (2 : ℝ) ^ j - 1
  have hq1 : 1 ≤ t / (2 : ℝ) ^ j := by rw [le_div_iff₀ hU]; linarith
  have hq2 : t / (2 : ℝ) ^ j ≤ 2 := by rw [div_le_iff₀ hU]; linarith
  have hdec : F t - Z.N t = w1 * a + w2 * b := by
    unfold F; rw [Phi_eq_G h1 h2']; unfold G; ring
  rw [hdec]
  refine le_trans (abs_add_pow4_le _ _) ?_
  have e1 : |w1 * a| ≤ |a| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith)
  have e2 : |w2 * b| ≤ |b| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith)
  have := pow_le_pow_left₀ (abs_nonneg _) e1 4
  have := pow_le_pow_left₀ (abs_nonneg _) e2 4
  linarith

lemma F_sub_N_measurable (Z : ZetaInputs) {a b : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable (fun t => |F t - Z.N t| ^ 4) (volume.restrict (Icc a b)) := by
  have hF : AEStronglyMeasurable F (volume.restrict (Icc a b)) :=
    (continuousOn_F.mono (t := Icc a b) (fun t (ht : t ∈ Icc a b) => show t ∈ Set.Ioi (0 : ℝ) from lt_of_lt_of_le ha ht.1)).aestronglyMeasurable measurableSet_Icc
  have hN : AEStronglyMeasurable (fun t => (Z.N t : ℝ)) (volume.restrict (Icc a b)) :=
    Z.N_measurable.aestronglyMeasurable
  exact ((hF.sub hN).norm.pow 4).congr (Filter.Eventually.of_forall (fun t => by simp [Real.norm_eq_abs]))

/-- **Lemma 7.6** (fourth moment of the counting error), under `FujiiA`:
for `U = 2^j`, `j ≥ j₀`, `|𝓕 − N|⁴` is integrable on `[U, 2U]` and `∫_U^{2U} |𝓕 − N|⁴ ≤ B·U`. -/
theorem fourth_moment (Z : ZetaInputs) (hFA : Z.FujiiA) :
    ∃ B : ℝ, ∃ j₀ : ℤ, 0 ≤ B ∧ ∀ j : ℤ, j₀ ≤ j →
      IntegrableOn (fun t => |F t - Z.N t| ^ 4) (Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) ∧
      ∫ t in Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), |F t - Z.N t| ^ 4 ≤ B * (2 : ℝ) ^ j := by
  obtain ⟨B, U₁, hB, hA⟩ := A_moment Z hFA
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt U₁ (by norm_num : (1 : ℝ) < 2)
  refine ⟨16 * B, max 8 (n : ℤ), by positivity, fun j hj => ?_⟩
  have hj8 : (8 : ℤ) ≤ j := le_trans (le_max_left _ _) hj
  have hjn : (n : ℤ) ≤ j := le_trans (le_max_right _ _) hj
  have hJ : (8 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj8
  set J : ℝ := (j : ℝ)
  have hzr : (2 : ℝ) ^ j = (2 : ℝ) ^ J := (Real.rpow_intCast 2 j).symm
  have hzr1 : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ (J + 1) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  have hU₁ : U₁ ≤ (2 : ℝ) ^ J := by
    rw [← hzr]
    have : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ j := by
      rw [← zpow_natCast]; exact zpow_le_zpow_right₀ (by norm_num) hjn
    linarith
  have hlo1 : (2 : ℝ) ^ (J / 2) - 1 ≤ (budget j : ℝ) := by
    have := Nat.lt_floor_add_one ((2 : ℝ) ^ ((j : ℝ) / 2)); unfold budget; linarith
  have hlo2 : (2 : ℝ) ^ (J / 2) - 1 ≤ (budget (j + 1) : ℝ) := by
    have : (budget j : ℝ) ≤ budget (j + 1) := by exact_mod_cast budget_mono j
    linarith
  have hhi1 : (budget j : ℝ) ^ 2 ≤ (2 : ℝ) ^ (J + 1) := by
    have := budget_sq_le j
    have : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [← hzr] at this; linarith
  have hhi2 : (budget (j + 1) : ℝ) ^ 2 ≤ (2 : ℝ) ^ (J + 1) := by
    have := budget_sq_le (j + 1); rw [hzr1] at this; exact this
  obtain ⟨g1, ig1, pg1, Ig1⟩ := hA J hJ hU₁ (budget j) hlo1 hhi1
  obtain ⟨g2, ig2, pg2, Ig2⟩ := hA J hJ hU₁ (budget (j + 1)) hlo2 hhi2
  rw [← hzr] at ig1 pg1 Ig1 ig2 pg2 Ig2
  have hpos := two_zpow_pos j
  have hmaj : ∀ t ∈ Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), |F t - Z.N t| ^ 4 ≤ 8 * (g1 t + g2 t) := by
    intro t ht
    have := F_sub_N_pointwise Z ht.1 ht.2
    have := pg1 t ht
    have := pg2 t ht
    linarith
  have ig : IntegrableOn (fun t => 8 * (g1 t + g2 t)) (Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) :=
    (ig1.add ig2).const_mul 8
  have hint : IntegrableOn (fun t => |F t - Z.N t| ^ 4) (Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) := by
    refine Integrable.mono' ig (F_sub_N_measurable Z hpos) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmaj t ht
  refine ⟨hint, ?_⟩
  calc ∫ t in Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), |F t - Z.N t| ^ 4
      ≤ ∫ t in Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), 8 * (g1 t + g2 t) := by
        refine setIntegral_mono_on hint ig measurableSet_Icc hmaj
    _ = 8 * ((∫ t in Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), g1 t)
          + ∫ t in Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j), g2 t) := by
        rw [integral_const_mul, integral_add ig1 ig2]
    _ ≤ 16 * B * (2 : ℝ) ^ j := by linarith

end RvmClock
