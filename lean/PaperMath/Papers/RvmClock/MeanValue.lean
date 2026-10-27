import PaperMath.Common.Zeta23Port.MV.Final
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mean value theorem for Dirichlet polynomials (Theorem 3.9 of the article, Montgomery–Vaughan)

Derived from the generalized Hilbert inequality `Zeta23.MV.mv_hilbert`, which was ported from
anthropics/formal-math (zeta23, Apache-2.0).  With `e(θ) = exp(-iθ)`:

  `| ∫_U^{2U} |Σ_{n∈s} b_n e(t log n)|² dt − U Σ |b_n|² | ≤ C Σ (n+1) |b_n|²`.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RvmClock

noncomputable def ex (θ : ℝ) : ℂ := Complex.exp (-(Complex.I * θ))

lemma norm_ex (θ : ℝ) : ‖ex θ‖ = 1 := by
  unfold ex
  rw [show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ex_mul_conj (a b : ℝ) : ex a * conj (ex b) = ex (a - b) := by
  unfold ex
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

lemma ex_zero : ex 0 = 1 := by simp [ex]

/-- `∫_U^{2U} e(tα) dt = i (e(2Uα) − e(Uα)) / α` for `α ≠ 0`. -/
lemma integral_ex {α : ℝ} (hα : α ≠ 0) (U : ℝ) :
    ∫ t in U..2 * U, ex (t * α) = Complex.I * (ex (2 * U * α) - ex (U * α)) / α := by
  have hc : (-(Complex.I * α) : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, hα]
  have h1 : (fun t : ℝ => ex (t * α)) = fun t : ℝ => Complex.exp (-(Complex.I * α) * t) := by
    funext t; unfold ex; congr 1; push_cast; ring
  rw [h1, integral_exp_mul_complex hc]
  unfold ex
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  field_simp
  rw [Complex.I_sq]
  have e1 : -(Complex.I * (α : ℂ) * ((2 * U : ℝ) : ℂ)) = -(Complex.I * ((2 * U * α : ℝ) : ℂ)) := by push_cast; ring
  have e2 : -(Complex.I * (α : ℂ) * ((U : ℝ) : ℂ)) = -(Complex.I * ((U * α : ℝ) : ℂ)) := by push_cast; ring
  rw [e1, e2]
  ring

/-- Admissible weights for the frequencies `log n`: `1/(r+1) ≤ |log r − log s|` for `r ≠ s`. -/
lemma log_gap {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≠ s) :
    1 / ((r : ℝ) + 1) ≤ |Real.log r - Real.log s| := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  rcases lt_or_gt_of_ne hrs with h | h
  · have hrs' : (r : ℝ) + 1 ≤ s := by exact_mod_cast h
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (r : ℝ) / (s : ℝ) by positivity)
    rw [Real.log_div hr0.ne' hs0.ne'] at h1
    have hq : (r : ℝ) / (s : ℝ) ≤ (r : ℝ) / ((r : ℝ) + 1) :=
      div_le_div_of_nonneg_left hr0.le (by positivity) hrs'
    have he : 1 - (r : ℝ) / ((r : ℝ) + 1) = 1 / ((r : ℝ) + 1) := by field_simp; ring
    have h2 : 1 / ((r : ℝ) + 1) ≤ Real.log s - Real.log r := by linarith
    rw [abs_sub_comm]; exact le_trans h2 (le_abs_self _)
  · have hsr' : (s : ℝ) + 1 ≤ r := by exact_mod_cast h
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (s : ℝ) / (r : ℝ) by positivity)
    rw [Real.log_div hs0.ne' hr0.ne'] at h1
    have hq : (s : ℝ) / (r : ℝ) ≤ 1 - 1 / ((r : ℝ) + 1) := by
      rw [div_le_iff₀ hr0]
      have : (1 - 1 / ((r : ℝ) + 1)) * r = r * r / ((r : ℝ) + 1) := by field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : 1 / ((r : ℝ) + 1) ≤ Real.log r - Real.log s := by linarith
    exact le_trans h2 (le_abs_self _)

/-- The Hilbert-type sum `H(V) = Σ_{m≠n} x_m conj(x_n)/(log m − log n)`, `x_m = b_m e(V log m)`. -/
noncomputable def Hsum (s : Finset ℕ) (b : ℕ → ℂ) (V : ℝ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s, if m = n then 0 else
    (b m * ex (V * Real.log m)) * conj (b n * ex (V * Real.log n)) / ((Real.log m - Real.log n : ℝ) : ℂ)

lemma Hsum_bound {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (b : ℕ → ℂ) (V : ℝ) : ‖Hsum s b V‖ ≤ C * ∑ n ∈ s, ((n : ℝ) + 1) * ‖b n‖ ^ 2 := by
  classical
  set x : s → ℂ := fun r => b r * ex (V * Real.log (r : ℕ)) with hx
  have hinj : Function.Injective (fun r : s => Real.log ((r : ℕ) : ℝ)) := by
    intro r t h
    have hr : (0 : ℝ) < ((r : ℕ) : ℝ) := by exact_mod_cast hs r r.2
    have ht : (0 : ℝ) < ((t : ℕ) : ℝ) := by exact_mod_cast hs t t.2
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr ht) h
    exact Subtype.ext (by exact_mod_cast this)
  have hδ : ∀ r : s, (0 : ℝ) < 1 / (((r : ℕ) : ℝ) + 1) := fun r => by positivity
  have hadm : ∀ r t : s, r ≠ t → 1 / (((r : ℕ) : ℝ) + 1) ≤ |Real.log ((r : ℕ) : ℝ) - Real.log ((t : ℕ) : ℝ)| :=
    fun r t hrt => log_gap (hs r r.2) (hs t t.2) (fun h => hrt (Subtype.ext h))
  have hM := hMV s (fun r => Real.log ((r : ℕ) : ℝ)) (fun r => 1 / (((r : ℕ) : ℝ) + 1)) x x hinj hδ hadm
  have hL : Hsum s b V = ∑ r : s, ∑ t : s, if r = t then (0 : ℂ) else
      x r * conj (x t) / ((Real.log ((r : ℕ) : ℝ) - Real.log ((t : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold Hsum
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases h : r = t
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]
  have hR : ∑ r : s, ‖x r‖ ^ 2 / (1 / (((r : ℕ) : ℝ) + 1)) = ∑ n ∈ s, ((n : ℝ) + 1) * ‖b n‖ ^ 2 := by
    rw [← Finset.sum_coe_sort s (fun n => ((n : ℝ) + 1) * ‖b n‖ ^ 2)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hx]; simp only
    rw [norm_mul, norm_ex, mul_one]
    field_simp
  rw [hL]
  have hA : 0 ≤ ∑ r : s, ‖x r‖ ^ 2 / (1 / (((r : ℕ) : ℝ) + 1)) :=
    Finset.sum_nonneg (fun r _ => div_nonneg (sq_nonneg _) (hδ r).le)
  calc _ ≤ C * Real.sqrt (∑ r : s, ‖x r‖ ^ 2 / (1 / (((r : ℕ) : ℝ) + 1)))
          * Real.sqrt (∑ r : s, ‖x r‖ ^ 2 / (1 / (((r : ℕ) : ℝ) + 1))) := hM
    _ = C * ∑ n ∈ s, ((n : ℝ) + 1) * ‖b n‖ ^ 2 := by
        rw [mul_assoc, Real.mul_self_sqrt hA, hR]

lemma continuous_ex_mul (α : ℝ) : Continuous fun t : ℝ => ex (t * α) := by
  unfold ex; fun_prop

lemma normSq_D (s : Finset ℕ) (b : ℕ → ℂ) (t : ℝ) :
    (((‖∑ n ∈ s, b n * ex (t * Real.log n)‖ ^ 2 : ℝ)) : ℂ)
      = ∑ m ∈ s, ∑ n ∈ s, b m * conj (b n) * ex (t * (Real.log m - Real.log n)) := by
  set D := ∑ n ∈ s, b n * ex (t * Real.log n) with hD
  have h1 : (((‖D‖ ^ 2 : ℝ)) : ℂ) = D * conj D := by rw [Complex.mul_conj']; push_cast; ring
  rw [h1, hD, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  rw [map_mul]
  have h2 : ex (t * Real.log m) * conj (ex (t * Real.log n)) = ex (t * (Real.log m - Real.log n)) := by
    rw [ex_mul_conj]; congr 1; ring
  calc b m * ex (t * Real.log m) * (conj (b n) * conj (ex (t * Real.log n)))
      = b m * conj (b n) * (ex (t * Real.log m) * conj (ex (t * Real.log n))) := by ring
    _ = b m * conj (b n) * ex (t * (Real.log m - Real.log n)) := by rw [h2]

/-- **Mean value theorem (Theorem 3.9)**, with an absolute constant. -/
theorem mean_value :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ), (∀ n ∈ s, 1 ≤ n) → ∀ (b : ℕ → ℂ) (U : ℝ),
      |(∫ t in U..2 * U, ‖∑ n ∈ s, b n * ex (t * Real.log n)‖ ^ 2) - U * ∑ n ∈ s, ‖b n‖ ^ 2|
        ≤ C * ∑ n ∈ s, ((n : ℝ) + 1) * ‖b n‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hMV⟩ := Zeta23.MV.mv_hilbert
  refine ⟨2 * C, by positivity, ?_⟩
  intro s hs b U
  have hint : ∀ m ∈ s, ∀ n ∈ s, ∫ t in U..2 * U, ex (t * (Real.log m - Real.log n))
      = if m = n then (U : ℂ) else
        Complex.I * (ex (2 * U * (Real.log m - Real.log n)) - ex (U * (Real.log m - Real.log n)))
          / ((Real.log m - Real.log n : ℝ) : ℂ) := by
    intro m hm n hn
    by_cases h : m = n
    · subst h; rw [if_pos rfl]; simp [ex_zero]; ring
    · rw [if_neg h]
      have hα : Real.log m - Real.log n ≠ 0 := by
        intro h0
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hs m hm
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hs n hn
        exact h (by exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr hm0) (Set.mem_Ioi.mpr hn0) (by linarith))
      exact integral_ex hα U
  have key : (((∫ t in U..2 * U, ‖∑ n ∈ s, b n * ex (t * Real.log n)‖ ^ 2 : ℝ)) : ℂ)
      = (U : ℂ) * ∑ n ∈ s, ((‖b n‖ ^ 2 : ℝ) : ℂ) + Complex.I * (Hsum s b (2 * U) - Hsum s b U) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_D]
    rw [intervalIntegral.integral_finsetSum
      (f := fun m t => ∑ n ∈ s, b m * conj (b n) * ex (t * (Real.log m - Real.log n))) (fun m _ => by
      have : Continuous fun t : ℝ => ∑ n ∈ s, b m * conj (b n) * ex (t * (Real.log m - Real.log n)) := by
        refine continuous_finsetSum _ (fun n _ => continuous_const.mul (continuous_ex_mul _))
      exact this.intervalIntegrable _ _)]
    have hin : ∀ m ∈ s, ∫ t in U..2 * U, ∑ n ∈ s, b m * conj (b n) * ex (t * (Real.log m - Real.log n))
        = ∑ n ∈ s, b m * conj (b n) * ∫ t in U..2 * U, ex (t * (Real.log m - Real.log n)) := by
      intro m _
      rw [intervalIntegral.integral_finsetSum
        (f := fun n t => b m * conj (b n) * ex (t * (Real.log m - Real.log n))) (fun n _ =>
        (continuous_const.mul (continuous_ex_mul _)).intervalIntegrable _ _)]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [intervalIntegral.integral_const_mul]
    rw [Finset.sum_congr rfl hin]
    have hev : ∀ m ∈ s, ∑ n ∈ s, b m * conj (b n) * ∫ t in U..2 * U, ex (t * (Real.log m - Real.log n))
        = (U : ℂ) * ((‖b m‖ ^ 2 : ℝ) : ℂ) + Complex.I * (∑ n ∈ s, (if m = n then 0 else
            (b m * ex (2 * U * Real.log m)) * conj (b n * ex (2 * U * Real.log n)) /
              ((Real.log m - Real.log n : ℝ) : ℂ))
          - ∑ n ∈ s, (if m = n then 0 else
            (b m * ex (U * Real.log m)) * conj (b n * ex (U * Real.log n)) /
              ((Real.log m - Real.log n : ℝ) : ℂ))) := by
      intro m hm
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      have hsplit : ∀ n ∈ s, b m * conj (b n) * ∫ t in U..2 * U, ex (t * (Real.log m - Real.log n))
          = (if m = n then (U : ℂ) * ((‖b m‖ ^ 2 : ℝ) : ℂ) else 0) + Complex.I *
            ((if m = n then 0 else
              (b m * ex (2 * U * Real.log m)) * conj (b n * ex (2 * U * Real.log n)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))
            - (if m = n then 0 else
              (b m * ex (U * Real.log m)) * conj (b n * ex (U * Real.log n)) /
                ((Real.log m - Real.log n : ℝ) : ℂ))) := by
        intro n hn
        rw [hint m hm n hn]
        by_cases h : m = n
        · subst h; simp only [if_true, sub_self, mul_zero, add_zero]
          rw [Complex.mul_conj']; push_cast; ring
        · simp only [if_neg h, zero_add]
          have e1 : b m * ex (2 * U * Real.log m) * conj (b n * ex (2 * U * Real.log n))
              = b m * conj (b n) * ex (2 * U * (Real.log m - Real.log n)) := by
            rw [map_mul]
            have := ex_mul_conj (2 * U * Real.log m) (2 * U * Real.log n)
            rw [show 2 * U * Real.log m - 2 * U * Real.log n = 2 * U * (Real.log m - Real.log n) by ring] at this
            rw [← this]; ring
          have e2 : b m * ex (U * Real.log m) * conj (b n * ex (U * Real.log n))
              = b m * conj (b n) * ex (U * (Real.log m - Real.log n)) := by
            rw [map_mul]
            have := ex_mul_conj (U * Real.log m) (U * Real.log n)
            rw [show U * Real.log m - U * Real.log n = U * (Real.log m - Real.log n) by ring] at this
            rw [← this]; ring
          rw [e1, e2]; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq s m]
      rw [if_pos hm]
    rw [Finset.sum_congr rfl hev, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_sub_distrib]
    unfold Hsum
    rfl
  have hb1 := Hsum_bound hMV hC.le hs b (2 * U)
  have hb2 := Hsum_bound hMV hC.le hs b U
  set I0 := ∫ t in U..2 * U, ‖∑ n ∈ s, b n * ex (t * Real.log n)‖ ^ 2 with hI0
  have hdiff : (((I0 - U * ∑ n ∈ s, ‖b n‖ ^ 2 : ℝ)) : ℂ) = Complex.I * (Hsum s b (2 * U) - Hsum s b U) := by
    push_cast; rw [key]; push_cast; ring
  have habs : |I0 - U * ∑ n ∈ s, ‖b n‖ ^ 2| = ‖Complex.I * (Hsum s b (2 * U) - Hsum s b U)‖ := by
    rw [← hdiff, Complex.norm_real, Real.norm_eq_abs]
  rw [habs, norm_mul, Complex.norm_I, one_mul]
  calc ‖Hsum s b (2 * U) - Hsum s b U‖ ≤ ‖Hsum s b (2 * U)‖ + ‖Hsum s b U‖ := norm_sub_le _ _
    _ ≤ 2 * C * ∑ n ∈ s, ((n : ℝ) + 1) * ‖b n‖ ^ 2 := by linarith

end RvmClock
