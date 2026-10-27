import PaperMath.Papers.RvmClock.ZetaBound
import PaperMath.Papers.RvmClock.Backlund
import PaperMath.Papers.RvmClock.Explicit

/-!
# Theorem 1.3 from the literature: Proposition 5.1 + Lemma 4.4 + the final deduction

Everything is about Mathlib's `riemannZeta`. The hypotheses are the results of the literature, stated
literally (`ExplicitInputs`, the functional equation with Lemma 4.3, Theorem 3.5(a)–(c), the decomposition of
`π S(T)`, Platt's bound), and three numerical values (`C₁`, `log(ζ(c)/ζ(2c))`, `log ζ(σ♯)`), checked
with interval arithmetic.
-/

namespace RvmClock.Thm13

open Complex RvmClock.Profile RvmClock.ZetaLines RvmClock.Explicit RvmClock.Backlund

lemma sigS_le : cc + (cc - 1 / 2) ^ 2 / RR - 1 / 2 ≤ 0.7501 := by unfold cc RR; norm_num

lemma mono_profile (σ T : ℝ) (hT : 100 ≤ T) (hσ : σ ≤ 3) :
    MonotoneOn (fun t => t ^ eStar σ * Real.log t) (Set.Icc (T - 2) (T + 2)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have he := eStar_nonneg hσ
  have a := Real.rpow_le_rpow hx0.le hxy he
  have b := Real.log_le_log hx0 hxy
  have c : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hx.1])
  have d : 0 ≤ y ^ eStar σ := Real.rpow_nonneg (by linarith [hy.1]) _
  exact mul_le_mul a b c d

/-- **Theorem 1.3**, inequality (1.7), from the literature. -/
theorem theorem_1_3 (S : ℝ → ℝ)
    -- Lemma 4.4 inputs
    (I : ExplicitInputs) (chi : ℂ → ℂ)
    (hFE : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      riemannZeta (sp σ t) = chi (sp σ t) * riemannZeta (1 - sp σ t))
    (hchi : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      ‖chi (sp σ t)‖ ≤ 1.0070 * (t / (2 * Real.pi)) ^ (1/2 - σ))
    -- Backlund data at height T (Theorem 3.5 at c = 1.000002, R = 1.000005)
    (Z : ℝ → ℕ → ℝ) (A0 D1 D2 E : ℝ → ℝ) (zc z2c zs : ℝ) (hzc : 0 < zc) (hz2c : 0 < z2c)
    (hA : ∀ T, 100 ≤ T → ∀ Ψ : ℝ → ℝ, (∀ θ, Ψ (-θ) = Ψ θ) →
      (∀ n : ℕ, 1 ≤ n → ∀ θ, (1 / (n : ℝ)) * Real.log ‖fB T n (pt cc RR θ)‖ ≤ Ψ θ) →
      ∃ nm : ℕ → ℕ, StrictMono nm ∧ ∀ ε > 0, ∃ M, ∀ m ≥ M,
        Z T (nm m) ≤ Real.log (zc / (Real.sqrt ((cc - 1) ^ 2 + T ^ 2) * z2c))
          + (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Ψ θ) + ε)
    (hB : ∀ T, 100 ≤ T → ∀ n : ℕ, 1 ≤ n → |D2 T| ≤ Real.pi * Z T n / (2 * dd) + E T / 2
      + 3 * Real.pi / (2 * n) + Real.pi / 4)
    (hEc : ∀ T, 100 ≤ T → E T / Real.pi ≤ (640 * delS - 112) / (1536 * (3 * T - 1)) + 1 / 1024)
    (hdec : ∀ T, 100 ≤ T → Real.pi * S T = A0 T + D2 T - D1 T) (hA0 : ∀ T, 100 ≤ T → |A0 T| ≤ Real.log zs)
    (hD1 : ∀ T, 100 ≤ T →
      D1 T = Real.arctan ((cc + (cc - 1 / 2) ^ 2 / RR - 1) / T) + Real.arctan (1 / (2 * T)))
    -- numerical values (interval arithmetic)
    (hC1 : (∫ θ in (0 : ℝ)..Real.pi, eStar (cc + RR * Real.cos θ)) / (2 * Real.pi * dd) ≤ 0.0978293)
    (hzeta : Real.log (zc / z2c) ≤ 12.62467) (hzs : Real.log zs ≤ 1.52499)
    -- Theorem 3.6 (Platt)
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 := by
  have hpi := Real.pi_pos
  have hdd := dd_pos
  set Ih := ∫ θ in (0 : ℝ)..Real.pi, eStar (cc + RR * Real.cos θ) with hIh
  have hIh0 : 0 ≤ Ih := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ _
    apply eStar_nonneg
    have := Real.cos_le_one θ; unfold cc RR; nlinarith
  set C1 := Ih / (2 * Real.pi * dd) with hC1def
  have hC10 : 0 ≤ C1 := by positivity
  apply explicit_S S C1 (Real.log zs) (fun T => E T / (2 * Real.pi)) hC1 hC10 hzs
    (E_bound (fun T => E T / (2 * Real.pi)) (fun T hT => by
      have := hEc T hT
      have e : E T / (2 * Real.pi) = (1 / 2) * (E T / Real.pi) := by field_simp
      rw [e]; nlinarith))
    _ hplatt
  intro T hT
  have hT3 : 3 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log (T + 2) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  -- Proposition 5.1 with K = 2.74, h = 𝔢_E^*, Ω = log
  have hM := master cc RR T 2.74 (E T) (A0 T) (D1 T) (D2 T) (S T) zc z2c zs eStar Real.log (Z T)
    hT3 (by norm_num) (by unfold cc; norm_num) (by unfold cc; norm_num) (by unfold cc RR; norm_num)
    (by unfold RR; norm_num) hzc hz2c hlog1
    (fun σ hσ => eStar_nonneg (by have := hσ.2; unfold cc RR at this; linarith))
    eStar_continuous.continuousOn
    (fun σ hσ => mono_profile σ T hT (by have := hσ.2; unfold cc RR at this; linarith))
    (fun σ hσ t ht => by
      have h4 := lemma_4_4 I chi hFE hchi σ
        ⟨by have := hσ.1; unfold cc RR at this; linarith, by have := hσ.2; unfold cc RR at this; linarith⟩
        t (by linarith [ht.1])
      have : sp σ t = (σ : ℂ) + (t : ℂ) * Complex.I := rfl
      rw [← this]; linarith)
    (hA T hT) (hB T hT) (hdec T hT) (hA0 T hT) (hD1 T hT)
  -- compare with the assembled form (5.5)
  have hC2 : C2 = 1 / (2 * dd) := rfl
  have hs := sigS_le
  have hσterm : (cc + (cc - 1 / 2) ^ 2 / RR - 1 / 2) / (Real.pi * T) ≤ 0.7501 / (Real.pi * T) := by
    apply div_le_div_of_nonneg_right hs (by positivity)
  have hC2n := C2_nonneg
  have hddeq : dd = Real.log (RR / (cc - 1 / 2)) := rfl
  rw [← hddeq, ← hIh] at hM
  have hmain : 1 / (2 * dd) * (Real.log (zc / z2c) + Real.log ((T + 3) / T)
        + Ih / Real.pi * Real.log (T + 2) + Real.log (Real.log (T + 2)) + Real.log 2.74)
      ≤ C1 * Real.log (T + 2) + C2 * Real.log (Real.log (T + 2))
        + C2 * (12.62467 + Real.log ((T + 3) / T) + Real.log 2.74) := by
    have expand : 1 / (2 * dd) * (Real.log (zc / z2c) + Real.log ((T + 3) / T)
        + Ih / Real.pi * Real.log (T + 2) + Real.log (Real.log (T + 2)) + Real.log 2.74)
        = C2 * Real.log (zc / z2c) + C2 * Real.log ((T + 3) / T)
          + C2 * (Ih / Real.pi * Real.log (T + 2)) + C2 * Real.log (Real.log (T + 2))
          + C2 * Real.log 2.74 := by rw [hC2]; ring
    have e : C2 * (Ih / Real.pi * Real.log (T + 2)) = C1 * Real.log (T + 2) := by
      rw [hC2, hC1def]; field_simp
    have h12 := mul_le_mul_of_nonneg_left hzeta hC2n
    have expand2 : C2 * (12.62467 + Real.log ((T + 3) / T) + Real.log 2.74)
        = C2 * 12.62467 + C2 * Real.log ((T + 3) / T) + C2 * Real.log 2.74 := by ring
    linarith
  linarith

end RvmClock.Thm13
