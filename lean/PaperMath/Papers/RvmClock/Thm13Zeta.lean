import PaperMath.Papers.RvmClock.Thm13
import PaperMath.Papers.RvmClock.ZetaConst
import PaperMath.Papers.RvmClock.ZetaSigS

/-!
# Theorem 1.3 with the zeta constants discharged

`Thm13.theorem_1_3` takes three real parameters `zc, z2c, zs` (standing for `ζ(c)`, `ζ(2c)`, `ζ(σ♯)`) and the
numerical hypotheses `0 < zc`, `0 < z2c`, `log (zc/z2c) ≤ 12.62467`, `log zs ≤ 1.52499`. Here they are
instantiated with Mathlib's `riemannZeta` at `c = 1.000002`, `2c = 2.000004`, `σ♯ = c + (c-1/2)²/R`, and the
four hypotheses are proved (`ZetaConst.log_zeta_ratio_le`, `ZetaSigS.log_zeta_sigS_le`). What remains are the
literature inputs (`ExplicitInputs`, functional equation and Lemma 4.3, Theorem 3.5, the decomposition of
`π S(T)`, Platt) and the single numerical hypothesis `hC1`.
-/

namespace RvmClock.Thm13

open Complex RvmClock.Profile RvmClock.ZetaLines RvmClock.Explicit RvmClock.Backlund

/-- `ζ(c)` for `c = 1.000002`. -/
noncomputable def zetaC : ℝ := (riemannZeta (cc : ℂ)).re
/-- `ζ(2c)`. -/
noncomputable def zeta2C : ℝ := (riemannZeta ((2 * cc : ℝ) : ℂ)).re
/-- `ζ(σ♯)`. -/
noncomputable def zetaS : ℝ := (riemannZeta (sigS : ℂ)).re

lemma zetaC_eq : zetaC = (riemannZeta ((1.000002 : ℝ) : ℂ)).re := by unfold zetaC cc; rfl
lemma zeta2C_eq : zeta2C = (riemannZeta ((2.000004 : ℝ) : ℂ)).re := by
  unfold zeta2C cc; norm_num

lemma zetaC_pos : 0 < zetaC := by rw [zetaC_eq]; exact ZetaConst.zeta_c_pos
lemma zeta2C_pos : 0 < zeta2C := by
  rw [zeta2C_eq]; linarith [ZetaConst.zeta_2c_ge]
lemma log_ratio_le : Real.log (zetaC / zeta2C) ≤ 12.62467 := by
  rw [zetaC_eq, zeta2C_eq]; exact ZetaConst.log_zeta_ratio_le
lemma log_zetaS_le : Real.log zetaS ≤ 1.52499 := ZetaSigS.log_zeta_sigS_le

/-- **Theorem 1.3**, inequality (1.7), with `ζ(c)`, `ζ(2c)`, `ζ(σ♯)` instantiated by Mathlib's `riemannZeta`
and their numerical bounds proved. -/
theorem theorem_1_3_zeta (S : ℝ → ℝ)
    -- Lemma 4.4 inputs
    (I : ExplicitInputs) (chi : ℂ → ℂ)
    (hFE : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      riemannZeta (sp σ t) = chi (sp σ t) * riemannZeta (1 - sp σ t))
    (hchi : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      ‖chi (sp σ t)‖ ≤ 1.0070 * (t / (2 * Real.pi)) ^ (1/2 - σ))
    -- Backlund data at height T (Theorem 3.5 at c = 1.000002, R = 1.000005)
    (Z : ℝ → ℕ → ℝ) (A0 D1 D2 E : ℝ → ℝ)
    (hA : ∀ T, 100 ≤ T → ∀ Ψ : ℝ → ℝ, (∀ θ, Ψ (-θ) = Ψ θ) →
      (∀ n : ℕ, 1 ≤ n → ∀ θ, (1 / (n : ℝ)) * Real.log ‖fB T n (pt cc RR θ)‖ ≤ Ψ θ) →
      ∃ nm : ℕ → ℕ, StrictMono nm ∧ ∀ ε > 0, ∃ M, ∀ m ≥ M,
        Z T (nm m) ≤ Real.log (zetaC / (Real.sqrt ((cc - 1) ^ 2 + T ^ 2) * zeta2C))
          + (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Ψ θ) + ε)
    (hB : ∀ T, 100 ≤ T → ∀ n : ℕ, 1 ≤ n → |D2 T| ≤ Real.pi * Z T n / (2 * dd) + E T / 2
      + 3 * Real.pi / (2 * n) + Real.pi / 4)
    (hEc : ∀ T, 100 ≤ T → E T / Real.pi ≤ (640 * delS - 112) / (1536 * (3 * T - 1)) + 1 / 1024)
    (hdec : ∀ T, 100 ≤ T → Real.pi * S T = A0 T + D2 T - D1 T)
    (hA0 : ∀ T, 100 ≤ T → |A0 T| ≤ Real.log zetaS)
    (hD1 : ∀ T, 100 ≤ T →
      D1 T = Real.arctan ((cc + (cc - 1 / 2) ^ 2 / RR - 1) / T) + Real.arctan (1 / (2 * T)))
    -- the remaining numerical value (interval arithmetic)
    (hC1 : (∫ θ in (0 : ℝ)..Real.pi, eStar (cc + RR * Real.cos θ)) / (2 * Real.pi * dd) ≤ 0.0978293)
    -- Theorem 3.6 (Platt)
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 :=
  theorem_1_3 S I chi hFE hchi Z A0 D1 D2 E zetaC zeta2C zetaS zetaC_pos zeta2C_pos hA hB hEc hdec hA0
    hD1 hC1 log_ratio_le log_zetaS_le hplatt

end RvmClock.Thm13
