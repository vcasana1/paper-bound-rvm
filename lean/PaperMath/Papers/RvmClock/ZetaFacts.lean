import PaperMath.Common.ZetaTail
import PaperMath.Papers.RvmClock.C1

/-!
# Two more inputs of Theorem 1.3 proved from Mathlib: `|ζ(3+it)| ≤ 1.21` and the functional equation

* `zeta3`: `‖ζ(3+it)‖ ≤ ζ(3) ≤ 1.2024 ≤ 1.21` (`Common.ZetaSeries.norm_zeta_le_zeta_re`,
  `Common.ZetaTail.zeta_three_le`); this is the field `ExplicitInputs.zeta3`.
* `chi s = 2 (2π)^{s-1} Γ(1-s) sin(πs/2)` and `functional_equation`: `ζ(s) = chi s · ζ(1-s)` for `Im s ≠ 0`,
  from Mathlib's `riemannZeta_one_sub`; this is the hypothesis `hFE` of `Thm13.theorem_1_3`, with `chi` now a
  definition.

`theorem_1_3_lit` is Theorem 1.3 with these two discharged. What remains are the literature inputs
(HPY, Patel–Yang, Yang, Patel, Titchmarsh (2.1.4), Fiori's Phragmén–Lindelöf, Bellotti–Wong's Theorem 3.5,
Platt) and Lemma 4.3 of the article, which is now the explicit statement
`‖chi (σ + it)‖ ≤ 1.0070 (t/2π)^{1/2-σ}` for this `chi` (`-0.01 ≤ σ ≤ 1/2`, `t ≥ 98`): it needs Stirling's
formula with an explicit remainder for the complex Gamma function, which Mathlib does not have.
-/

open Complex RvmClock.ZetaLines RvmClock.Explicit

namespace RvmClock.ZetaFacts

/-- `ExplicitInputs.zeta3`: `‖ζ(3+it)‖ ≤ 1.21`. -/
theorem zeta3 (t : ℝ) : ‖riemannZeta (sp 3 t)‖ ≤ 1.21 := by
  have hre : (sp 3 t).re = 3 := sp_re 3 t
  have h := Common.ZetaSeries.norm_zeta_le_zeta_re (s := sp 3 t) (by rw [hre]; norm_num)
  rw [hre] at h
  have := Common.ZetaTail.zeta_three_le
  linarith

/-- `χ(s) = 2 (2π)^{s-1} Γ(1-s) sin(πs/2)`, so that `ζ(s) = χ(s) ζ(1-s)`. -/
noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s) * Complex.sin (Real.pi * s / 2)

/-- The functional equation `ζ(s) = χ(s) ζ(1-s)` for `Im s ≠ 0` (Mathlib's `riemannZeta_one_sub`). -/
theorem functional_equation (s : ℂ) (hs : s.im ≠ 0) :
    riemannZeta s = chi s * riemannZeta (1 - s) := by
  have h1 : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.im h
    simp at this
    exact hs this
  have h2 : 1 - s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hs this
  have h := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at h
  rw [h]
  unfold chi
  rw [show (Real.pi : ℂ) * (1 - s) / 2 = Real.pi / 2 - Real.pi * s / 2 by ring,
    Complex.cos_pi_div_two_sub, neg_sub]

theorem hFE (σ t : ℝ) (ht : 98 ≤ t) :
    riemannZeta (sp σ t) = chi (sp σ t) * riemannZeta (1 - sp σ t) :=
  functional_equation _ (by rw [sp_im]; linarith)

/-- **Theorem 1.3** with the numerical inputs, `|ζ(3+it)| ≤ 1.21` and the functional equation proved. The
hypotheses are the literature inputs (`hpy`, `py`, `yang`, `patel`, `small`, `pl`, `hA`, `hB`, `hEc`, `hdec`,
`hA0`, `hD1`, `hplatt`) and Lemma 4.3 (`hchi`), now stated for the explicit `chi`. -/
theorem theorem_1_3_lit (S : ℝ → ℝ)
    -- Theorem 3.3 (Hiary–Patel–Yang; Patel–Yang; Yang with constant 2; Patel)
    (hpy : ∀ t : ℝ, 3 < |t| → |t| ≤ Real.exp 105 →
      ‖riemannZeta (sp (1/2) t)‖ ≤ 0.618 * |t| ^ ((1 : ℝ) / 6) * Real.log |t|)
    (py : ∀ t : ℝ, Real.exp 105 < |t| → ‖riemannZeta (sp (1/2) t)‖ ≤ 66.7 * |t| ^ ((27 : ℝ) / 164))
    (yang : ∀ m : ℕ, 4 ≤ m → m ≤ 9 → ∀ t : ℝ, 3 ≤ |t| →
      ‖riemannZeta (sp (1 - (m : ℝ) / (2 ^ m - 2)) t)‖ ≤ 2 * |t| ^ ((1 : ℝ) / (2 ^ m - 2)) * Real.log |t|)
    (patel : ∀ t : ℝ, 3 ≤ |t| → ‖riemannZeta (sp 1 t)‖ ≤ Real.log |t|)
    -- Titchmarsh (2.1.4), consequence
    (small : ∀ σ ∈ Set.Icc (1/2 : ℝ) 3, ∀ t : ℝ,
      ‖Xi (sp σ t)‖ ≤ ‖sp σ t‖ + 2 * ‖sp σ t‖ * ‖sp σ t - 1‖)
    -- Theorem 3.4 (Fiori) for Ξ
    (pl : ∀ a b α β : ℝ, a < b → 1 - a < 10 → β ≤ α → 0 ≤ β →
      (∀ t : ℝ, ‖Xi (sp a t)‖ ≤ 2 * ‖(10 : ℂ) + sp a t‖ ^ α * ‖Complex.log (10 + sp a t)‖) →
      (∀ t : ℝ, ‖Xi (sp b t)‖ ≤ 2 * ‖(10 : ℂ) + sp b t‖ ^ β * ‖Complex.log (10 + sp b t)‖) →
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, ‖Xi (sp σ t)‖ ≤
        (2 * ‖(10 : ℂ) + sp σ t‖ ^ α) ^ ((b - σ) / (b - a))
          * (2 * ‖(10 : ℂ) + sp σ t‖ ^ β) ^ ((σ - a) / (b - a)) * ‖Complex.log (10 + sp σ t)‖)
    -- Lemma 4.3 of the article, for the explicit `chi`
    (hchi : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      ‖chi (sp σ t)‖ ≤ 1.0070 * (t / (2 * Real.pi)) ^ (1/2 - σ))
    -- Backlund data at height T (Theorem 3.5 at c = 1.000002, R = 1.000005)
    (Z : ℝ → ℕ → ℝ) (A0 D1 D2 E : ℝ → ℝ)
    (hA : ∀ T, 100 ≤ T → ∀ Ψ : ℝ → ℝ, (∀ θ, Ψ (-θ) = Ψ θ) →
      (∀ n : ℕ, 1 ≤ n → ∀ θ, (1 / (n : ℝ)) * Real.log ‖Backlund.fB T n (Backlund.pt cc RR θ)‖ ≤ Ψ θ) →
      ∃ nm : ℕ → ℕ, StrictMono nm ∧ ∀ ε > 0, ∃ M, ∀ m ≥ M,
        Z T (nm m) ≤ Real.log (Thm13.zetaC / (Real.sqrt ((cc - 1) ^ 2 + T ^ 2) * Thm13.zeta2C))
          + (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Ψ θ) + ε)
    (hB : ∀ T, 100 ≤ T → ∀ n : ℕ, 1 ≤ n → |D2 T| ≤ Real.pi * Z T n / (2 * dd) + E T / 2
      + 3 * Real.pi / (2 * n) + Real.pi / 4)
    (hEc : ∀ T, 100 ≤ T → E T / Real.pi ≤ (640 * delS - 112) / (1536 * (3 * T - 1)) + 1 / 1024)
    (hdec : ∀ T, 100 ≤ T → Real.pi * S T = A0 T + D2 T - D1 T)
    (hA0 : ∀ T, 100 ≤ T → |A0 T| ≤ Real.log Thm13.zetaS)
    (hD1 : ∀ T, 100 ≤ T →
      D1 T = Real.arctan ((cc + (cc - 1 / 2) ^ 2 / RR - 1) / T) + Real.arctan (1 / (2 * T)))
    -- Theorem 3.6 (Platt)
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 :=
  C1.theorem_1_3_numeric S ⟨hpy, py, yang, patel, zeta3, small, pl⟩ chi
    (fun σ _ t ht => hFE σ t ht) hchi Z A0 D1 D2 E hA hB hEc hdec hA0 hD1 hplatt

end RvmClock.ZetaFacts
