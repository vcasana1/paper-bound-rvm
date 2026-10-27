import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Proposition 5.1 of `rvm_clock_envelope` (Backlund's method on a disc)

`riemannZeta` is Mathlib's. Theorem 3.5(a),(b) (Bellotti–Wong Lemmas 2.1, 2.3, 2.4) and the decomposition
of `π S(T)` enter as literal hypotheses, with `Z n = 𝒵_n(c,R)` and `D₂ = Δ arg((s-1)ζ(s))` abstract reals.
Lean checks: the majorant `Ψ` of `(1/n) log |𝔣_n|` from the hypothesis (5.1) on `ζ`, its integral,
the limit along the subsequence of Theorem 3.5(a), and the final inequality (5.2).
-/

namespace RvmClock.Backlund

open Complex

/-- `𝔣_n(s)` of (3.4). -/
noncomputable def fB (T : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (((s + T * I - 1) * riemannZeta (s + T * I)) ^ n
    + ((s - T * I - 1) * riemannZeta (s - T * I)) ^ n)

/-- The point `c + R e^{iθ}`. -/
noncomputable def pt (c R θ : ℝ) : ℂ := c + R * Complex.exp (θ * I)

lemma pt_re (c R θ : ℝ) : (pt c R θ).re = c + R * Real.cos θ := by
  simp [pt, Complex.exp_ofReal_mul_I_re]

lemma pt_im (c R θ : ℝ) : (pt c R θ).im = R * Real.sin θ := by
  simp [pt, Complex.exp_ofReal_mul_I_im]

lemma norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `|z| ≤ T + 3` when `|Re z| ≤ 3`, `|Im z| ≤ T + 2`, `T ≥ 2`. -/
lemma norm_le_T3 {z : ℂ} {T : ℝ} (hT : 2 ≤ T) (hre : |z.re| ≤ 3) (him : |z.im| ≤ T + 2) :
    ‖z‖ ≤ T + 3 := by
  have h1 : z.re ^ 2 ≤ 9 := by nlinarith [abs_nonneg z.re, sq_abs z.re]
  have h2 : z.im ^ 2 ≤ (T + 2) ^ 2 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  have h3 : ‖z‖ ^ 2 ≤ (T + 3) ^ 2 := by rw [norm_sq_eq]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) (by linarith) two_ne_zero).1 h3

lemma zeta_conj_norm (w : ℂ) : ‖riemannZeta w‖ = ‖riemannZeta ((starRingEnd ℂ) w)‖ := by
  rw [riemannZeta_conj, Complex.norm_conj]

section master

variable (c R T K E A0 D1 D2 S zc z2c zs : ℝ) (h Ω : ℝ → ℝ) (Z : ℕ → ℝ)

/-- The majorant `Ψ(θ)` in the proof of Proposition 5.1. -/
noncomputable def Psi (θ : ℝ) : ℝ :=
  Real.log (T + 3) + h (c + R * Real.cos θ) * Real.log (T + 2) + Real.log (Ω (T + 2)) + Real.log K

/-- The bound for `|(s ± iT - 1) ζ(s ± iT)|` on the circle. -/
lemma factor_bound (hT : 3 ≤ T) (hK : 1 ≤ K) (hc1 : 1 < c) (hc2 : c ≤ 2) (hR0 : 0 < R) (hR2 : R ≤ 2)
    (hΩ : 1 ≤ Ω (T + 2))
    (hmono : ∀ σ ∈ Set.Icc (c - R) (c + R),
      MonotoneOn (fun t => t ^ h σ * Ω t) (Set.Icc (T - 2) (T + 2)))
    (hz : ∀ σ ∈ Set.Icc (c - R) (c + R), ∀ t ∈ Set.Icc (T - 2) (T + 2),
      ‖riemannZeta (σ + t * I)‖ ≤ K * (t ^ h σ * Ω t))
    (σ u : ℝ) (hσ : σ ∈ Set.Icc (c - R) (c + R)) (hu : |u| ≤ R) :
    ‖((σ + u * I : ℂ) + T * I - 1) * riemannZeta ((σ + u * I : ℂ) + T * I)‖
        ≤ (T + 3) * (K * ((T + 2) ^ h σ * Ω (T + 2))) ∧
    ‖((σ + u * I : ℂ) - T * I - 1) * riemannZeta ((σ + u * I : ℂ) - T * I)‖
        ≤ (T + 3) * (K * ((T + 2) ^ h σ * Ω (T + 2))) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  have hu' := abs_le.1 hu
  have hre : |σ - 1| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
  have hTmem : T + 2 ∈ Set.Icc (T - 2) (T + 2) := ⟨by linarith, le_refl _⟩
  -- zeta bound at height t ∈ [T-2, T+2], pushed to T+2 by monotonicity
  have hzt : ∀ t ∈ Set.Icc (T - 2) (T + 2),
      ‖riemannZeta (σ + t * I)‖ ≤ K * ((T + 2) ^ h σ * Ω (T + 2)) := by
    intro t ht
    have := hz σ ⟨hσ1, hσ2⟩ t ht
    have hm := hmono σ ⟨hσ1, hσ2⟩ ht hTmem ht.2
    calc ‖riemannZeta (σ + t * I)‖ ≤ K * (t ^ h σ * Ω t) := this
      _ ≤ K * ((T + 2) ^ h σ * Ω (T + 2)) := by
        apply mul_le_mul_of_nonneg_left hm (by linarith)
  have hK0 : 0 ≤ K * ((T + 2) ^ h σ * Ω (T + 2)) := by
    have := hΩ; positivity
  constructor
  · have e1 : ((σ + u * I : ℂ) + T * I) = (σ : ℂ) + ((u + T : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [norm_mul, e1]
    have ht : u + T ∈ Set.Icc (T - 2) (T + 2) := ⟨by linarith, by linarith⟩
    have hn : ‖(σ : ℂ) + ((u + T : ℝ) : ℂ) * I - 1‖ ≤ T + 3 := by
      apply norm_le_T3 (by linarith)
      · simpa using hre
      · simp; exact abs_le.2 ⟨by linarith, by linarith⟩
    exact mul_le_mul hn (hzt _ ht) (norm_nonneg _) (by linarith)
  · have e2 : (starRingEnd ℂ) ((σ + u * I : ℂ) - T * I) = (σ : ℂ) + ((T - u : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    rw [norm_mul, zeta_conj_norm, e2]
    have ht : T - u ∈ Set.Icc (T - 2) (T + 2) := ⟨by linarith, by linarith⟩
    have hn : ‖(σ + u * I : ℂ) - T * I - 1‖ ≤ T + 3 := by
      apply norm_le_T3 (by linarith)
      · simpa using hre
      · simp; exact abs_le.2 ⟨by linarith, by linarith⟩
    exact mul_le_mul hn (hzt _ ht) (norm_nonneg _) (by linarith)

/-- `(1/n) log |𝔣_n(c + R e^{iθ})| ≤ Ψ(θ)`. -/
lemma psi_majorant (hT : 3 ≤ T) (hK : 1 ≤ K) (hc1 : 1 < c) (hc2 : c ≤ 2) (hR0 : 0 < R)
    (hR2 : R ≤ 2) (hΩ : 1 ≤ Ω (T + 2)) (hh : ∀ σ ∈ Set.Icc (c - R) (c + R), 0 ≤ h σ)
    (hmono : ∀ σ ∈ Set.Icc (c - R) (c + R),
      MonotoneOn (fun t => t ^ h σ * Ω t) (Set.Icc (T - 2) (T + 2)))
    (hz : ∀ σ ∈ Set.Icc (c - R) (c + R), ∀ t ∈ Set.Icc (T - 2) (T + 2),
      ‖riemannZeta (σ + t * I)‖ ≤ K * (t ^ h σ * Ω t))
    (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) :
    (1 / (n : ℝ)) * Real.log ‖fB T n (pt c R θ)‖ ≤ Psi c R T K h Ω θ := by
  set σ := c + R * Real.cos θ with hσdef
  have hσ : σ ∈ Set.Icc (c - R) (c + R) := by
    constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have hu : |R * Real.sin θ| ≤ R := by
    rw [abs_mul, abs_of_pos hR0]
    exact mul_le_of_le_one_right hR0.le (Real.abs_sin_le_one θ)
  have hp : pt c R θ = (σ : ℂ) + ((R * Real.sin θ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [pt_re, pt_im, hσdef, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  obtain ⟨ha, hb⟩ := factor_bound c R T K h Ω hT hK hc1 hc2 hR0 hR2 hΩ hmono hz σ _ hσ hu
  set M := (T + 3) * (K * ((T + 2) ^ h σ * Ω (T + 2))) with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ (T + 2) ^ h σ := Real.one_le_rpow (by linarith) (hh σ hσ)
    have h2 := hΩ
    have h3 : 1 ≤ (T + 2) ^ h σ * Ω (T + 2) := one_le_mul_of_one_le_of_one_le h1 h2
    have h4 : 1 ≤ K * ((T + 2) ^ h σ * Ω (T + 2)) := one_le_mul_of_one_le_of_one_le hK h3
    exact one_le_mul_of_one_le_of_one_le (by linarith) h4
  have hfB : ‖fB T n (pt c R θ)‖ ≤ M ^ n := by
    rw [hp]; unfold fB
    set a := ((σ + (R * Real.sin θ : ℝ) * I : ℂ) + T * I - 1)
        * riemannZeta ((σ + (R * Real.sin θ : ℝ) * I : ℂ) + T * I) with ha_def
    set b := ((σ + (R * Real.sin θ : ℝ) * I : ℂ) - T * I - 1)
        * riemannZeta ((σ + (R * Real.sin θ : ℝ) * I : ℂ) - T * I) with hb_def
    rw [norm_mul]
    have hab := norm_add_le (a ^ n) (b ^ n)
    rw [norm_pow, norm_pow] at hab
    have hpa := pow_le_pow_left₀ (norm_nonneg _) ha n
    have hpb := pow_le_pow_left₀ (norm_nonneg _) hb n
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    nlinarith
  have hMpos : 0 < M := by linarith
  have hlog : Real.log ‖fB T n (pt c R θ)‖ ≤ n * Real.log M := by
    rcases (norm_nonneg (fB T n (pt c R θ))).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]
      exact mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg hM1)
    · calc Real.log ‖fB T n (pt c R θ)‖ ≤ Real.log (M ^ n) := Real.log_le_log h0 hfB
        _ = n * Real.log M := by rw [Real.log_pow]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogM : Real.log M = Psi c R T K h Ω θ := by
    have hK0 : 0 < K := by linarith
    have hT2 : 0 < T + 2 := by linarith
    have hO : 0 < Ω (T + 2) := by linarith [hΩ]
    rw [hM, Real.log_mul (by linarith) (by positivity), Real.log_mul hK0.ne' (by positivity),
      Real.log_mul (by positivity) hO.ne', Real.log_rpow hT2]
    unfold Psi; rw [← hσdef]; ring
  rw [← hlogM]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn0]
  linarith

/-- `∫₀^π Ψ = π (log(T+3) + log Ω(T+2) + log K) + 𝓘_h log(T+2)`. -/
lemma integral_psi (hcont : ContinuousOn h (Set.Icc (c - R) (c + R))) (hR0 : 0 < R) :
    ∫ θ in (0 : ℝ)..Real.pi, Psi c R T K h Ω θ
      = Real.pi * (Real.log (T + 3) + Real.log (Ω (T + 2)) + Real.log K)
        + (∫ θ in (0 : ℝ)..Real.pi, h (c + R * Real.cos θ)) * Real.log (T + 2) := by
  have hmaps : Set.MapsTo (fun θ => c + R * Real.cos θ) (Set.uIcc 0 Real.pi)
      (Set.Icc (c - R) (c + R)) := by
    intro θ _
    constructor <;> nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have hci : ContinuousOn (fun θ => h (c + R * Real.cos θ)) (Set.uIcc 0 Real.pi) :=
    hcont.comp (by fun_prop) hmaps
  have hI : IntervalIntegrable (fun θ => h (c + R * Real.cos θ)) MeasureTheory.volume 0 Real.pi :=
    hci.intervalIntegrable
  have hI2 : IntervalIntegrable (fun θ => h (c + R * Real.cos θ) * Real.log (T + 2))
      MeasureTheory.volume 0 Real.pi := hI.mul_const _
  unfold Psi
  have e : (fun θ => Real.log (T + 3) + h (c + R * Real.cos θ) * Real.log (T + 2)
      + Real.log (Ω (T + 2)) + Real.log K)
      = fun θ => (Real.log (T + 3) + Real.log (Ω (T + 2)) + Real.log K)
          + h (c + R * Real.cos θ) * Real.log (T + 2) := by
    funext θ; ring
  rw [e, intervalIntegral.integral_add intervalIntegrable_const hI2, intervalIntegral.integral_const,
    intervalIntegral.integral_mul_const]
  simp

/-- **Proposition 5.1**, inequality (5.2). -/
theorem master (hT : 3 ≤ T) (hK : 1 ≤ K) (hc1 : 1 < c) (hc2 : c ≤ 2) (hcR : c < R) (hR2 : R ≤ 2)
    (hzc : 0 < zc) (hz2c : 0 < z2c)
    (hΩ : 1 ≤ Ω (T + 2)) (hh : ∀ σ ∈ Set.Icc (c - R) (c + R), 0 ≤ h σ)
    (hcont : ContinuousOn h (Set.Icc (c - R) (c + R)))
    (hmono : ∀ σ ∈ Set.Icc (c - R) (c + R),
      MonotoneOn (fun t => t ^ h σ * Ω t) (Set.Icc (T - 2) (T + 2)))
    (hz : ∀ σ ∈ Set.Icc (c - R) (c + R), ∀ t ∈ Set.Icc (T - 2) (T + 2),
      ‖riemannZeta (σ + t * I)‖ ≤ K * (t ^ h σ * Ω t))
    -- Theorem 3.5(a)
    (hA : ∀ Ψ : ℝ → ℝ, (∀ θ, Ψ (-θ) = Ψ θ) →
      (∀ n : ℕ, 1 ≤ n → ∀ θ, (1 / (n : ℝ)) * Real.log ‖fB T n (pt c R θ)‖ ≤ Ψ θ) →
      ∃ nm : ℕ → ℕ, StrictMono nm ∧ ∀ ε > 0, ∃ M, ∀ m ≥ M,
        Z (nm m) ≤ Real.log (zc / (Real.sqrt ((c - 1) ^ 2 + T ^ 2) * z2c))
          + (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Ψ θ) + ε)
    -- Theorem 3.5(b), with `𝔡 = log (R / (c - 1/2))` and `E = 𝓔(T, δ♯)`
    (hB : ∀ n : ℕ, 1 ≤ n → |D2| ≤ Real.pi * Z n / (2 * Real.log (R / (c - 1 / 2))) + E / 2
      + 3 * Real.pi / (2 * n) + Real.pi / 4)
    -- the decomposition of `π S(T)`, with `σ♯ = c + (c - 1/2)^2 / R`
    (hdec : Real.pi * S = A0 + D2 - D1) (hA0 : |A0| ≤ Real.log zs)
    (hD1 : D1 = Real.arctan ((c + (c - 1 / 2) ^ 2 / R - 1) / T) + Real.arctan (1 / (2 * T))) :
    |S| ≤ 1 / (2 * Real.log (R / (c - 1 / 2))) * (Real.log (zc / z2c) + Real.log ((T + 3) / T)
        + (∫ θ in (0 : ℝ)..Real.pi, h (c + R * Real.cos θ)) / Real.pi * Real.log (T + 2)
        + Real.log (Ω (T + 2)) + Real.log K)
      + Real.log zs / Real.pi + (c + (c - 1 / 2) ^ 2 / R - 1 / 2) / (Real.pi * T)
      + E / (2 * Real.pi) + 1 / 4 := by
  have hR0 : 0 < R := by linarith
  have hpi := Real.pi_pos
  have hT0 : 0 < T := by linarith
  set dd := Real.log (R / (c - 1 / 2)) with hdd
  have hdd0 : 0 < dd := Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  set Ih := ∫ θ in (0 : ℝ)..Real.pi, h (c + R * Real.cos θ) with hIh
  set Zst := Real.log (zc / z2c) + Real.log ((T + 3) / T) + Ih / Real.pi * Real.log (T + 2)
    + Real.log (Ω (T + 2)) + Real.log K with hZst
  -- the majorant
  have heven : ∀ θ, Psi c R T K h Ω (-θ) = Psi c R T K h Ω θ := by
    intro θ; unfold Psi; rw [Real.cos_neg]
  obtain ⟨nm, hnm, hlim⟩ := hA (Psi c R T K h Ω) heven
    (fun n hn θ => psi_majorant c R T K h Ω hT hK hc1 hc2 hR0 hR2 hΩ hh hmono hz n hn θ)
  -- the bound of Theorem 3.5(a) is at most Zst
  have hZ0 : Real.log (zc / (Real.sqrt ((c - 1) ^ 2 + T ^ 2) * z2c))
      + (1 / Real.pi) * (∫ θ in (0 : ℝ)..Real.pi, Psi c R T K h Ω θ) ≤ Zst := by
    rw [integral_psi c R T K h Ω hcont hR0]
    have hs : T ≤ Real.sqrt ((c - 1) ^ 2 + T ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (c - 1)])
    have hs0 : 0 < Real.sqrt ((c - 1) ^ 2 + T ^ 2) := lt_of_lt_of_le hT0 hs
    have e1 : Real.log (zc / (Real.sqrt ((c - 1) ^ 2 + T ^ 2) * z2c))
        = Real.log (zc / z2c) - Real.log (Real.sqrt ((c - 1) ^ 2 + T ^ 2)) := by
      rw [show zc / (Real.sqrt ((c - 1) ^ 2 + T ^ 2) * z2c)
          = (zc / z2c) / Real.sqrt ((c - 1) ^ 2 + T ^ 2) by field_simp]
      exact Real.log_div (by positivity) hs0.ne'
    have e2 : Real.log ((T + 3) / T) = Real.log (T + 3) - Real.log T :=
      Real.log_div (by linarith) hT0.ne'
    have hl : Real.log T ≤ Real.log (Real.sqrt ((c - 1) ^ 2 + T ^ 2)) := Real.log_le_log hT0 hs
    rw [e1, hZst, e2]
    have : (1 / Real.pi) * (Real.pi * (Real.log (T + 3) + Real.log (Ω (T + 2)) + Real.log K)
        + Ih * Real.log (T + 2)) = Real.log (T + 3) + Real.log (Ω (T + 2)) + Real.log K
        + Ih / Real.pi * Real.log (T + 2) := by
      field_simp
    rw [this]; linarith
  -- limit along the subsequence: |D2| ≤ π Zst / (2𝔡) + E/2 + π/4
  have hD2 : |D2| ≤ Real.pi * Zst / (2 * dd) + E / 2 + Real.pi / 4 := by
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨M, hM⟩ := hlim (η * dd / Real.pi) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (3 * Real.pi / η)
    set m := max M (N + 1) with hm
    have hm1 : M ≤ m := le_max_left _ _
    have hm2 : N + 1 ≤ m := le_max_right _ _
    have hnmm : m ≤ nm m := hnm.id_le m
    have hn1 : 1 ≤ nm m := by omega
    have hZm := hM m hm1
    have hBm := hB (nm m) hn1
    have hnr : (N : ℝ) + 1 ≤ (nm m : ℝ) := by exact_mod_cast (by omega : N + 1 ≤ nm m)
    have h3 : 3 * Real.pi / (2 * (nm m : ℝ)) ≤ η / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 3 * Real.pi < η * N := by have := (div_lt_iff₀ hη).1 hN; linarith
      nlinarith
    have h4 : Real.pi * Z (nm m) / (2 * dd) ≤ Real.pi * Zst / (2 * dd) + η / 2 := by
      have : Z (nm m) ≤ Zst + η * dd / Real.pi := by linarith
      calc Real.pi * Z (nm m) / (2 * dd) ≤ Real.pi * (Zst + η * dd / Real.pi) / (2 * dd) := by
            gcongr
        _ = Real.pi * Zst / (2 * dd) + η / 2 := by field_simp <;> ring
    linarith
  -- the change of arg (s - 1)
  have hσs : 1 ≤ c + (c - 1 / 2) ^ 2 / R := by
    have : 0 ≤ (c - 1 / 2) ^ 2 / R := by positivity
    linarith
  have hD1b : |D1| ≤ (c + (c - 1 / 2) ^ 2 / R - 1 / 2) / T := by
    have a1 : 0 ≤ (c + (c - 1 / 2) ^ 2 / R - 1) / T := div_nonneg (by linarith) hT0.le
    have a2 : 0 ≤ 1 / (2 * T) := by positivity
    have b1 := Real.arctan_le_self a1
    have b2 := Real.arctan_le_self a2
    have c1 := Real.arctan_nonneg.2 a1
    have c2 := Real.arctan_nonneg.2 a2
    rw [hD1, abs_of_nonneg (by linarith)]
    have : (c + (c - 1 / 2) ^ 2 / R - 1) / T + 1 / (2 * T)
        = (c + (c - 1 / 2) ^ 2 / R - 1 / 2) / T := by field_simp <;> ring
    linarith
  -- assemble
  have hS : Real.pi * |S| ≤ Real.log zs + (Real.pi * Zst / (2 * dd) + E / 2 + Real.pi / 4)
      + (c + (c - 1 / 2) ^ 2 / R - 1 / 2) / T := by
    rw [← abs_of_pos hpi, ← abs_mul, abs_of_pos hpi, hdec]
    have e : A0 + D2 - D1 = (A0 + D2) + (-D1) := by ring
    have t1 := abs_add_le (A0 + D2) (-D1)
    rw [abs_neg] at t1
    have t2 := abs_add_le A0 D2
    rw [e]; linarith
  have goal_eq : 1 / (2 * dd) * Zst + Real.log zs / Real.pi
      + (c + (c - 1 / 2) ^ 2 / R - 1 / 2) / (Real.pi * T) + E / (2 * Real.pi) + 1 / 4
      = (Real.log zs + (Real.pi * Zst / (2 * dd) + E / 2 + Real.pi / 4)
          + (c + (c - 1 / 2) ^ 2 / R - 1 / 2) / T) / Real.pi := by
    field_simp <;> ring
  rw [goal_eq, le_div_iff₀ hpi, mul_comm]
  exact hS

end master

end RvmClock.Backlund
