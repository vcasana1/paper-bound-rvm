import PaperMath.Papers.RvmClock.MeanValue
import Mathlib.Algebra.Order.Chebyshev

/-!
# Fourth moments of prime Dirichlet polynomials (used for `𝒟₁`, `𝒟₂` in Lemma 7.6)

For a finite set `P` of primes, `k ≥ 1` and coefficients `a_p`,
`∫_U^{2U} |Σ_{p∈P} a_p p^{-ikt}|⁴ dt ≤ 2U (Σ|a_p|²)² + C (Σ (p^k+1)|a_p|²)²`,
by the mean value theorem applied to the square, whose coefficients have fibres of size ≤ 2.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RvmClock

lemma ex_add (x y : ℝ) : ex x * ex y = ex (x + y) := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma prime_pair_eq {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime) (hq' : q'.Prime)
    (h : p * q = p' * q') : (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  have hd : p ∣ p' * q' := ⟨q, h.symm⟩
  rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
  · have e := (Nat.prime_dvd_prime_iff_eq hp hp').mp h1
    subst e
    left; exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos h⟩
  · have e := (Nat.prime_dvd_prime_iff_eq hp hq').mp h1
    subst e
    right; refine ⟨rfl, ?_⟩
    have : p * q = p * p' := by rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hp.pos this

section
variable (P : Finset ℕ) (k : ℕ) (a : ℕ → ℂ)

/-- `g(p,q) = (pq)^k`. -/
def gk (x : ℕ × ℕ) : ℕ := (x.1 * x.2) ^ k

noncomputable def cco (n : ℕ) : ℂ := ∑ x ∈ (P ×ˢ P).filter (fun x => gk k x = n), a x.1 * a x.2

lemma fiber_card_le (hP : ∀ p ∈ P, p.Prime) (hk : 1 ≤ k) (n : ℕ) :
    ((P ×ˢ P).filter (fun x => gk k x = n)).card ≤ 2 := by
  classical
  set F := (P ×ˢ P).filter (fun x => gk k x = n)
  by_cases hne : F.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hsub : F ⊆ {x0, x0.swap} := by
      intro x hx
      obtain ⟨hxP, hxn⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx0P, hx0n⟩ := Finset.mem_filter.mp hx0
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hxP
      obtain ⟨h3, h4⟩ := Finset.mem_product.mp hx0P
      have hpow : (x.1 * x.2) ^ k = (x0.1 * x0.2) ^ k := by
        simp only [gk] at hxn hx0n; rw [hxn, hx0n]
      have heq : x.1 * x.2 = x0.1 * x0.2 := Nat.pow_left_injective (by omega) hpow
      rcases prime_pair_eq (hP _ h1) (hP _ h2) (hP _ h3) (hP _ h4) heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp [Prod.ext_iff, e1, e2]
      · simp [Prod.ext_iff, Prod.swap, e1, e2]
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

lemma D_sq (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (∑ p ∈ P, a p * ex (t * Real.log ((p : ℝ) ^ k))) ^ 2
      = ∑ n ∈ (P ×ˢ P).image (gk k), cco P k a n * ex (t * Real.log n) := by
  classical
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hterm : ∀ x ∈ P ×ˢ P, a x.1 * ex (t * Real.log ((x.1 : ℝ) ^ k)) * (a x.2 * ex (t * Real.log ((x.2 : ℝ) ^ k)))
      = a x.1 * a x.2 * ex (t * Real.log (gk k x)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    have p1 : (0 : ℝ) < x.1 := by exact_mod_cast (hP _ h1).pos
    have p2 : (0 : ℝ) < x.2 := by exact_mod_cast (hP _ h2).pos
    have hl : Real.log ((x.1 : ℝ) ^ k) + Real.log ((x.2 : ℝ) ^ k) = Real.log (gk k x : ℝ) := by
      simp only [gk]; push_cast
      rw [← Real.log_mul (by positivity) (by positivity), mul_pow]
    calc a x.1 * ex (t * Real.log ((x.1 : ℝ) ^ k)) * (a x.2 * ex (t * Real.log ((x.2 : ℝ) ^ k)))
        = a x.1 * a x.2 * (ex (t * Real.log ((x.1 : ℝ) ^ k)) * ex (t * Real.log ((x.2 : ℝ) ^ k))) := by ring
      _ = a x.1 * a x.2 * ex (t * Real.log (gk k x)) := by
          rw [ex_add, ← mul_add, hl]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_fiberwise_of_maps_to (s := P ×ˢ P) (t := (P ×ˢ P).image (gk k)) (g := gk k)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold cco
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [(Finset.mem_filter.mp hx).2]

lemma sum_norm_cco_sq (hP : ∀ p ∈ P, p.Prime) (hk : 1 ≤ k) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    ∑ n ∈ (P ×ˢ P).image (gk k), w n * ‖cco P k a n‖ ^ 2
      ≤ 2 * ∑ x ∈ P ×ˢ P, w (gk k x) * (‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2) := by
  classical
  have hn : ∀ n, ‖cco P k a n‖ ^ 2 ≤
      2 * ∑ x ∈ (P ×ˢ P).filter (fun x => gk k x = n), ‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2 := by
    intro n
    unfold cco
    set F := (P ×ˢ P).filter (fun x => gk k x = n)
    have h1 : ‖∑ x ∈ F, a x.1 * a x.2‖ ≤ ∑ x ∈ F, ‖a x.1‖ * ‖a x.2‖ := by
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun x _ => norm_mul _ _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := F) (f := fun x => ‖a x.1‖ * ‖a x.2‖)
    have h3 : (F.card : ℝ) ≤ 2 := by exact_mod_cast fiber_card_le P k hP hk n
    have h4 : 0 ≤ ∑ x ∈ F, (‖a x.1‖ * ‖a x.2‖) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc ‖∑ x ∈ F, a x.1 * a x.2‖ ^ 2 ≤ (∑ x ∈ F, ‖a x.1‖ * ‖a x.2‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ F.card * ∑ x ∈ F, (‖a x.1‖ * ‖a x.2‖) ^ 2 := h2
      _ ≤ 2 * ∑ x ∈ F, (‖a x.1‖ * ‖a x.2‖) ^ 2 := mul_le_mul_of_nonneg_right h3 h4
      _ = 2 * ∑ x ∈ F, ‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2 := by
          congr 1; exact Finset.sum_congr rfl (fun x _ => by ring)
  calc ∑ n ∈ (P ×ˢ P).image (gk k), w n * ‖cco P k a n‖ ^ 2
      ≤ ∑ n ∈ (P ×ˢ P).image (gk k), w n * (2 * ∑ x ∈ (P ×ˢ P).filter (fun x => gk k x = n),
          ‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2) := Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (hn n) (hw n))
    _ = 2 * ∑ n ∈ (P ×ˢ P).image (gk k), ∑ x ∈ (P ×ˢ P).filter (fun x => gk k x = n),
          w (gk k x) * (‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [(Finset.mem_filter.mp hx).2]; ring
    _ = 2 * ∑ x ∈ P ×ˢ P, w (gk k x) * (‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2) := by
        rw [Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx)]

end

lemma sum_prod_sep (P : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ x ∈ P ×ˢ P, f x.1 * g x.2 = (∑ p ∈ P, f p) * ∑ p ∈ P, g p := by
  rw [Finset.sum_mul_sum, Finset.sum_product]

/-- **Fourth moment of a prime Dirichlet polynomial.**
`∫_U^{2U} |Σ_{p∈P} a_p p^{-ikt}|⁴ ≤ 2U V² + 2C W²`, `V = Σ|a_p|²`, `W = Σ(p^k+1)|a_p|²`. -/
theorem prime_fourth_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ (k : ℕ), 1 ≤ k →
      ∀ (a : ℕ → ℂ) (U : ℝ), 0 ≤ U →
      (∫ t in U..2 * U, ‖∑ p ∈ P, a p * ex (t * Real.log ((p : ℝ) ^ k))‖ ^ 4)
        ≤ 2 * U * (∑ p ∈ P, ‖a p‖ ^ 2) ^ 2
          + 2 * C * (∑ p ∈ P, ((p : ℝ) ^ k + 1) * ‖a p‖ ^ 2) ^ 2 := by
  classical
  obtain ⟨C, hC, hMV⟩ := mean_value
  refine ⟨C, hC, ?_⟩
  intro P hP k hk a U hU
  set s := (P ×ˢ P).image (gk k)
  have hs : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    have := pow_pos (Nat.mul_pos (hP _ h1).pos (hP _ h2).pos) k
    simp only [gk]; omega
  have hfun : (fun t : ℝ => ‖∑ p ∈ P, a p * ex (t * Real.log ((p : ℝ) ^ k))‖ ^ 4)
      = fun t => ‖∑ n ∈ s, cco P k a n * ex (t * Real.log n)‖ ^ 2 := by
    funext t
    rw [← D_sq P k a hP t, norm_pow]; ring
  rw [hfun]
  have h := hMV s hs (cco P k a) U
  have hup := (abs_le.mp h).2
  -- the two coefficient sums
  have h1 : ∑ n ∈ s, ‖cco P k a n‖ ^ 2 ≤ 2 * (∑ p ∈ P, ‖a p‖ ^ 2) ^ 2 := by
    have := sum_norm_cco_sq P k a hP hk (fun _ => 1) (fun _ => zero_le_one)
    simp only [one_mul] at this
    rw [sq, ← sum_prod_sep]; exact this
  have h2 : ∑ n ∈ s, ((n : ℝ) + 1) * ‖cco P k a n‖ ^ 2
      ≤ 2 * (∑ p ∈ P, ((p : ℝ) ^ k + 1) * ‖a p‖ ^ 2) ^ 2 := by
    have := sum_norm_cco_sq P k a hP hk (fun n => (n : ℝ) + 1) (fun n => by positivity)
    refine le_trans this ?_
    rw [sq, ← sum_prod_sep]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x hx => ?_)) (by norm_num)
    have e : ((gk k x : ℕ) : ℝ) = (x.1 : ℝ) ^ k * (x.2 : ℝ) ^ k := by
      simp only [gk]; push_cast; ring
    rw [e]
    have hA : 0 ≤ ‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2 := by positivity
    have hp : 0 ≤ (x.1 : ℝ) ^ k := by positivity
    have hq : 0 ≤ (x.2 : ℝ) ^ k := by positivity
    have : (x.1 : ℝ) ^ k * (x.2 : ℝ) ^ k + 1 ≤ ((x.1 : ℝ) ^ k + 1) * ((x.2 : ℝ) ^ k + 1) := by
      nlinarith
    calc ((x.1 : ℝ) ^ k * (x.2 : ℝ) ^ k + 1) * (‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2)
        ≤ ((x.1 : ℝ) ^ k + 1) * ((x.2 : ℝ) ^ k + 1) * (‖a x.1‖ ^ 2 * ‖a x.2‖ ^ 2) :=
          mul_le_mul_of_nonneg_right this hA
      _ = ((x.1 : ℝ) ^ k + 1) * ‖a x.1‖ ^ 2 * (((x.2 : ℝ) ^ k + 1) * ‖a x.2‖ ^ 2) := by ring
  have hc1 : U * ∑ n ∈ s, ‖cco P k a n‖ ^ 2 ≤ U * (2 * (∑ p ∈ P, ‖a p‖ ^ 2) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hU
  have hc2 := mul_le_mul_of_nonneg_left h2 hC
  nlinarith [hup, hc1, hc2]

end RvmClock
