import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mertens-type bounds used in Lemma 7.6 (replacing Theorem 3.10 of the article)

* `sum_log_div_le`  : `Σ_{p ≤ n} log p / p ≤ log n + log 4`  (Mertens' first theorem, upper bound);
* `sum_inv_prime_le`: `Σ_{Y ≤ p ≤ n} 1/p ≤ (log n + log 4) / log Y`;
* `nth_prime_le_sq`  : `p_m ≤ m²` for `m ≥ 8`.
-/

open Finset Real ArithmeticFunction

namespace RvmClock

/-- `log n! = Σ_{d ≤ n} Λ(d) · #{k ≤ n : d ∣ k}`. -/
lemma log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ d ∈ Ico 1 (n + 1), Λ d * (((Ico 1 (n + 1)).filter (fun k => d ∣ k)).card : ℝ) := by
  have h1 : (n.factorial : ℝ) = ∏ k ∈ Ico 1 (n + 1), (k : ℝ) := by
    rw [← Finset.prod_Ico_id_eq_factorial]; push_cast; rfl
  rw [h1, Real.log_prod (fun k hk => by
    have := (Finset.mem_Ico.mp hk).1; exact_mod_cast (show k ≠ 0 by omega))]
  have h2 : ∀ k ∈ Ico 1 (n + 1), Real.log (k : ℝ) = ∑ d ∈ k.divisors, Λ d := fun k _ => vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h2]
  rw [Finset.sum_comm' (t' := Ico 1 (n + 1)) (s' := fun d => (Ico 1 (n + 1)).filter (fun k => d ∣ k))]
  · refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro k d
    simp only [Finset.mem_Ico, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, Nat.pos_of_dvd_of_pos h3 (by omega), by
        have := Nat.le_of_dvd (by omega) h3; omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨h1, h2⟩, h3, by omega⟩

/-- `#{k ≤ n : d ∣ k} = n / d`. -/
lemma card_mult (n d : ℕ) : ((Ico 1 (n + 1)).filter (fun k => d ∣ k)).card = n / d := by
  have : Ico 1 (n + 1) = Ioc 0 n := by ext x; simp [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [this]; exact Nat.Ioc_filter_dvd_card_eq_div n d

lemma sum_floor_log_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℝ) := by
  rw [log_factorial_eq]
  have hsub : Nat.primesLE n ⊆ Ico 1 (n + 1) := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_Ico.mpr ⟨hp.2.one_lt.le, hp.1⟩
  calc ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
      = ∑ p ∈ Nat.primesLE n, Λ p * (((Ico 1 (n + 1)).filter (fun k => p ∣ k)).card : ℝ) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
        rw [vonMangoldt_apply_prime hp.2, card_mult, mul_comm]
    _ ≤ ∑ d ∈ Ico 1 (n + 1), Λ d * (((Ico 1 (n + 1)).filter (fun k => d ∣ k)).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => mul_nonneg vonMangoldt_nonneg (by positivity))

lemma log_factorial_le (n : ℕ) : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    _ = n * Real.log n := by rw [Real.log_pow]

/-- **Mertens' first theorem (upper bound)**: `Σ_{p ≤ n} log p / p ≤ log n + log 4` for `n ≥ 1`. -/
theorem sum_log_div_le {n : ℕ} (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]; exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hterm : ∀ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    have hfl : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := n) hp.2.pos
      rw [div_le_iff₀ hp0]
      have h2 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast this
      linarith
    calc (n : ℝ) * (Real.log p / p) = (n / p) * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hfl hlog
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
      ≤ ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE n, Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_le_sum hterm
  have h1 := sum_floor_log_le n
  have h2 := log_factorial_le n
  have h3 : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left h3 hn'

/-- `Σ_{Y ≤ p ≤ n} 1/p ≤ (log n + log 4) / log Y` for `Y > 1`. -/
theorem sum_inv_prime_le {n : ℕ} (hn : 1 ≤ n) {Y : ℝ} (hY : 1 < Y) :
    ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ => Y ≤ (p : ℝ)), (1 : ℝ) / p ≤ (Real.log n + Real.log 4) / Real.log Y := by
  have hlY : 0 < Real.log Y := Real.log_pos hY
  rw [le_div_iff₀ hlY, Finset.sum_mul]
  calc ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ => Y ≤ (p : ℝ)), (1 : ℝ) / p * Real.log Y
      ≤ ∑ p ∈ (Nat.primesLE n).filter (fun p : ℕ => Y ≤ (p : ℝ)), Real.log p / p := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hYp := (Finset.mem_filter.mp hp).2
        have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by linarith) hYp
        rw [div_mul_eq_mul_div, one_mul]
        exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hYp) hp0.le
    _ ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p hp _ => ?_)
        simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)) (Nat.cast_nonneg _)
    _ ≤ Real.log n + Real.log 4 := sum_log_div_le hn

/-- Chebyshev lower bound: `N log 2 - log (N+1) ≤ π(N) log N`. -/
lemma chebyshev_lower (N : ℕ) :
    (N : ℝ) * Real.log 2 - Real.log (N + 1) ≤ (Nat.primeCounting N : ℝ) * Real.log N := by
  have h1 := Chebyshev.two_pow_le_mul_lcmUpto N
  have h2 := Chebyshev.psi_eq_log_lcmUpto N
  have h3 := Chebyshev.psi_le_primeCounting_mul_log N
  have hl : (0 : ℝ) < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  have h4 : (N : ℝ) * Real.log 2 ≤ Real.log (N + 1) + Real.log (Nat.lcmUpto N) := by
    have h5 : ((2 : ℝ) ^ N) ≤ ((N : ℝ) + 1) * (Nat.lcmUpto N : ℝ) := by exact_mod_cast h1
    have h6 := Real.log_le_log (by positivity) h5
    rw [Real.log_pow, Real.log_mul (by positivity) hl.ne'] at h6
    linarith
  linarith

/-- `p_m ≤ m²` for `m ≥ 8` (here `prime (m-1) = Nat.nth Nat.Prime (m-1) = p_m`). -/
theorem nth_prime_le_sq {m : ℕ} (hm : 8 ≤ m) : Nat.nth Nat.Prime (m - 1) ≤ m ^ 2 := by
  have hm' : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- log m ≤ m/8 + log 8 - 1
  have hlm : Real.log m ≤ m / 8 + 3 * Real.log 2 - 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < m / 8 by positivity)
    rw [Real.log_div (by positivity) (by norm_num), show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have hlm0 : 0 < Real.log m := Real.log_pos (by linarith)
  set N := m ^ 2 with hN
  have hNr : (N : ℝ) = (m : ℝ) ^ 2 := by rw [hN]; push_cast; ring
  have hlogN : Real.log N = 2 * Real.log m := by rw [hNr, Real.log_pow]; push_cast; ring
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log m := by
    have : (N : ℝ) + 1 ≤ 2 * (m : ℝ) ^ 2 := by rw [hNr]; nlinarith
    calc Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (m : ℝ) ^ 2) := Real.log_le_log (by positivity) this
      _ = Real.log 2 + 2 * Real.log m := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have hcheb := chebyshev_lower N
  rw [hlogN, hNr] at hcheb
  have hpi : (m : ℝ) ≤ Nat.primeCounting N := by
    by_contra hc
    push Not at hc
    have h1 : (Nat.primeCounting N : ℝ) * (2 * Real.log m) < m * (2 * Real.log m) :=
      mul_lt_mul_of_pos_right hc (by positivity)
    have hlN1 : Real.log ((m : ℝ) ^ 2 + 1) ≤ Real.log 2 + 2 * Real.log m := by rw [← hNr]; exact hlogN1
    nlinarith [mul_le_mul_of_nonneg_left hlm (show (0:ℝ) ≤ 2 * m by positivity)]
  have hpi' : m ≤ Nat.primeCounting N := by exact_mod_cast hpi
  have hlt : m - 1 < Nat.count Nat.Prime (N + 1) := by
    have : Nat.primeCounting N = Nat.count Nat.Prime (N + 1) := rfl
    omega
  have := Nat.nth_lt_of_lt_count hlt
  omega

end RvmClock
