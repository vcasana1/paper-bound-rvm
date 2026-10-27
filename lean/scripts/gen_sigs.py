import json
from fractions import Fraction as F
d = json.load(open('/home/claude/lean/gen/sigs_numbers.json'))
eps = F(*d['eps']); digits = 12
def dec(q):
    q = F(q); n = q * 10**digits; assert n.denominator == 1, q
    sign = '-' if n < 0 else ''; n = abs(n.numerator)
    s = str(n).rjust(digits+1,'0'); r = (s[:-digits] + '.' + s[-digits:]).rstrip('0').rstrip('.')
    return sign + r
lines = d['lines']
Z = F(*d['Z'])
# Zd: decimal upper bound for Z with 12 decimals
import math
Zd = F(math.floor(Z*10**digits)+1, 10**digits); assert Zd >= Z
total_q = 1 + sum(F(q) for _,_,_,q in lines)
qt = F(d['qt']); qt1 = F(d['qt1'])
tail_bound = qt / (F(1,4)+eps)
Zcheck = total_q + tail_bound; assert Zcheck == Z
# log bound
x = 1 - Zd/8; nT = 36
s = sum(x**(i+1)/(i+1) for i in range(nT)); rem = x**(nT+1)/(1-x)
up = -s + rem
upd = F(math.floor(up*10**digits)+1, 10**digits); assert upd >= up
L2u = F(6931471808, 10**10)
assert 3*L2u + upd <= F(152499,100000), float(3*L2u+upd)
EPS = "1375007 / 500002500000"
out = []
out.append(f'''import PaperMath.Common.ZetaTail
import PaperMath.Common.LogBounds
import PaperMath.Papers.RvmClock.Explicit

/-!
# The numerical input `log ζ(σ♯) ≤ 1.52499` of Theorem 1.3

`σ♯ = c + (c - 1/2)²/R = 1.25000275000025 = 5/4 + ε₀`, `ε₀ = {EPS}` (exact), with `c = 1.000002`,
`R = 1.000005` (`RvmClock.Explicit.sigS`). Value: `log ζ(σ♯) = 1.5249835587…`; margin `6.4 · 10⁻⁶`.

Proof, all for Mathlib's `riemannZeta`:
* `ζ(σ♯) ≤ ∑_{{n<50}} n^{{-σ♯}} + (49.5)^{{1-σ♯}}/(σ♯-1)` (midpoint rule, `Common.ZetaTail.zeta_le_partial_add_tail`;
  the error of the tail is `≈ σ♯ · 50^{{-σ♯-1}}/24 < 8 · 10⁻⁶`);
* each `n^{{-σ♯}} = n^{{-5/4}} n^{{-ε₀}}` is bounded by a 12-digit decimal with `Common.ZetaTail.rpow_neg_add_le`
  (`1 ≤ q₁⁴ n⁵` and `n^{{-ε₀}} ≤ 1/(1 + ε₀ (k log 2 + 1 - 2^k/n))`, `2^k ≤ n`), every check by `norm_num`;
* the resulting bound is `ζ(σ♯) ≤ {dec(Zd)}` (true value `4.5950680197…`), and
  `log {dec(Zd)} = 3 log 2 + log (1 - x)`, `x = 1 - {dec(Zd)}/8`, is bounded by the Taylor series with
  remainder (`Common.LogBounds.log_one_sub_le`, 36 terms) and `Real.log_two_lt_d9`.
-/

open Finset Common.ZetaTail Common.LogBounds RvmClock.Explicit

namespace RvmClock.ZetaSigS

/-- `ε₀ = σ♯ - 5/4`, exactly. -/
lemma sigS_eq : sigS = 5 / 4 + ({EPS} : ℝ) := by
  unfold sigS cc RR; norm_num

lemma one_lt_sigS : 1 < sigS := by rw [sigS_eq]; norm_num

lemma sigS_pos : 0 < sigS := by linarith [one_lt_sigS]

/-- One term: `1/n^{{σ♯}} ≤ q` from the rational data `k, q₁, q`. -/
lemma term (n k : ℕ) (q₁ q : ℝ) (hn : 1 ≤ n) (hk : (2 : ℝ) ^ k ≤ n) (hq₁ : 0 < q₁)
    (h₁ : 1 ≤ q₁ ^ 4 * (n : ℝ) ^ 5)
    (hq : q₁ ≤ q * (1 + {EPS} * (k * 0.6931471803 + (1 - 2 ^ k / (n : ℝ))))) :
    1 / (n : ℝ) ^ sigS ≤ q := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [one_div, ← Real.rpow_neg (show (0 : ℝ) ≤ n by linarith), sigS_eq]
  exact rpow_neg_add_le 5 4 k (by norm_num) (by norm_num) hn' (by norm_num) hk hq₁ h₁ hq
''')
# single lemma: all 48 terms, range 50 unrolled
out.append(f"""
/-- `∑_{{n<50}} 1/n^{{σ♯}} ≤ {dec(total_q)}` (the terms `n = 0` and `n = 1` are `0` and `1`; the others are the
rational bounds of `term`). -/
lemma partial_sum_le : ∑ n ∈ range 50, 1 / (n : ℝ) ^ sigS ≤ {dec(total_q)} := by
  have t0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ sigS = 0 := by
    simp [Real.zero_rpow sigS_pos.ne']
  have t1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ sigS = 1 := by simp""")
for n,k,q1,q in lines:
    out.append(f"  have t{n} := term {n} {k} {dec(q1)} {dec(q)} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
out.append("  simp only [Finset.sum_range_succ, Finset.sum_range_zero]")
out.append("  linarith")
out.append("")
# tail bound decimal
tb = tail_bound
tbd = F(math.floor(tb*10**digits)+1, 10**digits)
# ensure total Zd >= total_q + tbd
assert total_q + tbd <= Zd, (float(total_q+tbd), float(Zd))
out[-1] = out[-1].replace("TAILBOUND", dec(tbd))
out.append(f'''lemma tail_le : (((50 : ℕ) : ℝ) - 1 / 2) ^ (1 - sigS) / (sigS - 1) ≤ {dec(tbd)} := by
  have hx : (1 : ℝ) ≤ ((50 : ℕ) : ℝ) - 1 / 2 := by norm_num
  have h := rpow_neg_add_le (x := ((50 : ℕ) : ℝ) - 1 / 2) (a := 1 / 4) (ε := {EPS})
    (q₁ := {dec(qt1)}) (q := {dec(qt)}) 1 4 5 (by norm_num) (by norm_num) hx (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [sigS_eq, show (1 : ℝ) - (5 / 4 + {EPS}) = -(1 / 4 + {EPS}) by norm_num]
  rw [show (5 / 4 + ({EPS} : ℝ)) - 1 = 1 / 4 + {EPS} by norm_num]
  calc _ ≤ ({dec(qt)} : ℝ) / (1 / 4 + {EPS}) := by gcongr
    _ ≤ _ := by norm_num

/-- `ζ(σ♯) ≤ {dec(Zd)}`. -/
theorem zeta_sigS_le : (riemannZeta (sigS : ℂ)).re ≤ {dec(Zd)} := by
  have h := zeta_le_partial_add_tail one_lt_sigS 50 (by norm_num)
  linarith [partial_sum_le, tail_le]

lemma log_Zd_le : Real.log ({dec(Zd)} : ℝ) ≤ 1.52499 := by
  have h := log_one_sub_le (x := 1 - {dec(Zd)} / 8) (by norm_num) (by norm_num) {nT}
  have e : Real.log (1 - (1 - {dec(Zd)} / 8)) = Real.log {dec(Zd)} - 3 * Real.log 2 := by
    rw [show (1 : ℝ) - (1 - {dec(Zd)} / 8) = {dec(Zd)} / 2 ^ 3 by norm_num,
      log_div_two_pow (by norm_num) 3]; push_cast; ring
  rw [e] at h
  have hs : -(∑ i ∈ range {nT}, (1 - {dec(Zd)} / 8 : ℝ) ^ (i + 1) / (i + 1))
      + (1 - {dec(Zd)} / 8 : ℝ) ^ ({nT} + 1) / (1 - (1 - {dec(Zd)} / 8)) ≤ {dec(upd)} := by
    norm_num [Finset.sum_range_succ]
  linarith [Real.log_two_lt_d9]

/-- **Numerical input of Theorem 1.3**: `log ζ(σ♯) ≤ 1.52499`. -/
theorem log_zeta_sigS_le : Real.log (riemannZeta (sigS : ℂ)).re ≤ 1.52499 := by
  have hpos : 0 < (riemannZeta (sigS : ℂ)).re := Common.ZetaSeries.zeta_re_pos one_lt_sigS
  exact le_trans (Real.log_le_log hpos zeta_sigS_le) log_Zd_le

end RvmClock.ZetaSigS
''')
open('/home/claude/papermath/PaperMath/Papers/RvmClock/ZetaSigS.lean','w').write('\n'.join(out))
print('Zd', dec(Zd), 'total_q', dec(total_q), 'tbd', dec(tbd), 'upd', dec(upd), float(3*L2u+upd))
