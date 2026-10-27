#!/usr/bin/env python3
"""Generate PaperMath/Papers/RvmClock/C1.lean: C₁ ≤ 0.0978293 by exact piecewise integration.

Integral I = ∫_0^π eStar(c + R cos θ) dθ, c = 1.000002, R = 1.000005.
Atoms: arcsin y_a = arcsin((c-a)/R) (θa a = π/2 + arcsin y_a), arcsin z_a = arcsin((c+a-1)/R)
(θb a = π/2 + arcsin z_a), √(1-((a-c)/R)²) = sin θa a, √(1-((1-a-c)/R)²) = sin θb a, π, dd.
All bounds are exact rationals checked with Fraction arithmetic; mpmath only to pick the candidates.
"""
from fractions import Fraction as F
from mpmath import mp, mpf, asin, sqrt, pi, log, acos, cos, quad
import math
mp.dps = 50
DIG = 12                                  # decimals of the rational bounds
def mpq(q): return mpf(q.numerator) / mpf(q.denominator)
def dec(q):
    q = F(q); n = q * 10**DIG; assert n.denominator == 1, q
    sign = '-' if n < 0 else ''; n = abs(n.numerator)
    s = str(n).rjust(DIG + 1, '0'); r = (s[:-DIG] + '.' + s[-DIG:]).rstrip('0').rstrip('.')
    return sign + r
def floor_dec(v): return F(math.floor(v * 10**DIG), 10**DIG)
def ceil_dec(v): return F(math.floor(v * 10**DIG) + 1, 10**DIG)

c = F(1000002, 10**6); R = F(1000005, 10**6)
nodes = [F(1,2), F(5,7), F(5,6), F(28,31), F(17,18), F(123,127), F(167,170), F(1)]
nodes_lean = ['1/2', '5/7', '5/6', '28/31', '17/18', '123/127', '167/170', '1']
vals = [F(27,164), F(1,14), F(1,30), F(1,62), F(1,126), F(1,254), F(1,510), F(0)]
s = [(vals[i+1]-vals[i])/(nodes[i+1]-nodes[i]) for i in range(7)]

# ---- exact-rational Taylor partial sums of sin ----
def sin_partial(u, n):   # ∑_{i<n} (-1)^i u^(2i+1)/(2i+1)!
    return sum(F((-1)**i) * u**(2*i+1) / math.factorial(2*i+1) for i in range(n))
def kterms(u):
    u = float(u)
    return 6 if u <= 0.6 else (8 if u <= 1.0 else 10)

def arcsin_bounds(y):
    """rational lo, hi with lo ≤ arcsin y ≤ hi, certified: sin lo ≤ y (via odd partial ≥ sin) and
    y ≤ sin hi (via even partial ≤ sin)."""
    v = asin(mpq(y))
    lo = floor_dec(v); hi = ceil_dec(v); k = kterms(hi)
    while not (sin_partial(lo, 2*k+1) <= y): lo -= F(1, 10**DIG)
    while not (y <= sin_partial(hi, 2*k)): hi += F(1, 10**DIG)
    assert 0 < lo and hi <= F(157, 100) and hi**2 <= 6
    return lo, hi, k
def sqrt_bounds(w):      # w rational in (0,1]; lo ≤ √w ≤ hi with lo² ≤ w ≤ hi²
    v = sqrt(mpq(w)); lo = floor_dec(v); hi = ceil_dec(v)
    while not (lo**2 <= w): lo -= F(1, 10**DIG)
    while not (w <= hi**2): hi += F(1, 10**DIG)
    assert lo >= 0
    return lo, hi

atoms = []   # (kind, lean_expr, lo, hi, extra, group)
# y_a = (c - a)/R, z_a = (c + a - 1)/R  (a in nodes; z only for a ≥ 5/7)
for a, al in zip(nodes, nodes_lean):
    y = (c - a) / R
    lo, hi, k = arcsin_bounds(y)
    atoms.append(('arcsin', f"Real.arcsin ((1.000002 - {al}) / 1.000005)", lo, hi, (y, k), 'A'))
    w = 1 - ((a - c) / R)**2
    lo, hi = sqrt_bounds(w)
    atoms.append(('sqrt', f"Real.sqrt (1 - (({al} - 1.000002) / 1.000005) ^ 2)", lo, hi, (w,), 'S'))
for a, al in zip(nodes[1:], nodes_lean[1:]):
    z = (c + a - 1) / R
    lo, hi, k = arcsin_bounds(z)
    atoms.append(('arcsin', f"Real.arcsin ((1.000002 + {al} - 1) / 1.000005)", lo, hi, (z, k), 'B'))
    w = 1 - ((1 - a - c) / R)**2
    lo, hi = sqrt_bounds(w)
    atoms.append(('sqrt', f"Real.sqrt (1 - ((1 - {al} - 1.000002) / 1.000005) ^ 2)", lo, hi, (w,), 'T'))

# ---- the closed form of I in terms of the atoms, as an interval computation (sanity) ----
# I = 27/164 θh + s0 ((c-1/2) θh + R sinθh) + Σ_{i=1..6} (s_i - s_{i-1}) ((c - a_i) θa_i + R sinθa_i)
#     + (0 - s6)((c-1) θa_1 + R sinθa_1)
#     + (1/2 - c)(π - θh) + R sinθh
#     + 27/164 (π - θh) + s0 ((1/2 - c)(π - θh) + R sinθh)
#     + Σ_{i=1..6} (s_i - s_{i-1}) ((1 - c - a_i)(π - θb_i) + R sinθb_i) + (0 - s6)((1 - c - 1)(π - θb_1) + R sinθb_1)
# with θa = π/2 + arcsin y, θb = π/2 + arcsin z. Evaluate with mpmath at the true values and at the bounds.
pi_lo = F('3.14159265358979323846'); pi_hi = F('3.14159265358979323847')
def I_of(av, sv, bv, tv, PI):   # av: arcsin y_a (8), sv: sin θa (8), bv: arcsin z_a (7), tv: sin θb (7)
    tha = [PI/2 + v for v in av]; thb = [PI/2 + v for v in bv]
    thh = tha[0]
    I = F(27,164)*thh + s[0]*((c - F(1,2))*thh + R*sv[0])
    for i in range(1, 7): I += (s[i]-s[i-1])*((c - nodes[i])*tha[i] + R*sv[i])
    I += (0 - s[6])*((c - 1)*tha[7] + R*sv[7])
    I += (F(1,2) - c)*(PI - thh) + R*sv[0]
    I += F(27,164)*(PI - thh) + s[0]*((F(1,2) - c)*(PI - thh) + R*sv[0])
    for i in range(1, 7): I += (s[i]-s[i-1])*((1 - c - nodes[i])*(PI - thb[i-1]) + R*tv[i-1])
    I += (0 - s[6])*((1 - c - 1)*(PI - thb[6]) + R*tv[6])
    return I
A = [x for x in atoms if x[5]=='A']; S = [x for x in atoms if x[5]=='S']
B = [x for x in atoms if x[5]=='B']; T = [x for x in atoms if x[5]=='T']
assert len(A)==8 and len(S)==8 and len(B)==7 and len(T)==7
# true value (mp)
I_true = I_of([asin(mpq(x[4][0])) for x in A], [sqrt(mpq(x[4][0])) for x in S],
              [asin(mpq(x[4][0])) for x in B], [sqrt(mpq(x[4][0])) for x in T], pi)
d_true = log(mpq(R)/(mpq(c) - mpf(1)/2))
print("I_true", I_true, "C1", I_true/(2*pi*d_true))
# worst case upper bound of I over the boxes (coefficients have signs; do a crude max over corners is 2^30 — instead
# use linear programming by sign: I is linear in atoms, so take hi for positive coefficients, lo for negative)
def coeffs():
    base = I_of([F(0)]*8, [F(0)]*8, [F(0)]*7, [F(0)]*7, F(0))
    cs = []
    for grp, n in (('A',8),('S',8),('B',7),('T',7),('P',1)):
        for j in range(n):
            av=[F(0)]*8; sv=[F(0)]*8; bv=[F(0)]*7; tv=[F(0)]*7; PI=F(0)
            if grp=='A': av[j]=F(1)
            if grp=='S': sv[j]=F(1)
            if grp=='B': bv[j]=F(1)
            if grp=='T': tv[j]=F(1)
            if grp=='P': PI=F(1)
            cs.append(I_of(av,sv,bv,tv,PI) - base)
    return base, cs
base, cs = coeffs()
allatoms = A + S + B + T
I_hi = base
for (x, cf) in zip(allatoms, cs[:30]):
    I_hi += cf * (x[3] if cf > 0 else x[2])
cpi = cs[30]; I_hi += cpi * (pi_hi if cpi > 0 else pi_lo)
# dd lower bound: log 2 ≥ 0.6931471803, log(1.000005/1.000004) ≥ 1 - 1.000004/1.000005
d_lo = F('0.6931471803') + (1 - F(1000004, 1000005))
rhs = F('0.0978293') * 2 * pi_lo * d_lo
print("I_hi", float(I_hi), "rhs", float(rhs), "ok" if I_hi <= rhs else "FAIL", "slack", float(rhs - I_hi))
assert I_hi <= rhs

# ---- Lean output ----
L = []
L.append('''import PaperMath.Common.TrigBounds
import PaperMath.Papers.RvmClock.Thm13Zeta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The numerical input `C₁ ≤ 0.0978293` of Theorem 1.3

`C₁ = (1/(2π𝔡)) ∫₀^π 𝔢_E^*(c + R cos θ) dθ`, `c = 1.000002`, `R = 1.000005`, `𝔡 = log (R/(c - 1/2))`.
Value `0.0978292318785…`; margin `6.8 · 10⁻⁸`.

The integrand is piecewise linear in `cos θ` (`Profile.gE` is a sum of hinge terms `max 0 (σ - ς_i)`), so the
integral is computed exactly:
* on `[0, θ_h]` (`σ ≥ 1/2`, `θ_h = arccos ((1/2 - c)/R)`), `𝔢_E^* = gE`, and each hinge integrates to
  `(c - a) θ_a + R sin θ_a`, `θ_a = arccos ((a - c)/R)` (`int_max_a`);
* on `[θ_h, π]` (`σ ≤ 1/2`), `𝔢_E^* = 1/2 - σ + gE (1 - σ)`, and each hinge integrates to
  `(1 - c - a)(π - θ'_a) + R sin θ'_a`, `θ'_a = arccos ((1 - a - c)/R)` (`int_max_b`).
With `arccos x = π/2 + arcsin (-x)` and `sin (arccos x) = √(1 - x²)`, `I` is a linear combination of
`π`, 15 values `arcsin y` (`y` rational) and 15 square roots of rationals; each is bounded to 12 decimals
(`Common.TrigBounds`: alternating Taylor series of `sin`, `Real.pi_gt_d20`), and `linarith` closes.
-/

open Real RvmClock.Profile RvmClock.Explicit RvmClock.ZetaLines Common.TrigBounds intervalIntegral

namespace RvmClock.C1

/-- Kink angle of `max 0 (c + R cos θ - a)`. -/
noncomputable def θa (a : ℝ) : ℝ := arccos ((a - cc) / RR)
/-- Kink angle of `max 0 (1 - (c + R cos θ) - a)`. -/
noncomputable def θb (a : ℝ) : ℝ := arccos ((1 - a - cc) / RR)
/-- `θ_h = θa (1/2)`: the angle where `σ = 1/2`. -/
noncomputable def θh : ℝ := θa (1 / 2)

lemma RR_pos : 0 < RR := by unfold RR; norm_num
lemma RR_ne : RR ≠ 0 := RR_pos.ne'

lemma xa_mem {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : -1 ≤ (a - cc) / RR ∧ (a - cc) / RR ≤ 1 := by
  unfold cc RR
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith

lemma xb_mem {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) :
    -1 ≤ (1 - a - cc) / RR ∧ (1 - a - cc) / RR ≤ 1 := by
  unfold cc RR
  constructor
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [div_le_iff₀ (by norm_num)]; linarith

lemma cos_θa {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : cos (θa a) = (a - cc) / RR :=
  cos_arccos (xa_mem h1 h2).1 (xa_mem h1 h2).2
lemma cos_θb {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : cos (θb a) = (1 - a - cc) / RR :=
  cos_arccos (xb_mem h1 h2).1 (xb_mem h1 h2).2
lemma θa_nonneg (a : ℝ) : 0 ≤ θa a := arccos_nonneg _
lemma θa_le_pi (a : ℝ) : θa a ≤ π := arccos_le_pi _
lemma θb_nonneg (a : ℝ) : 0 ≤ θb a := arccos_nonneg _
lemma θb_le_pi (a : ℝ) : θb a ≤ π := arccos_le_pi _
lemma θh_nonneg : 0 ≤ θh := θa_nonneg _
lemma θh_le_pi : θh ≤ π := θa_le_pi _
lemma cos_θh : cos θh = (1 / 2 - cc) / RR := cos_θa (by norm_num) (by norm_num)

lemma θa_le_θh {a : ℝ} (h1 : 1 / 2 ≤ a) : θa a ≤ θh := by
  unfold θh θa
  apply arccos_le_arccos
  exact div_le_div_of_nonneg_right (by linarith) RR_pos.le

lemma θh_le_θb {a : ℝ} (h1 : 1 / 2 ≤ a) : θh ≤ θb a := by
  unfold θh θa θb
  apply arccos_le_arccos
  exact div_le_div_of_nonneg_right (by linarith) RR_pos.le

/-! ### Elementary integrals -/

lemma integral_lin (a α β : ℝ) :
    ∫ θ in α..β, (cc + RR * cos θ - a) = (cc - a) * (β - α) + RR * (sin β - sin α) := by
  have e : (fun θ => cc + RR * cos θ - a) = fun θ => (cc - a) + RR * cos θ := by funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => RR * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

lemma integral_lin' (a α β : ℝ) :
    ∫ θ in α..β, (1 - (cc + RR * cos θ) - a) = (1 - cc - a) * (β - α) - RR * (sin β - sin α) := by
  have e : (fun θ => 1 - (cc + RR * cos θ) - a) = fun θ => (1 - cc - a) + (-RR) * cos θ := by
    funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -RR * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

lemma integral_half (α β : ℝ) :
    ∫ θ in α..β, (1 / 2 - (cc + RR * cos θ)) = (1 / 2 - cc) * (β - α) - RR * (sin β - sin α) := by
  have e : (fun θ => 1 / 2 - (cc + RR * cos θ)) = fun θ => (1 / 2 - cc) + (-RR) * cos θ := by
    funext θ; ring
  rw [e, integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ : ℝ => -RR * cos θ).intervalIntegrable _ _), integral_const,
    integral_const_mul, integral_cos, smul_eq_mul]
  ring

/-- `∫₀^{θ_h} max 0 (c + R cos θ - a) = (c - a) θ_a + R sin θ_a` for `1/2 ≤ a ≤ 1`. -/
lemma int_max_a {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) :
    ∫ θ in (0 : ℝ)..θh, max 0 (cc + RR * cos θ - a) = (cc - a) * θa a + RR * sin (θa a) := by
  have hI : ∀ α β : ℝ, IntervalIntegrable (fun θ => max 0 (cc + RR * cos θ - a)) MeasureTheory.volume α β :=
    fun α β => (continuous_const.max (by fun_prop)).intervalIntegrable α β
  have hR := RR_ne
  have hc := cos_θa h1 h2
  have hcR : RR * ((a - cc) / RR) = a - cc := by field_simp
  rw [← integral_add_adjacent_intervals (hI 0 (θa a)) (hI (θa a) θh)]
  have e1 : ∫ θ in (0 : ℝ)..θa a, max 0 (cc + RR * cos θ - a)
      = ∫ θ in (0 : ℝ)..θa a, (cc + RR * cos θ - a) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θa_nonneg a)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 (θa_le_pi a) hθ.2
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_right (by linarith)
  have e2 : ∫ θ in θa a..θh, max 0 (cc + RR * cos θ - a) = ∫ θ in θa a..θh, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θa_le_θh h1)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θa_nonneg a) (hθ.2.trans θh_le_pi) hθ.1
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_left (by linarith)
  rw [e1, e2, integral_lin, integral_zero, sin_zero]
  ring

/-- `∫_{θ_h}^π max 0 (1 - (c + R cos θ) - a) = (1 - c - a)(π - θ'_a) + R sin θ'_a` for `1/2 ≤ a ≤ 1`. -/
lemma int_max_b {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) :
    ∫ θ in θh..π, max 0 (1 - (cc + RR * cos θ) - a)
      = (1 - cc - a) * (π - θb a) + RR * sin (θb a) := by
  have hI : ∀ α β : ℝ,
      IntervalIntegrable (fun θ => max 0 (1 - (cc + RR * cos θ) - a)) MeasureTheory.volume α β :=
    fun α β => (continuous_const.max (by fun_prop)).intervalIntegrable α β
  have hR := RR_ne
  have hc := cos_θb h1 h2
  have hcR : RR * ((1 - a - cc) / RR) = 1 - a - cc := by field_simp
  rw [← integral_add_adjacent_intervals (hI θh (θb a)) (hI (θb a) π)]
  have e1 : ∫ θ in θh..θb a, max 0 (1 - (cc + RR * cos θ) - a) = ∫ θ in θh..θb a, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θh_le_θb h1)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θh_nonneg.trans hθ.1) (θb_le_pi a) hθ.2
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_left (by linarith)
  have e2 : ∫ θ in θb a..π, max 0 (1 - (cc + RR * cos θ) - a)
      = ∫ θ in θb a..π, (1 - (cc + RR * cos θ) - a) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (θb_le_pi a)] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi (θb_nonneg a) hθ.2 hθ.1
    rw [hc] at h
    have h' := mul_le_mul_of_nonneg_left h RR_pos.le
    rw [hcR] at h'
    dsimp only
    exact max_eq_right (by linarith)
  rw [e1, e2, integral_lin', integral_zero, sin_pi]
  ring

/-! ### The two halves of the integral -/

lemma eStar_left {θ : ℝ} (hθ : θ ∈ Set.uIcc 0 θh) :
    eStar (cc + RR * cos θ) = gE (cc + RR * cos θ) := by
  rw [Set.uIcc_of_le θh_nonneg] at hθ
  have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 θh_le_pi hθ.2
  rw [cos_θh] at h
  have hR := RR_ne
  have hcR : RR * ((1 / 2 - cc) / RR) = 1 / 2 - cc := by field_simp
  have h' := mul_le_mul_of_nonneg_left h RR_pos.le
  rw [hcR] at h'
  exact eStar_of_half_le (by linarith)

lemma eStar_right {θ : ℝ} (hθ : θ ∈ Set.uIcc θh π) :
    eStar (cc + RR * cos θ) = 1 / 2 - (cc + RR * cos θ) + gE (1 - (cc + RR * cos θ)) := by
  rw [Set.uIcc_of_le θh_le_pi] at hθ
  have h := cos_le_cos_of_nonneg_of_le_pi θh_nonneg hθ.2 hθ.1
  rw [cos_θh] at h
  have hR := RR_ne
  have hcR : RR * ((1 / 2 - cc) / RR) = 1 / 2 - cc := by field_simp
  have h' := mul_le_mul_of_nonneg_left h RR_pos.le
  rw [hcR] at h'
  exact eStar_of_le_half (by linarith)

lemma integral_left :
    ∫ θ in (0 : ℝ)..θh, gE (cc + RR * cos θ)
      = 27 / 164 * θh + s0 * ((cc - 1 / 2) * θh + RR * sin θh)
        + (s1 - s0) * ((cc - 5 / 7) * θa (5 / 7) + RR * sin (θa (5 / 7)))
        + (s2 - s1) * ((cc - 5 / 6) * θa (5 / 6) + RR * sin (θa (5 / 6)))
        + (s3 - s2) * ((cc - 28 / 31) * θa (28 / 31) + RR * sin (θa (28 / 31)))
        + (s4 - s3) * ((cc - 17 / 18) * θa (17 / 18) + RR * sin (θa (17 / 18)))
        + (s5 - s4) * ((cc - 123 / 127) * θa (123 / 127) + RR * sin (θa (123 / 127)))
        + (s6 - s5) * ((cc - 167 / 170) * θa (167 / 170) + RR * sin (θa (167 / 170)))
        + (0 - s6) * ((cc - 1) * θa 1 + RR * sin (θa 1)) := by
  simp only [gE]
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_add, integral_add]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_lin, int_max_a (a := 5 / 7) (by norm_num) (by norm_num),
      int_max_a (a := 5 / 6) (by norm_num) (by norm_num),
      int_max_a (a := 28 / 31) (by norm_num) (by norm_num),
      int_max_a (a := 17 / 18) (by norm_num) (by norm_num),
      int_max_a (a := 123 / 127) (by norm_num) (by norm_num),
      int_max_a (a := 167 / 170) (by norm_num) (by norm_num),
      int_max_a (a := 1) (by norm_num) (by norm_num), sin_zero]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma integral_right :
    ∫ θ in θh..π, (1 / 2 - (cc + RR * cos θ) + gE (1 - (cc + RR * cos θ)))
      = (1 / 2 - cc) * (π - θh) + RR * sin θh
        + (27 / 164 * (π - θh) + s0 * ((1 / 2 - cc) * (π - θh) + RR * sin θh)
        + (s1 - s0) * ((1 - cc - 5 / 7) * (π - θb (5 / 7)) + RR * sin (θb (5 / 7)))
        + (s2 - s1) * ((1 - cc - 5 / 6) * (π - θb (5 / 6)) + RR * sin (θb (5 / 6)))
        + (s3 - s2) * ((1 - cc - 28 / 31) * (π - θb (28 / 31)) + RR * sin (θb (28 / 31)))
        + (s4 - s3) * ((1 - cc - 17 / 18) * (π - θb (17 / 18)) + RR * sin (θb (17 / 18)))
        + (s5 - s4) * ((1 - cc - 123 / 127) * (π - θb (123 / 127)) + RR * sin (θb (123 / 127)))
        + (s6 - s5) * ((1 - cc - 167 / 170) * (π - θb (167 / 170)) + RR * sin (θb (167 / 170)))
        + (0 - s6) * ((1 - cc - 1) * (π - θb 1) + RR * sin (θb 1))) := by
  simp only [gE]
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_add, integral_add, integral_add]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_half, integral_lin', int_max_b (a := 5 / 7) (by norm_num) (by norm_num),
      int_max_b (a := 5 / 6) (by norm_num) (by norm_num),
      int_max_b (a := 28 / 31) (by norm_num) (by norm_num),
      int_max_b (a := 17 / 18) (by norm_num) (by norm_num),
      int_max_b (a := 123 / 127) (by norm_num) (by norm_num),
      int_max_b (a := 167 / 170) (by norm_num) (by norm_num),
      int_max_b (a := 1) (by norm_num) (by norm_num), sin_pi]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- `∫₀^π 𝔢_E^*(c + R cos θ) dθ` in closed form. -/
theorem integral_eStar_eq :
    ∫ θ in (0 : ℝ)..π, eStar (cc + RR * cos θ)
      = (27 / 164 * θh + s0 * ((cc - 1 / 2) * θh + RR * sin θh)
        + (s1 - s0) * ((cc - 5 / 7) * θa (5 / 7) + RR * sin (θa (5 / 7)))
        + (s2 - s1) * ((cc - 5 / 6) * θa (5 / 6) + RR * sin (θa (5 / 6)))
        + (s3 - s2) * ((cc - 28 / 31) * θa (28 / 31) + RR * sin (θa (28 / 31)))
        + (s4 - s3) * ((cc - 17 / 18) * θa (17 / 18) + RR * sin (θa (17 / 18)))
        + (s5 - s4) * ((cc - 123 / 127) * θa (123 / 127) + RR * sin (θa (123 / 127)))
        + (s6 - s5) * ((cc - 167 / 170) * θa (167 / 170) + RR * sin (θa (167 / 170)))
        + (0 - s6) * ((cc - 1) * θa 1 + RR * sin (θa 1)))
      + ((1 / 2 - cc) * (π - θh) + RR * sin θh
        + (27 / 164 * (π - θh) + s0 * ((1 / 2 - cc) * (π - θh) + RR * sin θh)
        + (s1 - s0) * ((1 - cc - 5 / 7) * (π - θb (5 / 7)) + RR * sin (θb (5 / 7)))
        + (s2 - s1) * ((1 - cc - 5 / 6) * (π - θb (5 / 6)) + RR * sin (θb (5 / 6)))
        + (s3 - s2) * ((1 - cc - 28 / 31) * (π - θb (28 / 31)) + RR * sin (θb (28 / 31)))
        + (s4 - s3) * ((1 - cc - 17 / 18) * (π - θb (17 / 18)) + RR * sin (θb (17 / 18)))
        + (s5 - s4) * ((1 - cc - 123 / 127) * (π - θb (123 / 127)) + RR * sin (θb (123 / 127)))
        + (s6 - s5) * ((1 - cc - 167 / 170) * (π - θb (167 / 170)) + RR * sin (θb (167 / 170)))
        + (0 - s6) * ((1 - cc - 1) * (π - θb 1) + RR * sin (θb 1)))) := by
  have hI : ∀ α β : ℝ, IntervalIntegrable (fun θ => eStar (cc + RR * cos θ)) MeasureTheory.volume α β :=
    fun α β => (eStar_continuous.comp (by fun_prop)).intervalIntegrable α β
  rw [← integral_add_adjacent_intervals (hI 0 θh) (hI θh π),
    integral_congr (fun θ hθ => eStar_left hθ), integral_congr (fun θ hθ => eStar_right hθ),
    integral_left, integral_right]

/-! ### The atoms: `θa a = π/2 + arcsin ((c - a)/R)`, `θb a = π/2 + arcsin ((c + a - 1)/R)`, and the sines -/

lemma θa_eq (a : ℝ) : θa a = π / 2 + arcsin ((cc - a) / RR) := by
  unfold θa
  rw [show (a - cc) / RR = -((cc - a) / RR) by ring, arccos_neg, arccos_eq_pi_div_two_sub_arcsin]
  ring

lemma θb_eq (a : ℝ) : θb a = π / 2 + arcsin ((cc + a - 1) / RR) := by
  unfold θb
  rw [show (1 - a - cc) / RR = -((cc + a - 1) / RR) by ring, arccos_neg,
    arccos_eq_pi_div_two_sub_arcsin]
  ring

lemma sin_θa (a : ℝ) : sin (θa a) = Real.sqrt (1 - ((a - cc) / RR) ^ 2) := by
  unfold θa; exact sin_arccos _

lemma sin_θb (a : ℝ) : sin (θb a) = Real.sqrt (1 - ((1 - a - cc) / RR) ^ 2) := by
  unfold θb; exact sin_arccos _

lemma θh_eq : θh = π / 2 + arcsin ((cc - 1 / 2) / RR) := θa_eq _
lemma sin_θh : sin θh = Real.sqrt (1 - ((1 / 2 - cc) / RR) ^ 2) := sin_θa _

/-- `𝔡 = log (R/(c - 1/2)) ≥ 0.6931471803 + 10⁻⁶/1.000005`. -/
lemma dd_ge : (0.6931471803 : ℝ) + (1 - 1000004 / 1000005) ≤ dd := by
  unfold dd cc RR
  have e : (1.000005 : ℝ) / (1.000002 - 1 / 2) = 2 * (1000005 / 1000004) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num)]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1000005 / 1000004 by norm_num)
  rw [inv_div] at h2
  linarith

/-! ### Rational bounds for the 15 arcsines and the 15 square roots (12 decimals) -/
''')
# numeric lemmas
names = []
for idx, (kind, expr, lo, hi, extra, grp) in enumerate(atoms):
    nm = f"atom{idx}"; names.append(nm)
    if kind == 'arcsin':
        y, k = extra
        L.append(f'''lemma {nm} : ({dec(lo)} : ℝ) ≤ {expr} ∧ {expr} ≤ {dec(hi)} := by
  have hy : ({expr.split('arcsin ')[1]} : ℝ) = {y.numerator} / {y.denominator} := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := {dec(lo)}) (by norm_num) (by norm_num) {k}
    have hs : ∑ i ∈ Finset.range (2 * {k} + 1), (-1 : ℝ) ^ i * sinTerm {dec(lo)} i
        ≤ {y.numerator} / {y.denominator} := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := {dec(hi)}) (by norm_num) (by norm_num) {k}
    have hs : ({y.numerator} : ℝ) / {y.denominator}
        ≤ ∑ i ∈ Finset.range (2 * {k}), (-1 : ℝ) ^ i * sinTerm {dec(hi)} i := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
''')
    else:
        (w,) = extra
        inner = expr[len('Real.sqrt '):]
        L.append(f'''lemma {nm} : ({dec(lo)} : ℝ) ≤ {expr} ∧ {expr} ≤ {dec(hi)} := by
  have hw : ({inner} : ℝ) = {w.numerator} / {w.denominator} := by norm_num
  rw [hw]
  exact ⟨le_sqrt_of_sq (by norm_num), sqrt_le_of_sq (by norm_num) (by norm_num)⟩
''')
L.append(f'''
/-- **Numerical input of Theorem 1.3**: `C₁ ≤ 0.0978293`. -/
theorem C1_le :
    (∫ θ in (0 : ℝ)..π, eStar (cc + RR * cos θ)) / (2 * π * dd) ≤ 0.0978293 := by
  rw [integral_eStar_eq, sin_θh, θh_eq]
  simp only [sin_θa, sin_θb]
  simp only [θa_eq, θb_eq]
  have hdd := dd_ge
  have hd0 := dd_pos
  rw [div_le_iff₀ (mul_pos (mul_pos two_pos Real.pi_pos) hd0)]
  have hπ1 := Real.pi_gt_d20
  have hπ2 := Real.pi_lt_d20
  have hpd : (3.14159265358979323846 : ℝ) * ((0.6931471803 : ℝ) + (1 - 1000004 / 1000005))
      ≤ π * dd := mul_le_mul hπ1.le hdd (by norm_num) (by linarith)
  simp only [cc, RR, s0, s1, s2, s3, s4, s5, s6, sl]
  obtain ⟨l0, u0⟩ := {names[0]}
''')
for j, nm in enumerate(names[1:], start=1):
    L.append(f"  obtain ⟨l{j}, u{j}⟩ := {nm}")
L.append("  linarith [hpd]\n")
L.append('''
/-- **Theorem 1.3** with all numerical inputs proved: only the literature inputs remain. -/
theorem theorem_1_3_numeric (S : ℝ → ℝ)
    (I : ExplicitInputs) (chi : ℂ → ℂ)
    (hFE : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      riemannZeta (sp σ t) = chi (sp σ t) * riemannZeta (1 - sp σ t))
    (hchi : ∀ σ ∈ Set.Icc (-0.01 : ℝ) (1/2), ∀ t : ℝ, 98 ≤ t →
      ‖chi (sp σ t)‖ ≤ 1.0070 * (t / (2 * Real.pi)) ^ (1/2 - σ))
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
    (hplatt : ∀ T, Real.exp 1 ≤ T → T ≤ 100 → |S T| ≤ 2.5167) :
    ∀ T, Real.exp 1 ≤ T →
      |S T| ≤ 0.09783 * Real.log T + 0.7214 * Real.log (Real.log T) + 10.6 :=
  Thm13.theorem_1_3_zeta S I chi hFE hchi Z A0 D1 D2 E hA hB hEc hdec hA0 hD1 C1_le hplatt

end RvmClock.C1
''')
open('/home/claude/papermath/PaperMath/Papers/RvmClock/C1.lean', 'w').write('\n'.join(L))
print("written; atoms:", len(atoms))
for kind, expr, lo, hi, extra, grp in atoms:
    print(kind, expr, dec(lo), dec(hi), extra[1] if kind=='arcsin' else '')
