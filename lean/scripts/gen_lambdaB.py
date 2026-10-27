#!/usr/bin/env python3
"""Generate PaperMath/Papers/RvmClock/LambdaB.lean: certified bounds for Λ(𝔢_B) (Corollary 1.2).

Λ(𝔢_B) = (1/(2π log 2)) ∫_0^π 𝔢_B^*(1 + cos θ) dθ  (the form in which it arises in the proof of Theorem 1.1).
With c = R = 1 the hinge formulas of Common.HingeIntegral give I = ∫_0^π 𝔢_B^*(1 + cos θ) dθ as a
combination of π, arcsin(1 - a) (θ_a = π/2 + arcsin(1 - a)), arcsin(a) (θ'_a = π/2 + arcsin a),
√(1 - (a - 1)²) and √(1 - a²), a over the nodes. Every bound is an exact rational checked here with
Fraction arithmetic; mpmath only picks the candidates.
"""
from fractions import Fraction as F
from mpmath import mp, mpf, asin, sqrt, pi, log, acos, cos, quad
import math
mp.dps = 50
DIG = 13
def mpq(q): return mpf(q.numerator) / mpf(q.denominator)
def dec(q):
    q = F(q); n = q * 10**DIG; assert n.denominator == 1, q
    sign = '-' if n < 0 else ''; n = abs(n.numerator)
    s = str(n).rjust(DIG + 1, '0'); r = (s[:-DIG] + '.' + s[-DIG:]).rstrip('0').rstrip('.')
    return sign + r
def floor_dec(v): return F(math.floor(v * 10**DIG), 10**DIG)
def ceil_dec(v): return F(math.floor(v * 10**DIG) + 1, 10**DIG)
def lean_q(q): return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else f"{q.numerator}"

# ---- the nodes: Bourgain's pair and its images under the A-process ----
k, l = F(13, 84), F(55, 84)
pairs = []
for j in range(8):
    pairs.append((k, l)); k, l = k / (2*k + 2), F(1, 2) + l / (2*k + 2)
nodes = [l - k for k, l in pairs] + [F(1)]
vals = [k for k, l in pairs] + [F(0)]
assert nodes[0] == F(1, 2) and all(nodes[i] < nodes[i+1] for i in range(8))
assert all(vals[i] > vals[i+1] for i in range(8))
NN = len(nodes) - 1                       # 8 strips
s = [(vals[i+1] - vals[i]) / (nodes[i+1] - nodes[i]) for i in range(NN)]
print("nodes", [str(x) for x in nodes]); print("vals", [str(x) for x in vals])

def sin_partial(u, n): return sum(F((-1)**i) * u**(2*i+1) / math.factorial(2*i+1) for i in range(n))
def kterms(u):
    u = float(u)
    return 6 if u <= 0.6 else (8 if u <= 1.0 else 11)
def arcsin_bounds(y):
    v = asin(mpq(y)); lo = floor_dec(v); hi = ceil_dec(v); k = kterms(hi)
    while not (sin_partial(lo, 2*k+1) <= y): lo -= F(1, 10**DIG)
    while not (y <= sin_partial(hi, 2*k)): hi += F(1, 10**DIG)
    assert 0 < lo and hi <= F(157, 100) and hi**2 <= 6
    return lo, hi, k
def sqrt_bounds(w):
    v = sqrt(mpq(w)); lo = floor_dec(v); hi = ceil_dec(v)
    while not (lo**2 <= w): lo -= F(1, 10**DIG)
    while not (w <= hi**2): hi += F(1, 10**DIG)
    assert lo >= 0
    return lo, hi

# atoms: A_j = arcsin((1 - n_j)/1), S_j = √(1 - ((n_j - 1)/1)²) for j = 0..7 (n_0 = 1/2: θ_h);
#        B_j = arcsin((1 + n_j - 1)/1), T_j = √(1 - ((1 - n_j - 1)/1)²) for j = 1..7.
# The node 1: arcsin 0 = 0, √1 = 1, arcsin 1 = π/2, √0 = 0 (exact, proved separately).
atoms = []
for j in range(NN):
    a = nodes[j]; al = lean_q(a)
    y = 1 - a; lo, hi, kk = arcsin_bounds(y)
    atoms.append(('arcsin', f"Real.arcsin ((1 - {al}) / 1)", lo, hi, (y, kk), 'A'))
    w = 1 - (a - 1)**2; lo, hi = sqrt_bounds(w)
    atoms.append(('sqrt', f"Real.sqrt (1 - (({al} - 1) / 1) ^ 2)", lo, hi, (w,), 'S'))
for j in range(1, NN):
    a = nodes[j]; al = lean_q(a)
    y = a; lo, hi, kk = arcsin_bounds(y)
    atoms.append(('arcsin', f"Real.arcsin ((1 + {al} - 1) / 1)", lo, hi, (y, kk), 'B'))
    w = 1 - a**2; lo, hi = sqrt_bounds(w)
    atoms.append(('sqrt', f"Real.sqrt (1 - ((1 - {al} - 1) / 1) ^ 2)", lo, hi, (w,), 'T'))

# ---- closed form of I (c = R = 1), in the order of integral_left / integral_right ----
def I_of(A, S, B, T, PI, A1, S1, B1, T1):
    """A[j], S[j] (j=0..7): arcsin(1-n_j), √(1-(n_j-1)²); B[j], T[j] (j=1..7); node 1: A1, S1, B1, T1."""
    c = R = 1
    tha = [PI/2 + v for v in A]; thh = tha[0]
    I = vals[0]*thh + s[0]*((c - F(1,2))*thh + R*S[0])
    for i in range(1, NN): I += (s[i]-s[i-1])*((c - nodes[i])*tha[i] + R*S[i])
    I += (0 - s[NN-1])*((c - 1)*(PI/2 + A1) + R*S1)
    I += (F(1,2) - c)*(PI - thh) + R*S[0]
    I += vals[0]*(PI - thh) + s[0]*((F(1,2) - c)*(PI - thh) + R*S[0])
    for i in range(1, NN): I += (s[i]-s[i-1])*((1 - c - nodes[i])*(PI - (PI/2 + B[i])) + R*T[i])
    I += (0 - s[NN-1])*((1 - c - 1)*(PI - (PI/2 + B1)) + R*T1)
    return I

A_ = [x for x in atoms if x[5]=='A']; S_ = [x for x in atoms if x[5]=='S']
B_ = [x for x in atoms if x[5]=='B']; T_ = [x for x in atoms if x[5]=='T']
def unpack(f):
    return ([f(x) for x in A_], [f(x) for x in S_], [None] + [f(x) for x in B_], [None] + [f(x) for x in T_])
Am, Sm, Bm, Tm = unpack(lambda x: (asin if x[0]=='arcsin' else sqrt)(mpq(x[4][0])))
I_true = I_of(Am, Sm, Bm, Tm, pi, mpf(0), mpf(1), pi/2, mpf(0))
Lam_true = I_true / (2*pi*log(2))
e = lambda s_: 0  # placeholder
# independent check by quadrature
def gB(x):
    if x >= 1: return mpf(0)
    for i in range(NN):
        if mpq(nodes[i]) <= x <= mpq(nodes[i+1]):
            return mpq(vals[i]) + mpq(s[i])*(x - mpq(nodes[i]))
    raise ValueError
def eS(x):
    if x >= mpf(1)/2: return gB(x)
    if x >= 0: return mpf(1)/2 - x + gB(1 - x)
    return mpf(1)/2 - x
pts = sorted(set([mpf(0), pi] + [acos(mpq(a) - 1) for a in nodes] + [acos(-mpq(a)) for a in nodes]))
Iq = quad(lambda t: eS(1 + cos(t)), pts)
print("Lambda closed", Lam_true, " quadrature", Iq/(2*pi*log(2)))
assert abs(Iq - I_true) < mpf(10)**-25

# ---- certified interval: I is linear in the atoms and in π ----
zero = lambda n: [F(0)]*n
base = I_of(zero(NN), zero(NN), [None]+zero(NN-1), [None]+zero(NN-1), F(0), F(0), F(1), F(0), F(0))
def coeff(grp, j):
    A, S, B, T = zero(NN), zero(NN), [None]+zero(NN-1), [None]+zero(NN-1); PI = F(0); B1 = F(0)
    if grp == 'A': A[j] = F(1)
    if grp == 'S': S[j] = F(1)
    if grp == 'B': B[j] = F(1)
    if grp == 'T': T[j] = F(1)
    if grp == 'P': PI = F(1); B1 = F(1, 2)     # arcsin 1 = π/2
    return I_of(A, S, B, T, PI, F(0), F(1), B1, F(0)) - base
pi_lo = F('3.14159265358979323846'); pi_hi = F('3.14159265358979323847')
lg_lo = F('0.6931471803'); lg_hi = F('0.6931471808')
I_hi = base; I_lo = base
for grp, lst in (('A', A_), ('S', S_), ('B', B_), ('T', T_)):
    for idx, x in enumerate(lst):
        j = idx if grp in 'AS' else idx + 1
        cf = coeff(grp, j)
        I_hi += cf * (x[3] if cf > 0 else x[2]); I_lo += cf * (x[2] if cf > 0 else x[3])
cp = coeff('P', 0)
I_hi += cp * (pi_hi if cp > 0 else pi_lo); I_lo += cp * (pi_lo if cp > 0 else pi_hi)
UP, LOW = F('0.096816007'), F('0.096816006')
ok_up = I_hi <= UP * 2 * pi_lo * lg_lo
ok_low = LOW * 2 * pi_hi * lg_hi <= I_lo
print("I in [", float(I_lo), ",", float(I_hi), "]  upper ok", ok_up, " lower ok", ok_low)
print("slack up", float(UP*2*pi_lo*lg_lo - I_hi), " slack low", float(I_lo - LOW*2*pi_hi*lg_hi))
assert ok_up and ok_low

# ---- Lean ----
def gB_lean():
    t = f"{lean_q(vals[0])} + s0 * (σ - 1/2)"
    for i in range(1, NN): t += f"\n    + (s{i} - s{i-1}) * max 0 (σ - {lean_q(nodes[i])})"
    t += f"\n    + (0 - s{NN-1}) * max 0 (σ - 1)"
    return t
def left_rhs():
    t = f"{lean_q(vals[0])} * θh 1 1 + s0 * ((1 - 1 / 2) * θh 1 1 + 1 * sin (θh 1 1))"
    for i in range(1, NN):
        a = lean_q(nodes[i])
        t += f"\n        + (s{i} - s{i-1}) * ((1 - {a}) * θa 1 1 ({a}) + 1 * sin (θa 1 1 ({a})))"
    t += f"\n        + (0 - s{NN-1}) * ((1 - 1) * θa 1 1 1 + 1 * sin (θa 1 1 1))"
    return t
def right_rhs():
    t = "(1 / 2 - 1) * (π - θh 1 1) + 1 * sin (θh 1 1)\n        + ("
    t += f"{lean_q(vals[0])} * (π - θh 1 1) + s0 * ((1 / 2 - 1) * (π - θh 1 1) + 1 * sin (θh 1 1))"
    for i in range(1, NN):
        a = lean_q(nodes[i])
        t += f"\n        + (s{i} - s{i-1}) * ((1 - 1 - {a}) * (π - θb 1 1 ({a})) + 1 * sin (θb 1 1 ({a})))"
    t += f"\n        + (0 - s{NN-1}) * ((1 - 1 - 1) * (π - θb 1 1 1) + 1 * sin (θb 1 1 1)))"
    return t
def rw_a(kind):
    lem = 'int_max_a hR h1 h2' if kind == 'a' else 'int_max_b hR h2 h3'
    return ",\n      ".join(f"{lem} (a := {lean_q(nodes[i])}) (by norm_num) (by norm_num)" for i in range(1, NN)) \
        + f",\n      {lem} (a := 1) (by norm_num) (by norm_num)"

L = []
L.append(f'''import PaperMath.Common.TrigBounds
import PaperMath.Common.HingeIntegral
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Certified value of `Λ(𝔢_B)` (Corollary 1.2)

`𝔢_B` is the piecewise linear function through the points `(λ_j - κ_j, κ_j)`, `(κ_j, λ_j) = A^j(13/84, 55/84)`
(`0 ≤ j ≤ 7`, `A` van der Corput's process), and `(1, 0)`; `𝔢_B^*` its reflected extension (1.4).
In the proof of Theorem 1.1 the envelope functional arises as
`Λ(𝔢) = (2π log 2)⁻¹ ∫₀^π 𝔢^*(1 + cos θ) dθ`, and (1.5) is this integral after `σ = 1 + cos θ`.
The integral is computed exactly with `Common.HingeIntegral` at `c = R = 1` (`θ_h = arccos (-1/2)`), as a
combination of `π`, 15 values `arcsin y` and 15 square roots (`y` rational), each bounded to 13 decimals
(`Common.TrigBounds`); with `log 2 ∈ (0.6931471803, 0.6931471808)` this gives
`0.096816006 ≤ Λ(𝔢_B) ≤ 0.096816007` (value `0.0968160063238…`) and `2π Λ(𝔢_B) ≤ 0.60832`.
Generated by `scripts/gen_lambdaB.py`.
-/

open Real intervalIntegral Common.TrigBounds Common.HingeIntegral

namespace RvmClock.LambdaB

/-- van der Corput's `A`-process on exponent pairs. -/
noncomputable def Aproc (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / (2 * p.1 + 2), 1 / 2 + p.2 / (2 * p.1 + 2))

/-- slope on `[a, b]` -/
noncomputable def sl (a b ea eb : ℝ) : ℝ := (eb - ea) / (b - a)
''')
for i in range(NN):
    L.append(f"noncomputable def s{i} : ℝ := sl ({lean_q(nodes[i])}) ({lean_q(nodes[i+1])}) ({lean_q(vals[i])}) ({lean_q(vals[i+1])})")
L.append(f'''
/-- The Bourgain profile `𝔢_B` on `[1/2, ∞)` (constant `0` after `1`), written with hinges. -/
noncomputable def gB (σ : ℝ) : ℝ :=
  {gB_lean()}

/-- Its reflected extension `𝔢_B^*` (1.4). -/
noncomputable def eBStar (σ : ℝ) : ℝ := if σ ≤ 1 / 2 then 1 / 2 - σ + gB (1 - σ) else gB σ

lemma gB_continuous : Continuous gB := by unfold gB; fun_prop

lemma eBStar_continuous : Continuous eBStar := by
  unfold eBStar
  apply Continuous.if_le
  · exact continuous_const.sub continuous_id |>.add (gB_continuous.comp (continuous_const.sub continuous_id))
  · exact gB_continuous
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    have hx' : x = 1 / 2 := hx
    subst hx'; norm_num
''')
# nodes from the A-process and values at the nodes
for j in range(8):
    kq, lq = pairs[j]
    L.append(f'''lemma pair_{j} : Aproc^[{j}] (13 / 84, 55 / 84) = (({lean_q(kq)} : ℝ), {lean_q(lq)}) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Aproc]''' + ("\n  norm_num\n" if j > 0 else "\n"))
for j in range(NN + 1):
    L.append(f'''lemma gB_node_{j} : gB ({lean_q(nodes[j])}) = {lean_q(vals[j])} := by
  norm_num [gB, {", ".join(f"s{i}" for i in range(NN))}, sl, max_def]
''')
L.append(f'''lemma gB_one_le {{σ : ℝ}} (h : 1 ≤ σ) : gB σ = 0 := by
  unfold gB
  rw [{", ".join("max_eq_right (by linarith)" for _ in range(NN))}]
  unfold {" ".join(f"s{i}" for i in range(NN))} sl; ring

/-! ### The integral -/

lemma hR : (0 : ℝ) < 1 := one_pos
lemma h1 : (1 : ℝ) - 1 ≤ 1 / 2 := by norm_num
lemma h2 : (1 : ℝ) ≤ 1 + 1 := by norm_num
lemma h3 : (1 : ℝ) ≤ 1 := le_refl _

lemma eBStar_left {{θ : ℝ}} (hθ : θ ∈ Set.uIcc 0 (θh 1 1)) :
    eBStar (1 + 1 * cos θ) = gB (1 + 1 * cos θ) := by
  rw [Set.uIcc_of_le θh_nonneg] at hθ
  have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 θh_le_pi hθ.2
  rw [cos_θh hR h1 h2] at h
  unfold eBStar
  split_ifs with hs
  · have : 1 + 1 * cos θ = 1 / 2 := by norm_num at h hs ⊢; linarith
    rw [this]; norm_num
  · rfl

lemma eBStar_right {{θ : ℝ}} (hθ : θ ∈ Set.uIcc (θh 1 1) π) :
    eBStar (1 + 1 * cos θ) = 1 / 2 - (1 + 1 * cos θ) + gB (1 - (1 + 1 * cos θ)) := by
  rw [Set.uIcc_of_le θh_le_pi] at hθ
  have h := cos_le_cos_of_nonneg_of_le_pi θh_nonneg hθ.2 hθ.1
  rw [cos_θh hR h1 h2] at h
  unfold eBStar
  rw [if_pos (by norm_num at h ⊢; linarith)]

lemma integral_left :
    ∫ θ in (0 : ℝ)..θh 1 1, gB (1 + 1 * cos θ)
      = {left_rhs()} := by
  simp only [gB]
  rw [{", ".join("integral_add" for _ in range(NN+1))}]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_lin, {rw_a('a')}, sin_zero]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma integral_right :
    ∫ θ in θh 1 1..π, (1 / 2 - (1 + 1 * cos θ) + gB (1 - (1 + 1 * cos θ)))
      = {right_rhs()} := by
  simp only [gB]
  rw [{", ".join("integral_add" for _ in range(NN+2))}]
  · simp only [integral_const_mul, integral_const, smul_eq_mul]
    rw [integral_half, integral_lin', {rw_a('b')}, sin_pi]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- `∫₀^π 𝔢_B^*(1 + cos θ) dθ` in closed form. -/
theorem integral_eBStar_eq :
    ∫ θ in (0 : ℝ)..π, eBStar (1 + cos θ)
      = ({left_rhs()})
      + ({right_rhs()}) := by
  have hI : ∀ α β : ℝ, IntervalIntegrable (fun θ => eBStar (1 + 1 * cos θ)) MeasureTheory.volume α β :=
    fun α β => (eBStar_continuous.comp (by fun_prop)).intervalIntegrable α β
  have e1 : (fun θ => eBStar (1 + cos θ)) = fun θ => eBStar (1 + 1 * cos θ) := by
    funext θ; rw [one_mul]
  rw [e1, ← integral_add_adjacent_intervals (hI 0 (θh 1 1)) (hI (θh 1 1) π),
    integral_congr (fun θ hθ => eBStar_left hθ), integral_congr (fun θ hθ => eBStar_right hθ),
    integral_left, integral_right]

/-! ### Rational bounds for the 15 arcsines and the 15 square roots (13 decimals) -/

lemma arcsin_zero' : Real.arcsin ((1 - 1) / 1) = 0 := by norm_num
lemma sqrt_one' : Real.sqrt (1 - ((1 - 1) / 1) ^ 2) = 1 := by norm_num
lemma arcsin_one' : Real.arcsin ((1 + 1 - 1) / 1) = π / 2 := by norm_num
lemma sqrt_zero' : Real.sqrt (1 - ((1 - 1 - 1) / 1) ^ 2) = 0 := by norm_num
''')
names = []
for idx, (kind, expr, lo, hi, extra, grp) in enumerate(atoms):
    nm = f"atom{idx}"; names.append(nm)
    if kind == 'arcsin':
        y, kk = extra
        L.append(f'''lemma {nm} : ({dec(lo)} : ℝ) ≤ {expr} ∧ {expr} ≤ {dec(hi)} := by
  have hy : ({expr.split('arcsin ')[1]} : ℝ) = {y.numerator} / {y.denominator} := by norm_num
  rw [hy]
  constructor
  · apply le_arcsin_of_sin_le (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_le_partial (x := {dec(lo)}) (by norm_num) (by norm_num) {kk}
    have hs : ∑ i ∈ Finset.range (2 * {kk} + 1), (-1 : ℝ) ^ i * sinTerm {dec(lo)} i
        ≤ {y.numerator} / {y.denominator} := by
      norm_num [sinTerm, Finset.sum_range_succ, Nat.factorial]
    linarith
  · apply arcsin_le_of_le_sin (by rw [abs_le]; constructor <;> norm_num)
    have h := sin_ge_partial (x := {dec(hi)}) (by norm_num) (by norm_num) {kk}
    have hs : ({y.numerator} : ℝ) / {y.denominator}
        ≤ ∑ i ∈ Finset.range (2 * {kk}), (-1 : ℝ) ^ i * sinTerm {dec(hi)} i := by
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
obt = "\n".join(f"  obtain ⟨l{j}, u{j}⟩ := {nm}" for j, nm in enumerate(names))
prep = f'''  rw [integral_eBStar_eq]
  simp only [θh]
  simp only [sin_θa, sin_θb]
  simp only [θa_eq, θb_eq]
  rw [arcsin_zero', sqrt_one', arcsin_one', sqrt_zero']
  simp only [{", ".join(f"s{i}" for i in range(NN))}, sl]
  have hπ1 := Real.pi_gt_d20
  have hπ2 := Real.pi_lt_d20
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hpl1 : (3.14159265358979323846 : ℝ) * 0.6931471803 ≤ π * log 2 :=
    mul_le_mul hπ1.le hl1.le (by norm_num) Real.pi_pos.le
  have hpl2 : π * log 2 ≤ (3.14159265358979323847 : ℝ) * 0.6931471808 :=
    mul_le_mul hπ2.le hl2.le (Real.log_pos one_lt_two).le (by norm_num)
{obt}'''
L.append(f'''
/-- **Corollary 1.2, certified**: `Λ(𝔢_B) ≤ 0.096816007`. -/
theorem LambdaB_le :
    (∫ θ in (0 : ℝ)..π, eBStar (1 + cos θ)) / (2 * π * log 2) ≤ 0.096816007 := by
  have hpos : 0 < 2 * π * log 2 := mul_pos (mul_pos two_pos Real.pi_pos) (Real.log_pos one_lt_two)
  rw [div_le_iff₀ hpos]
{prep}
  linarith [hpl1]

/-- `Λ(𝔢_B) ≥ 0.096816006`. -/
theorem LambdaB_ge :
    0.096816006 ≤ (∫ θ in (0 : ℝ)..π, eBStar (1 + cos θ)) / (2 * π * log 2) := by
  have hpos : 0 < 2 * π * log 2 := mul_pos (mul_pos two_pos Real.pi_pos) (Real.log_pos one_lt_two)
  rw [le_div_iff₀ hpos]
{prep}
  linarith [hpl2]

/-- **Corollary 1.4(a), certified constant**: `2π Λ(𝔢_B) ≤ 0.60832`. -/
theorem two_pi_LambdaB_le :
    2 * π * ((∫ θ in (0 : ℝ)..π, eBStar (1 + cos θ)) / (2 * π * log 2)) ≤ 0.60832 := by
  have h := LambdaB_le
  have hπ := Real.pi_lt_d20
  have h0 : 0 ≤ (∫ θ in (0 : ℝ)..π, eBStar (1 + cos θ)) / (2 * π * log 2) := le_trans (by norm_num) LambdaB_ge
  have hm := mul_le_mul hπ.le h h0 (by norm_num)
  linarith

/-- The Lindelöf profile: `Λ(0) = (3√3 - π)/(12 π log 2)` (Remark 5.2), with `0^*(σ) = max (1/2 - σ) 0`. -/
theorem Lambda0_eq :
    (∫ θ in (0 : ℝ)..π, max (1 / 2 - (1 + cos θ)) 0) / (2 * π * log 2)
      = (3 * Real.sqrt 3 - π) / (12 * π * log 2) := by
  have hI : ∀ α β : ℝ, IntervalIntegrable (fun θ => max (1 / 2 - (1 + cos θ)) 0) MeasureTheory.volume α β :=
    fun α β => ((by fun_prop : Continuous fun θ : ℝ => 1 / 2 - (1 + cos θ)).max continuous_const).intervalIntegrable α β
  have e1 : ∫ θ in (0 : ℝ)..θh 1 1, max (1 / 2 - (1 + cos θ)) 0 = ∫ θ in (0 : ℝ)..θh 1 1, (0 : ℝ) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le θh_nonneg] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi hθ.1 θh_le_pi hθ.2
    rw [cos_θh hR h1 h2] at h
    dsimp only
    exact max_eq_right (by norm_num at h ⊢; linarith)
  have e2 : ∫ θ in θh 1 1..π, max (1 / 2 - (1 + cos θ)) 0 = ∫ θ in θh 1 1..π, (1 / 2 - (1 + 1 * cos θ)) := by
    apply integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le θh_le_pi] at hθ
    have h := cos_le_cos_of_nonneg_of_le_pi θh_nonneg hθ.2 hθ.1
    rw [cos_θh hR h1 h2] at h
    dsimp only
    rw [one_mul]
    exact max_eq_left (by norm_num at h ⊢; linarith)
  have hθh : θh 1 1 = 2 * π / 3 := by
    rw [θh_eq]
    have : ((1 : ℝ) - 1 / 2) / 1 = 1 / 2 := by norm_num
    rw [this, show (1 : ℝ) / 2 = sin (π / 6) by rw [Real.sin_pi_div_six],
      Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    ring
  have hs : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [← integral_add_adjacent_intervals (hI 0 (θh 1 1)) (hI (θh 1 1) π), e1, e2, integral_zero,
    integral_half, hθh, sin_pi, hs]
  have hl := Real.log_pos one_lt_two
  have hp := Real.pi_pos
  field_simp
  ring

end RvmClock.LambdaB
''')
open('/home/claude/papermath/PaperMath/Papers/RvmClock/LambdaB.lean', 'w').write('\n'.join(L))
print("written; atoms:", len(atoms))
