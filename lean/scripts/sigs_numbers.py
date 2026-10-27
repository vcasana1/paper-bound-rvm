# Numerical design of the bound log zeta(sigma#) <= 1.52499 (exact rationals; mpmath only for reference)
from fractions import Fraction as F
from mpmath import mp, mpf, zeta, log, exp
import math
mp.dps = 40
cc = F(1000002, 1000000); RR = F(1000005, 1000000)
sigS = cc + (cc - F(1,2))**2 / RR
eps = sigS - F(5,4)
print("sigS =", sigS, float(sigS)); print("eps  =", eps, float(eps))
L2 = F(6931471803, 10**10)   # Real.log_two_gt_d9
N = 50
def floor_log2(n): return int(math.floor(math.log2(n)))
def rat_pow_root_upper(x, p, r, digits):
    # smallest decimal q with `digits` decimals such that 1 <= q^r * x^p
    v = mpf(x.numerator)/mpf(x.denominator)
    q0 = v**(-mpf(p)/r)
    scale = F(10)**digits
    q = F(math.floor(q0*scale)+1, 1)/scale
    while q**r * x**p < 1: q += F(1,1)/scale
    while (q - F(1,1)/scale)**r * x**p >= 1: q -= F(1,1)/scale
    return q
lines = []; total = F(1)  # n = 1
digits = 12
for n in range(2, N):
    x = F(n); k = floor_log2(n)
    q1 = rat_pow_root_upper(x, 5, 4, digits)
    L = k*L2 + (1 - F(2)**k / x)
    qexact = q1 / (1 + eps*L)
    scale = F(10)**digits
    q = F(math.floor(qexact*scale)+1, 1)/scale
    assert q1 <= q*(1+eps*L)
    total += q
    lines.append((n, k, q1, q))
# tail
x = F(99,2); k = 5
qt1 = rat_pow_root_upper(x, 1, 4, digits)
L = k*L2 + (1 - F(2)**k/x)
qt_exact = qt1/(1+eps*L); scale = F(10)**digits
qt = F(math.floor(qt_exact*scale)+1,1)/scale
assert qt1 <= qt*(1+eps*L)
tail = qt / (sigS - 1)
Z = total + tail
print("partial", float(total), "tail", float(tail), "Z", float(Z))
true = zeta(mpf(sigS.numerator)/sigS.denominator)
print("true zeta", true, "excess", float(Z) - float(true))
print("log Z", log(mpf(Z.numerator)/Z.denominator), "target 1.52499")
# log Z via Z = 8 (1 - x)
xq = 1 - Z/8
print("x =", float(xq))
n = 36
s = sum(xq**(i+1)/(i+1) for i in range(n)); rem = xq**(n+1)/(1-xq)
L2u = F(6931471808, 10**10)
logZ_up = 3*L2u + (-s + rem)
print("logZ upper", float(logZ_up), "ok" if logZ_up <= F(152499,100000) else "FAIL")
import json
json.dump({"eps": [eps.numerator, eps.denominator], "sigS":[sigS.numerator, sigS.denominator],
           "lines": [(n,k,str(q1),str(q)) for n,k,q1,q in lines], "qt1": str(qt1), "qt": str(qt),
           "Z": [Z.numerator, Z.denominator], "x": [xq.numerator, xq.denominator], "n_taylor": n,
           "sum_upper": str(-s+rem)}, open('/home/claude/lean/gen/sigs_numbers.json','w'))
def dec(q):  # exact decimal string of a rational with denominator 10^k
    s = str(q.numerator).rjust(digits+1,'0'); return s[:-digits] + '.' + s[-digits:]
print(dec(lines[0][3]), dec(qt))
