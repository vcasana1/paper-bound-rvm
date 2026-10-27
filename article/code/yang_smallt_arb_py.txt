# yang_smallt_arb.py -- certificate for Remark 4.5(ii) of the article rvm_clock_envelope (Appendix A).
# Python 3.13.17, python-flint 0.9.0 (Arb ball arithmetic, 120 bits, outward rounding).
# Rigorous redo of Yang (JMAA 534 (2024) 128124), Sec. 3.1, eqs. (3.9)-(3.13), for 4<=k<=9,
# with |Log(Q0+s)| = rho(s)*log|Q0+s| in the Phragmen-Lindelof conclusion (Fiori Cor.3 / Trudgian Lemma 3),
# A(t0) as printed in (3.12), t0 on a partition of [3, T_k].  On a piece t in [e^a, e^b], t0=e^a:
#   |zeta(sigma_k+it)| <= 0.618^{k/(K-1)} * rho_max(piece) * A(e^a) * t^{(1-sigma_k)/3} log t
#                     <= C_piece * t^{1/(2K-2)} log t,  C_piece = 0.618^{k/(K-1)} rho_max A(e^a) e^{b(k-3)/(6K-6)}.
from flint import arb, ctx
ctx.prec = 120
Q0 = arb('1.31'); c231 = arb('2.31')**2
def A(u):            # (3.12) with t0 = e^u
    q = c231*(-2*u).exp()
    return (q+1)**(arb(23)/42) * (1 + (q+1).log()/(2*u))
def rho(u0, u1, sk): # max of |Log(Q0+s)|/log|Q0+s| for s = sk+it, t in [e^u0, e^u1]
    t = u0.exp().union(u1.exp()); x = Q0 + sk
    L = (x*x + t*t).log()/2; Ar = (t/x).atan()
    return (1 + (Ar/L)**2).sqrt()
out = []
for k in range(4, 10):
    K = 2**(k-1); sk = 1 - arb(k)/(2*K-2)
    uT = (arb('2.6134')*(K-1) + arb('2.8876')*k)/(k-3)
    base = arb('0.618')**(arb(k)/(K-1)); ex = arb(k-3)/(6*K-6)
    a = arb(3).log(); worst = arb(0); n = 0
    while (a < uT):
        b = a + arb('0.002')*(1 + a/10)
        if b > uT: b = uT
        C = base*rho(a, b, sk)*A(a)*(b*ex).exp()
        if C.upper() > worst.upper(): worst = C
        a = b; n += 1
    out.append((k, float(uT.upper()), n, float(worst.upper())))
    print('k=%d  T_k=exp(%.3f)  pieces=%d  constant on [3,T_k] <= %.5f' % out[-1])
m = max(o[3] for o in out)
print('max over 4<=k<=9: %.5f  (<= 2: %s); for t>=T_k Yang Sec.3.2 gives 1.546' % (m, m <= 2))
