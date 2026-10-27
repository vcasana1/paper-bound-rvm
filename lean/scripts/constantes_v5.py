# constantes_v5.py -- constants of the article rvm_clock_envelope (Appendix A).
# Bourgain profile (Theorem 1.1, Corollary 1.2) and explicit profile (Theorem 1.3): the angular integrals by
# quadrature and by the closed form (5.3), the constants C_1, C_2, log(zeta(c)/zeta(2c)), log zeta(sigma#),
# C_3(100) as defined in Section 5.3 (with the costs 2C_1/T and 2C_2/(T log T)) and the same sum with the exact
# differences, Lambda(0), and the crossing points with Bellotti-Wong (1.7) and with Yang's (4.29).
# Python 3.13.17, mpmath 1.4.1, 40 decimal digits.
import sys, mpmath
from mpmath import mp, mpf, quad, sqrt, log, pi, acos, cos, sin, zeta, nstr
mp.dps = 40
print('Python', sys.version.split()[0], ' mpmath', mpmath.__version__, ' mp.dps =', mp.dps)

def closed_form(nodes, c, R):
    """int_0^pi e*(c+R cos th) dth by the hinge formulas (5.3): nodes (sigma_i, e_i), sigma_0 = 1/2 < ... < sigma_n = 1"""
    n = len(nodes)-1
    xs = [a for a,_ in nodes]; es = [b for _,b in nodes]
    s = [(es[i+1]-es[i])/(xs[i+1]-xs[i]) for i in range(n)]            # slopes
    hinges = [(xs[i], s[i]-s[i-1]) for i in range(1,n)] + [(mpf(1), -s[n-1])]
    th_h = acos((mpf(1)/2 - c)/R)                                       # sigma = 1/2
    e0, s0 = es[0], s[0]
    I = (e0 + s0*(c-mpf(1)/2))*th_h + s0*R*sin(th_h)                    # linear part, sigma >= 1/2
    I += ((1+s0)*(mpf(1)/2-c) + e0)*(pi-th_h) + (1+s0)*R*sin(th_h)      # linear part of 1/2-sigma+e(1-sigma), sigma <= 1/2
    for a, coef in hinges:
        th_a = acos((a-c)/R);   I += coef*((c-a)*th_a + R*sin(th_a))          # int_0^th_h max(0, sigma-a)
        th_b = acos((1-a-c)/R); I += coef*((1-c-a)*(pi-th_b) + R*sin(th_b))   # int_th_h^pi max(0, 1-sigma-a)
    return I

def pl(nodes):
    """piecewise linear function through the nodes (sigma, e), increasing sigma, 0 to the right of the last node"""
    def e(s):
        if s >= nodes[-1][0]: return mpf(0)
        for (a,ea),(b,eb) in zip(nodes, nodes[1:]):
            if a <= s <= b: return ea + (eb-ea)*(s-a)/(b-a)
        raise ValueError(s)
    return e

def reflect(e):
    """reflected extension (1.4)"""
    def es(s):
        s = mpf(s)
        if s >= 1: return mpf(0)
        if s >= mpf(1)/2: return e(s)
        if s >= 0: return mpf(1)/2 - s + e(1-s)
        return mpf(1)/2 - s
    return es

# --- Corollary 1.2: Bourgain profile via the A-process ---
k, l = mpf(13)/84, mpf(55)/84
nodesB = []
for j in range(8):
    nodesB.append((l-k, k)); k, l = k/(2*k+2), mpf(1)/2 + l/(2*k+2)
nodesB.append((mpf(1), mpf(0)))
from fractions import Fraction as Fr
kf, lf = Fr(13,84), Fr(55,84); nf=[]
for j in range(8):
    nf.append((lf-kf, kf)); kf, lf = kf/(2*kf+2), Fr(1,2)+lf/(2*kf+2)
print('Bourgain nodes (1.6):', [(str(a),str(b)) for a,b in nf])
eB = reflect(pl(nodesB))
brk = sorted(set([mpf(0)]+[1-a for a,_ in nodesB]+[a for a,_ in nodesB]+[mpf(1)/2]))
brk = [b for b in brk if 0 <= b <= 1]
A = quad(lambda s: eB(s)/sqrt(s*(2-s)), brk) / (2*pi*log(2))
print('Cor 1.2: Lambda(e_B) =', nstr(A, 20), ' Cor 1.4(a): 2*pi*Lambda(e_B) =', nstr(2*pi*A, 20))
AB_closed = closed_form(nodesB, mpf(1), mpf(1))/(2*pi*log(2))
print('Cor 1.2 by the closed form (5.3) with c = R = 1: Lambda(e_B) =', nstr(AB_closed, 20))
assert abs(AB_closed - A) < mpf(10)**-20   # the sigma-quadrature has an integrable singularity at 0

# --- Theorem 1.3: explicit profile (4.3), constants (5.4) ---
nodesE = [(mpf(1)/2, mpf(27)/164)] + [(1 - mpf(m)/(2**m-2), mpf(1)/(2**m-2)) for m in range(4,10)] + [(mpf(1), mpf(0))]
print('explicit nodes (4.3):', [(nstr(a,8), nstr(b,8)) for a,b in nodesE])
eE = reflect(pl(nodesE))
c, R = mpf('1.000002'), mpf('1.000005')
sig1 = c + (c-mpf(1)/2)**2/R; delta = 2*c - sig1 - mpf(1)/2
D = log(R/(c-mpf(1)/2))
print('sigma1 =', nstr(sig1,15), ' delta =', nstr(delta,15), ' c-R =', nstr(c-R,5), ' D =', nstr(D,20))
# integral I = int_0^pi eE(c+R cos th) dth, split at the angles of the nodes
pts = set([mpf(0), pi])
for a,_ in nodesE + [(1-a,0) for a,_ in nodesE] + [(mpf(0),0)]:
    x = (a - c)/R
    if -1 < x < 1: pts.add(acos(x))
pts = sorted(pts)
I = quad(lambda th: eE(c + R*cos(th)), pts)
C1 = I/(2*pi*D); C2 = 1/(2*D)
print('I =', nstr(I,25)); print('C1 = I/(2 pi D) =', nstr(C1,25)); print('C2 = 1/(2D) =', nstr(C2,25))
I_closed = closed_form(nodesE, c, R)
print('I by the closed form (5.3) =', nstr(I_closed,25), ' C1 =', nstr(I_closed/(2*pi*D),25))
assert abs(I_closed - I) < mpf(10)**-25
print('log zeta(sigma1) =', nstr(log(zeta(sig1)),15), ' zeta(c) <=', nstr(c/(c-1),10), ' zeta(c)/zeta(2c)=', nstr(zeta(c)/zeta(2*c),12))

# --- Lemmas 4.3-4.4 and the constant term C_3(100) of Section 5.3 ---
t0 = mpf(98)
eps_chi = (mpf(1)/3 + mpf('2.0005')/6)/t0 + mpf('0.87')/t0**2   # |R1|+|R2| + |phi1|+|phi2|
chi_fac = mp.e**eps_chi
K1 = 2*(1+mpf('84.5')/t0**2)**(1+mpf(27)/164) * (1 + (mpf('84.5')/t0**2 + pi/2)/log(t0))
K = chi_fac*K1
print('factor chi <=', nstr(chi_fac,8), '  K1 <=', nstr(K1,8), '  K = chi*K1 <=', nstr(K,8))
Kr = mpf('2.74'); assert K <= Kr and K1 <= Kr
T = mpf(100)
lzr = log(zeta(c)/zeta(2*c))
Eterm = ((640*delta-112)/(1536*(3*T-1)) + mpf(2)**-10)/2     # E/(2 pi)
C3base = C2*(lzr + log(1+3/T) + log(Kr)) + (log(zeta(sig1)) + (sig1-mpf(1)/2)/T)/pi + Eterm + mpf(1)/4
C3T = C3base + 2*C1/T + 2*C2/(T*log(T))                                   # C_3(T) of Section 5.3
C3exact = C3base + C1*(log(T+2)-log(T)) + C2*(log(log(T+2))-log(log(T)))  # same sum, exact differences
print('log(zeta(c)/zeta(2c)) =', nstr(lzr,12), ' E/(2pi) <=', nstr(Eterm,8))
print('C_3(100) =', nstr(C3T,12), ' (with the costs 2C_1/T + 2C_2/(T log T));  with exact differences:', nstr(C3exact,12))
print('Lemma 4.1: 1/16+1/8+1/3 =', nstr(mpf(1)/16+mpf(1)/8+mpf(1)/3,8))
print('Cor 1.4(a): 2*pi*0.0968160064 =', nstr(2*pi*mpf('0.0968160064'),10))

# --- Remark 5.2: Lindelof profile (e=0 on [1/2,1]) ---
eL = reflect(lambda s: mpf(0))
AL = quad(lambda s: eL(s)/sqrt(s*(2-s)), [0, mpf(1)/2, 1])/(2*pi*log(2))
print('Lindelof: a_L =', nstr(AL,12), ' 2pi a_L =', nstr(2*pi*AL,12))
# --- crossing with Bellotti-Wong for S(T): 0.10076 L + min(0.24460 LL + 7.20844, 1.68845 LL + 1.50956) ---
from mpmath import findroot
def diff(L):
    L = mpf(L); BW = mpf('0.10076')*L + min(mpf('0.24460')*log(L)+mpf('7.20844'), mpf('1.68845')*log(L)+mpf('1.50956'))
    ours = mpf('0.09783')*L + mpf('0.7214')*log(L) + mpf('10.6')
    return ours - BW
lo, hi = mpf(10), mpf(10**6)
for _ in range(200):
    mid = (lo+hi)/2
    if diff(mid) > 0: lo = mid
    else: hi = mid
print('crossing: (1.7) < Bellotti-Wong for log T >', nstr(hi,8))
# --- crossing with Yang's (4.29): |N - N_0| <= 0.11 log t + 0.29 log log t + 2.29 + 0.2/t_0 (t >= t_0 >= e) ---
yang = lambda L: mpf('0.11')*L + mpf('0.29')*log(L) + mpf('2.29') - (mpf('0.09783')*L + mpf('0.7214')*log(L) + mpf('10.7'))
print('crossing: (1.8) < Yang (4.29) (without the term 0.2/t_0) for log t >', nstr(findroot(yang, 933),8))

# --- Remark: Bellotti-Wong left profile (linear on [0,1/2]) with c,R -> 1 ---
eR = pl(nodesE)
def eBWl(s):
    s = mpf(s)
    if s >= 1: return mpf(0)
    if s >= mpf(1)/2: return eR(s)
    if s >= 0: return mpf(1)/2 - s + 2*s*mpf(27)/164
    return mpf(1)/2 - s
brkE = sorted(set([mpf(0), mpf(1)/2, mpf(1)] + [a for a,_ in nodesE] + [1-a for a,_ in nodesE]))
ABW = quad(lambda s: eBWl(s)/sqrt(s*(2-s)), [b for b in brkE if 0 <= b <= 1])/(2*pi*log(2))
AEr = quad(lambda s: eE(s)/sqrt(s*(2-s)), [b for b in brkE if 0 <= b <= 1])/(2*pi*log(2))
print('limit c,R->1: BW linear-left profile =', nstr(ABW,10), ' reflected explicit profile =', nstr(AEr,10))
