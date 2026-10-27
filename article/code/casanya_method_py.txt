# casanya_method.py -- Casana's method (Section 7.1 of the article rvm_clock_envelope): the k-th ordinate of a
# zero of zeta is approximated by the sublevel measure
#     x_k = |{t > 0 : F(t) < k - 1/2}|,   F = N_0 + Phi,
# where N_0(t) = (t/2pi) log(t/(2 pi e)) + 7/8 is the Riemann-von Mangoldt main term and Phi is the finite Euler
# phase (1.10)-(1.11): on the dyadic block 2^j <= t <= 2^{j+1}, Phi interpolates linearly between Phi_{m_j} and
# Phi_{m_{j+1}}, m_j = floor(2^{j/2}), Phi_m(t) = -(1/pi) sum_{nu<=m} arg(1 - p_nu^{-1/2-it}) (principal argument).
# This program evaluates x_k on a grid (step h) for k <= K and compares it with the ordinate gamma_k (mpmath) and
# with the bare clock tau_k, N_0(tau_k) = k - 1/2.  Illustration only: the article proves a mean-square bound
# (Theorem 1.5), not a bound for each k.  Python 3.13.17, numpy, mpmath 1.4.1.
import numpy as np
from mpmath import mp, zetazero, lambertw, mpf, exp, pi as mpi

K, TMAX, H = 20, 120.0, 0.001
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

def N0(t):
    return t / (2 * np.pi) * np.log(t / (2 * np.pi * np.e)) + 7 / 8

def phi_m(m, t):
    """Phi_m(t) = -(1/pi) sum_{nu<=m} arg(1 - p_nu^{-1/2-it})."""
    s = np.zeros_like(t)
    for p in primes[:m]:
        z = p ** (-0.5) * np.exp(-1j * t * np.log(p))
        s -= np.angle(1 - z)
    return s / np.pi

def F(t):
    j = np.floor(np.log2(t)).astype(int)              # block index: 2^j <= t < 2^{j+1}
    out = np.empty_like(t)
    for jj in np.unique(j):
        sel = j == jj
        tt = t[sel]
        mj, mj1 = int(np.floor(2 ** (jj / 2))), int(np.floor(2 ** ((jj + 1) / 2)))
        lam = tt / 2.0 ** jj - 1                       # 0 at 2^j, 1 at 2^{j+1}
        out[sel] = N0(tt) + (1 - lam) * phi_m(mj, tt) + lam * phi_m(mj1, tt)
    return out

def tau(k):
    """Bare clock: N_0(tau_k) = k - 1/2, by Lambert's W (equation (1.9))."""
    a = (k - mpf(1) / 2 - mpf(7) / 8)
    return 2 * mpi * a / lambertw(a / exp(1))

t = np.arange(H / 2, TMAX, H)                         # midpoints of the grid cells (0, TMAX]
Ft = F(t)
assert Ft[-1] > K - 0.5 + 2, "TMAX too small"
print('Casana method: x_k = |{t > 0 : N_0(t) + Phi(t) < k - 1/2}|, grid step h = %g on (0, %g]' % (H, TMAX))
print('%3s %12s %12s %12s %12s %12s' % ('k', 'x_k', 'gamma_k', 'x_k-gamma_k', 'tau_k', 'tau_k-gamma_k'))
mp.dps = 15
for k in range(1, K + 1):
    xk = H * np.count_nonzero(Ft < k - 0.5)
    gk = float(zetazero(k).imag)
    tk = float(tau(k))
    print('%3d %12.4f %12.4f %12.4f %12.4f %12.4f' % (k, xk, gk, xk - gk, tk, tk - gk))
