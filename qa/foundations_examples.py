"""Recomputes every number in the worked examples added to the primers and Modules 2-3 on 2026-10-01.

Run: python3 qa/foundations_examples.py   (an AssertionError means the page and the math disagree)
"""
import math

import numpy as np


def close(a, b, tol=5e-4):
    assert abs(a - b) <= tol * max(1.0, abs(b)), (a, b)


# ---------- Primer B, KKT ----------
f0 = lambda x: (x[0] - 2) ** 2 + (x[1] - 1) ** 2
grad_f0 = lambda x: np.array([2 * (x[0] - 2), 2 * (x[1] - 1)])
g = np.linspace(-1, 3, 801)
X1, X2 = np.meshgrid(g, g)
F = (X1 - 2) ** 2 + (X2 - 1) ** 2


def grid_min(mask):
    i = np.argmin(np.where(mask, F, np.inf))
    return np.array([X1.flat[i], X2.flat[i]]), F.flat[i]


# Example 1: s.t. x1 + x2 <= 1  ->  x* = (1, 0), lambda = 2, cost 2
xs, val = grid_min(X1 + X2 <= 1 + 1e-12)
assert np.allclose(xs, [1, 0], atol=0.01) and abs(val - 2) < 0.02
x = np.array([1.0, 0.0]); lam = 2.0
assert np.allclose(grad_f0(x) + lam * np.array([1, 1]), 0) and x.sum() - 1 == 0
cost = lambda b: (3 - b) ** 2 / 2          # optimal cost with budget x1 + x2 <= b, b <= 3
close(cost(1), 2); close((cost(1 + 1e-6) - cost(1)) / 1e-6, -2, 1e-5)

# Example 2: add x1 <= 0.5  ->  x* = (0.5, 0.5), lambda = (1, 2), cost 2.5
xs, val = grid_min((X1 + X2 <= 1 + 1e-12) & (X1 <= 0.5 + 1e-12))
assert np.allclose(xs, [0.5, 0.5], atol=0.01) and abs(val - 2.5) < 0.02
x = np.array([0.5, 0.5]); l1, l2 = 1.0, 2.0
assert np.allclose(grad_f0(x) + l1 * np.array([1, 1]) + l2 * np.array([1, 0]), 0)
assert f0(np.array([1, 0])) == 2 and 1 - 0.5 > 0           # candidate {1} violates x1 <= 0.5
assert 0.5 + 1 - 1 > 0                                       # candidate {2}: (0.5, 1) violates x1 + x2 <= 1
e = 1e-6                                                     # prices: relax each constraint by e
close((f0(np.array([0.5 + e, 0.5 - e])) - 2.5) / e, -2, 1e-4)
close((f0(np.array([0.5, 0.5 + e])) - 2.5) / e, -1, 1e-4)

# Example 3: wrong guess with x2 >= -1 also active: x = (2, -1) gives lambda2 = -4
x = np.array([2.0, -1.0])
A = np.array([[1, 0], [1, -1]])                              # columns: grad f1 = (1,1), grad f2 = (0,-1)
lam = np.linalg.solve(A, -grad_f0(x))
assert np.allclose(lam, [0, -4])

# Non-convex: min -x^2 on [-1, 1]: KKT points 0 (lambda = 0), 1 (lambda1 = 2), -1 (lambda2 = 2)
fp = lambda x: -2 * x
assert fp(0) == 0 and fp(1) + 2 * 1 == 0 and fp(-1) + 2 * (-1) == 0

# Approximate KKT from the log barrier: x*(t) = (3 - sqrt(1 + 2/t))/2, lambda = 1/(t(1 - x))
for t, xexp, lexp in ((10, 0.9523, 2.0954), (100, 0.9950, 2.0100)):
    xt = (3 - math.sqrt(1 + 2 / t)) / 2
    lt = 1 / (t * (1 - xt))
    close(xt, xexp); close(lt, lexp)
    close(2 * (xt - 2) + lt, 0, 1e-9)                        # stationarity residual is zero
    close(lt * (1 - xt), 1 / t, 1e-9)                        # complementary slackness residual is 1/t

print("Primer B KKT examples check out")


# ---------- Module 2 ----------
# s1 duality: min (x1-2)^2 + (x2-1)^2 s.t. x1 + x2 <= 1: g(lam) = 2 lam - lam^2/2, max at lam = 2 with g = 2 = p*
gfun = lambda lam: 2 * lam - lam**2 / 2
for lam in (0.0, 1.0, 2.0, 3.0):
    x = np.array([2 - lam / 2, 1 - lam / 2])                 # minimiser of the Lagrangian
    close(f0(x) + lam * (x.sum() - 1), gfun(lam), 1e-12)
    assert gfun(lam) <= 2 + 1e-12                            # weak duality
close(gfun(1), 1.5); close(gfun(2), 2); close(gfun(3), 1.5)
# s1 duality gap with a 0/1 variable: min x s.t. 0.5 - x <= 0 over {0, 1}: p* = 1, g(lam) = min(0.5 lam, 1 - 0.5 lam), d* = 0.5
gd = lambda lam: min(lam * 0.5, 1 + lam * (0.5 - 1))
lams = np.linspace(0, 4, 4001)
close(max(gd(l) for l in lams), 0.5); close(lams[np.argmax([gd(l) for l in lams])], 1.0, 1e-3)

# s2 LMI [[x,1],[1,y]] >= 0  <=>  x >= 0, y >= 0, xy >= 1  (spot checks)
psd = lambda M: np.linalg.eigvalsh(M).min() >= -1e-12
assert psd(np.array([[2, 1], [1, 0.5]])) and psd(np.array([[1, 1], [1, 1]])) and not psd(np.array([[2, 1], [1, 0.4]]))
assert psd(np.array([[0.5, 1], [1, 3]])) and not psd(np.array([[-1, 1], [1, -1]]))
# s2 discrete Lyapunov LMI: A = [[0.5, 1], [0, 0.5]] is Schur stable, P = I fails, the Stein solution P works
A = np.array([[0.5, 1.0], [0.0, 0.5]])
assert max(abs(np.linalg.eigvals(A))) == 0.5
assert np.linalg.eigvalsh(A.T @ A - np.eye(2)).max() > 0          # P = I is not a certificate
P = np.linalg.solve(np.kron(A.T, A.T) - np.eye(4), -np.eye(2).reshape(-1)).reshape(2, 2)   # A^T P A - P = -I
P = (P + P.T) / 2
assert np.allclose(A.T @ P @ A - P, -np.eye(2)) and np.linalg.eigvalsh(P).min() > 0
print("Stein P =", np.round(P, 4).tolist(), "eig", np.round(np.linalg.eigvalsh(P), 4).tolist())
x0 = np.array([0.0, 1.0]); x1 = A @ x0
close(np.linalg.norm(x1), math.sqrt(1.25)); assert np.linalg.norm(x1) > np.linalg.norm(x0)
V = lambda x: x @ P @ x
print("V(x0), V(x1), ||x0||, ||x1|| =", round(V(x0), 4), round(V(x1), 4), 1.0, round(float(np.linalg.norm(x1)), 4))
assert V(x1) < V(x0)

# s3 Schur complement: M = [[2, 1], [1, 1]] > 0 since 2 > 0 and 1 - 1/2 = 0.5 > 0; eigenvalues (3 +- sqrt 5)/2
M = np.array([[2.0, 1.0], [1.0, 1.0]])
assert np.allclose(sorted(np.linalg.eigvalsh(M)), sorted([(3 - math.sqrt(5)) / 2, (3 + math.sqrt(5)) / 2]))
close(1 - 1 / 2, 0.5)
# ||x||^2 <= t  <=>  [[t, x^T], [x, I]] >= 0 ; x = (3, 4): boundary at t = 25
for t, ok in ((25, True), (26, True), (24, False)):
    Mx = np.block([[np.array([[t]]), np.array([[3.0, 4.0]])], [np.array([[3.0], [4.0]]), np.eye(2)]])
    assert psd(Mx) == ok

# s4 S-lemma: x^2 <= 1  =>  2 - x - x^2 >= 0 ; certificate tau = 1.5 gives 0.5 (x - 1)^2, and no other tau works
xs_ = np.linspace(-5, 5, 2001)
assert np.allclose((2 - xs_ - xs_**2) - 1.5 * (1 - xs_**2), 0.5 * (xs_ - 1) ** 2)
for tau in (1.4, 1.6, 1.0, 2.0):
    assert ((2 - xs_ - xs_**2) - tau * (1 - xs_**2)).min() < 0

# s5 one-neuron Lipschitz bound via the QC 2 lam dz (w1 dx - dz) >= 0: optimum lam = w2^2 = 9 gives L = |w1 w2| = 6
w1, w2 = 2.0, 3.0
def Lsq(lam):                                                # smallest L^2 with [[L^2, -lam w1], [-lam w1, 2 lam - w2^2]] >= 0
    return (lam * w1) ** 2 / (2 * lam - w2**2)
lam_grid = np.linspace(4.6, 40, 200001)
i = np.argmin([Lsq(l) for l in lam_grid])
close(lam_grid[i], 9.0, 1e-3); close(math.sqrt(Lsq(9.0)), 6.0, 1e-12)
Mq = np.array([[36.0, -18.0], [-18.0, 9.0]])
assert np.allclose(sorted(np.linalg.eigvalsh(Mq)), [0, 45])
close(math.sqrt(Lsq(12.0)), math.sqrt(144 * 4 / 15), 1e-12)   # a non-optimal multiplier gives a valid but larger bound
print("L at lam=12:", round(math.sqrt(Lsq(12.0)), 3))

# s6 dissipativity: x+ = 0.5 x + w, z = x, V = p x^2, supply gamma^2 w^2 - z^2 ; p = 2 gives gamma = 2 = H-inf norm
def gamma_sq(p):
    return p + p**2 / (3 * p - 4)
pg = np.linspace(1.34, 10, 200001)
j = np.argmin([gamma_sq(p) for p in pg])
close(pg[j], 2.0, 1e-3); close(gamma_sq(2.0), 4.0, 1e-12)
Md = np.array([[1 - 0.75 * 2, 2 / 2], [2 / 2, 2 - 4]])
assert np.linalg.eigvalsh(Md).max() <= 1e-12
w = np.linspace(0, math.pi, 10001)
close(max(1 / abs(np.exp(1j * w) - 0.5)), 2.0, 1e-6)     # |G(e^{jw})| = 1/|e^{jw} - 0.5| peaks at w = 0
print("Module 2 examples check out")

# ---------- Module 3 ----------
k = lambda a, b: math.exp(-((a - b) ** 2) / 2)
Kmat = lambda pts: np.array([[k(a, b) for b in pts] for a in pts])
K3 = Kmat([0, 1, 2])
print("Gram(0,1,2) =", np.round(K3, 4).tolist(), "eig", np.round(np.linalg.eigvalsh(K3), 4).tolist())
c = np.array([1, -2, 1]); print("c^T K c for c=(1,-2,1):", round(float(c @ K3 @ c), 4))
assert np.linalg.eigvalsh(K3).min() > 0
# minimum-norm interpolant of +1 at 0 and -1 at d: norm^2 = 2/(1 - k(0,d))
for d_, nexp in ((1.0, 2.2546), (0.1, 20.025)):
    Kd = Kmat([0, d_]); y = np.array([1.0, -1.0])
    n2 = y @ np.linalg.solve(Kd, y)
    close(n2, 2 / (1 - k(0, d_)), 1e-9); close(math.sqrt(n2), nexp, 2e-3)
    dk = math.sqrt(2 * (1 - k(0, d_)))
    close(2 / dk, math.sqrt(n2), 1e-9)                       # the Lipschitz-lemma lower bound is attained
print("norms:", round(math.sqrt(2 / (1 - k(0, 1))), 3), round(math.sqrt(2 / (1 - k(0, 0.1))), 3))

# GP regression with data x = (0, 1), y = (1, 0.5), lambda = 0.01
X = [0.0, 1.0]; Y = np.array([1.0, 0.5]); lam = 0.01
Kt = Kmat(X) + lam * np.eye(2)
def post(x):
    kt = np.array([k(x, a) for a in X])
    return float(kt @ np.linalg.solve(Kt, Y)), math.sqrt(max(0.0, 1 - kt @ np.linalg.solve(Kt, kt)))
for xq in (0.0, 0.5, 3.0):
    m_, s_ = post(xq); print(f"GP at {xq}: mean {m_:.4f}, std {s_:.4f}")
m05, s05 = post(0.5); m3, s3 = post(3.0); m0, s0 = post(0.0)
close(m05, 0.8189, 2e-3); close(s05, 0.1909, 2e-3); close(m3, -0.0090, 0.05); close(s3, 0.9870, 2e-3); close(m0, 0.9892, 2e-3); close(s0, 0.0992, 2e-3)

# noise-free power function at 0.5 and 3 for data at 0 and 1
def P_nf(x):
    kt = np.array([k(x, a) for a in X]); return math.sqrt(max(0.0, 1 - kt @ np.linalg.solve(Kmat(X), kt)))
close(P_nf(0.5), 0.1745); print("power function at 3:", round(P_nf(3.0), 4)); close(P_nf(3.0), 0.9868, 2e-3)

# information gain with lambda = 0.01
ig = lambda pts: 0.5 * math.log(np.linalg.det(np.eye(len(pts)) + Kmat(pts) / 0.01))
close(ig([0]), 0.5 * math.log(101)); close(ig([0, 0]), 0.5 * math.log(201), 1e-6)
close(ig([0, 0.1]), 0.5 * (math.log(1 + 100 * (1 + k(0, 0.1))) + math.log(1 + 100 * (1 - k(0, 0.1)))), 1e-6)
close(ig([0, 5]), math.log(101), 1e-4)
print("info gain: one", round(ig([0]), 3), "same point twice", round(ig([0, 0]), 3), "0.1 apart", round(ig([0, 0.1]), 3), "far apart", round(ig([0, 5]), 3))
# sequential form for the repeated point: 1/2 [log(1 + 1/lam) + log(1 + s1^2/lam)] with s1^2 = 1 - 1/(1 + lam)
s1 = 1 - 1 / (1 + 0.01); close(0.5 * (math.log(1 + 100) + math.log(1 + s1 / 0.01)), ig([0, 0]), 1e-9)

# confidence band (all-time form): beta = B + (R/sqrt(lam)) sqrt(2 gamma + 2 ln(1/delta))
gamma1 = 0.5 * math.log(1 + 1 / 0.01)
beta = lambda B, R, lam_, gam, dl: B + R / math.sqrt(lam_) * math.sqrt(2 * gam + 2 * math.log(1 / dl))
b1 = beta(1, 0.1, 0.01, gamma1, 0.01); b2 = beta(1, 0.1, 0.01, gamma1, 0.001)
print("beta_2 with delta 0.01 / 0.001:", round(b1, 3), round(b2, 3))
close(b1, 4.72, 2e-3); close(b2, 5.29, 2e-3)
print("Module 3 examples check out")

# after review (2026-10-01): boundary cases and rounding
close(-4 * 4.5**2, -81, 1e-12)                                  # QC example: lambda = 9/2 has determinant -4 lambda^2 < 0
close((1 - 0.75 * 4 / 3) * (4 / 3 - 4) - (4 / 3) ** 2 / 4, -4 / 9, 1e-12)   # dissipativity: p = 4/3 has determinant -4/9
close(0.5 * math.log(201 / 101), 0.344, 2e-3)                   # information gain of the repeated measurement
assert math.cosh(0.7 * 1.0) <= math.exp(0.7**2 * 1.0**2 / 2)    # +-R noise is R-sub-Gaussian (cosh(aR) <= exp(a^2 R^2 / 2))
print("review fixes check out")
