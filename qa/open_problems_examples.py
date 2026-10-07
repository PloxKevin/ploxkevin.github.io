"""Recomputes every number used in the worked examples of SafeLearning/open-problems.html.

Run: python3 qa/open_problems_examples.py   (prints each value; an AssertionError means the page and the math disagree)
"""
import math
from statistics import NormalDist

import numpy as np


def close(a, b, tol=5e-4):
    assert abs(a - b) <= tol * max(1.0, abs(b)), (a, b)


def show(label, value):
    print(f"{label:58s} {value}")


# T1: a function that vanishes on the data but not in between (SE kernel, length scale 1)
k = lambda x, y: math.exp(-((x - y) ** 2) / 2)
a = k(0.5, 0) / (k(0, 0) + k(0, 1))  # equal weights by symmetry
g = lambda x: k(x, 0.5) - a * (k(x, 0) + k(x, 1))
close(g(0), 0, 1e-12); close(g(1), 0, 1e-12)
G = np.array([[k(u, v) for v in (0.5, 0, 1)] for u in (0.5, 0, 1)])
c = np.array([1, -a, -a])
norm2 = c @ G @ c
close(norm2, g(0.5), 1e-9)  # ||g||^2 = g(0.5) because g is orthogonal to the data span
show("T1 a", round(a, 4)); show("T1 g(0.5) = ||g||^2", round(g(0.5), 4)); show("T1 ||g||", round(math.sqrt(norm2), 4))
show("T1 c=100: value at 0.5, norm", (round(100 * g(0.5), 2), round(100 * math.sqrt(norm2), 2)))
close(a, 0.5493); close(g(0.5), 0.03046); close(math.sqrt(norm2), 0.1745)

# T2: LoSBO balls r = (y - E - h)/L with L = 2, E = 0.1, h = 0
r = lambda y: (y - 0.1 - 0) / 2
close(r(1.0), 0.45); close(r(0.9), 0.40); close(r(1.2), 0.55)
close(0.45 + r(0.9), 0.85); close(0.2 - r(1.2), -0.35); close(0.2 + r(1.2), 0.75)

# T3: regret rates with gamma_T ~ (ln T)^2 (SE kernel, d = 1, constants ignored)
T = 10_000
gam = math.log(T) ** 2
show("T3 gamma_T, gamma_T sqrt T, sqrt(gamma_T T), ratio",
     (round(gam, 1), round(gam * math.sqrt(T)), round(math.sqrt(gam * T)), round(math.sqrt(gam), 1)))
close(gam, 84.8, 1e-3); close(gam * math.sqrt(T), 8483, 1e-3); close(math.sqrt(gam * T), 921, 1e-3)
assert 1 / (2 * 0.5 + 1) == 0.5  # Matern nu = 1/2, d = 1: gamma_T ~ T^{d/(2 nu + d)} = T^{1/2}
close(1e6 ** 0.5, 1000); close(1e6 ** (2 / 3), 10_000, 1e-6)

# T4: ensemble members fit 2x on [0, 1] to within 0.02 and agree closely at x = 3
xs = np.linspace(0, 1, 101)
members = [lambda x: 2 * x, lambda x: 2 * x + 0.02 * x**2, lambda x: 2 * x - 0.02 * x**2]
assert max(abs(m(x) - 2 * x) for m in members for x in xs) <= 0.02 + 1e-12
preds = [m(3) for m in members]
show("T4 predictions at x=3, population std", ([round(p, 2) for p in preds], round(float(np.std(preds)), 3)))
close(float(np.std(preds)), 0.147)

# T5: lower bound after k steps = 0.30 - k * L
close(0.30 - 10 * 0.01, 0.20); close(0.30 - 30 * 0.01, 0.0, 1e-9); close(0.30 - 20 * 0.02, -0.10); close(0.30 - 20 * 0.01, 0.10)

# T6: p* = (R tau - inf V) e^{T_f/tau} - R tau with R = 1, tau = 1, inf V = 0
pstar = lambda Tf: (1 * 1 - 0) * math.exp(Tf / 1) - 1 * 1
show("T6 p* for T_f = 2, 5, 10", [round(pstar(t), 1) for t in (2, 5, 10)])
close(pstar(2), 6.39); close(pstar(5), 147.4); close(pstar(10), 22025.5)
show("T6 gamma^-T_f for gamma=0.99, T_f=100,500,1000", [round(0.99 ** -t, 1) for t in (100, 500, 1000)])
close(0.99 ** -100, 2.73, 2e-3); close(0.99 ** -500, 152.2, 2e-3); close(0.99 ** -1000, 23164, 2e-3)

# P1: Module 12 walkthrough network f(x) = W1 ReLU(W0 x + b0)
W0 = np.array([[1, 2], [1, -2]]); W1 = np.array([[1, 1]])
prod = np.linalg.norm(W1, 2) * np.linalg.norm(W0, 2)
grads = [np.linalg.norm(W1 @ np.diag(s) @ W0) for s in ([1, 1], [1, 0], [0, 1], [0, 0])]
show("P1 product bound, true L*, LipSDP (Module 12)", (round(prod, 3), round(max(grads), 3), round(4 / math.sqrt(3), 3)))
close(prod, 4); close(max(grads), math.sqrt(5)); assert 4 / math.sqrt(3) >= math.sqrt(5)

# P2: Counterexample 1 of Module 12: ReLU, v = (0, 1), vbar = (-1.5, 0), T = (e1 - e2)(e1 - e2)^T
relu = lambda v: np.maximum(v, 0)
v, vb = np.array([0.0, 1.0]), np.array([-1.5, 0.0])
dv, dz = v - vb, relu(v) - relu(vb)
Tm = np.array([[1, -1], [-1, 1]])
form = 2 * dv @ Tm @ dz - 2 * dz @ Tm @ dz
assert all(0 <= dz[i] / dv[i] <= 1 for i in range(2))  # each neuron's own chord has slope in [0, 1]
show("P2 dv, dz, coupled chord slope, quadratic form", (dv.tolist(), dz.tolist(), (dz[0] - dz[1]) / (dv[0] - dv[1]), form))
close(form, -3, 1e-12)

# P3: scalar a = 1, b = 1; q = 1, y = -2 gives k = -2 and closed loop -1
q, y = 1.0, -2.0
kk = y / q
assert q > 0 and 1 * q + 1 * y < 0 and 1 + 1 * kk == -1 and 2 * (1 / q) * (1 + kk) < 0

# P4: margin certificate radius M / (sqrt(2) L), L = 1
eps = 36 / 255
show("P4 36/255, radius for margins 0.25 and 0.15", (round(eps, 4), round(0.25 / math.sqrt(2), 4), round(0.15 / math.sqrt(2), 4)))
assert 0.25 / math.sqrt(2) > eps > 0.15 / math.sqrt(2)
d_img = 224 * 224 * 3
show("P4 per-value change if spread over ImageNet image (x255)", round(eps / math.sqrt(d_img) * 255, 3))
close(eps / math.sqrt(d_img) * 255, 0.0928)

# P5: kernel (1, 2, 3) as a state-space system
A = np.array([[0, 0], [1, 0]]); B = np.array([1, 0]); C = np.array([2, 3]); D = 1
u = [1, 0, 0, 0, 0]; x = np.zeros(2); ys = []
for ut in u:
    ys.append(float(C @ x + D * ut)); x = A @ x + B * ut
assert ys == [1, 2, 3, 0, 0], ys
u = [1, 1, 0, 2, 0]; x = np.zeros(2); ys = []
for ut in u:
    ys.append(float(C @ x + D * ut)); x = A @ x + B * ut
assert ys == list(np.convolve(u, [1, 2, 3])[:5]), ys
show("P5 output for input (1,1,0,2,0)", ys)

# R2: projected gradient descent-ascent on L(p, lam) = p - lam (p - 0.5)
p, lam, hist = 0.0, 0.0, [(0.0, 0.0)]
for _ in range(400):
    p, lam = min(1, max(0, p + 0.5 * (1 - lam))), max(0, lam + 0.5 * (p - 0.5))
    hist.append((p, lam))
show("R2 first 12 iterates (p, lambda)", [(round(a_, 3), round(b_, 3)) for a_, b_ in hist[:12]])
avg = sum(h[0] for h in hist) / len(hist)
show("R2 average p over 401 iterates; range of p in last 100", (round(avg, 3), min(h[0] for h in hist[-100:]), max(h[0] for h in hist[-100:])))
close(avg, 0.507, 2e-3); assert min(h[0] for h in hist[-100:]) == 0 and max(h[0] for h in hist[-100:]) == 1

# R3: C = 10 with probability 0.05, else 0
pC = 0.05
EC = 10 * pC
cvar90 = 0 + (10 - 0) * pC / 0.10  # VaR_0.9 = 0, CVaR = VaR + E[(C - VaR)_+] / (1 - 0.9)
show("R3 E[C], P(C>0), CVaR_0.9", (EC, pC, cvar90))
close(EC, 0.5); close(cvar90, 5)

# R4: least-squares line for a^2 on [0, 0.5], extrapolated to a = 2
aa = np.linspace(0, 0.5, 100001)
m_, q_ = np.polyfit(aa, aa**2, 1)
show("R4 slope, intercept, prediction at a=2 (true 4)", (round(m_, 4), round(q_, 4), round(m_ * 2 + q_, 4)))
close(m_, 0.5); close(q_, -1 / 24, 1e-3); close(m_ * 2 + q_, 0.9583)

# R5: harmful response r = 1.0, c = 0.6; safe response r = 0.7, c = 0.1; budget d = 0.3
qmax = (0.3 - 0.1) / (0.6 - 0.1); close(qmax, 0.4); close(0.7 + 0.3 * qmax, 0.82)
qwrong = (0.3 - 0.1) / (0.4 - 0.1); close(qwrong, 2 / 3)
true_cost = 0.6 * qwrong + 0.1 * (1 - qwrong)
show("R5 q allowed (true / wrong cost model), true cost at wrong q", (round(qmax, 3), round(qwrong, 3), round(true_cost, 3)))
close(true_cost, 0.4333)

# F2: grid spacing for a Lipschitz certificate: m - L r / 2 > 0 with m = 0.1, L = 50
rmax = 2 * 0.1 / 50; close(rmax, 0.004)
per_axis = math.floor(1 / rmax) + 1  # strict margin: cell-centred grid, r < rmax
r = 1 / per_axis
assert 0.1 - 50 * r / 2 > 0
show("F2 points per axis, d=2, d=6, d=12", (per_axis, per_axis**2, f"{per_axis**6:.2e}", f"{per_axis**12:.2e}"))
assert per_axis == 251 and per_axis**2 == 63_001

# F3: HOCBF for p' = v, v' = u, |u| <= 1, h = p, alpha1 = alpha2 = 1: u >= -2v - p
pp, vv = 1.0, -3.0
need = -2 * vv - pp
show("F3 required u, psi1, braking distance", (need, vv + pp, vv**2 / 2))
assert need == 5 and vv + pp == -2 and vv**2 / 2 == 4.5

# S1: split conformal quantile index ceil((n+1)(1-delta))
scores = sorted([0.2, 0.3, 0.3, 0.4, 0.5, 0.6, 0.8, 0.9, 1.2])
n = len(scores)
i90 = math.ceil((n + 1) * (1 - 0.1) - 1e-12); i95 = math.ceil((n + 1) * (1 - 0.05) - 1e-12)
assert i90 == 9 and scores[i90 - 1] == 1.2 and i95 == 10 > n

# S2: randomized smoothing radius sigma * Phi^{-1}(pA) when pB = 1 - pA
Phi_inv = NormalDist().inv_cdf
R = 0.5 * Phi_inv(0.9)
d_cifar = 32 * 32 * 3
show("S2 radius, l_inf radius (x255), 8/255", (round(R, 3), round(R / math.sqrt(d_cifar) * 255, 2), round(8 / 255, 4)))
close(R, 0.641); close(R / math.sqrt(d_cifar) * 255, 2.95, 2e-3)
pA_max = 0.001 ** (1 / 100_000)
show("S2 best pA lower bound with n=1e5, alpha=1e-3; max radius/sigma", (round(pA_max, 6), round(Phi_inv(pA_max), 2)))
close(Phi_inv(pA_max), 3.81, 2e-3)

# S3: an LMI that a solver tolerance of 1e-8 would accept
M = np.array([[1, 1], [1, 1 - 1e-9]])
ev = np.linalg.eigvalsh(M)
show("S3 eigenvalues", ev.tolist())
assert ev[0] < 0 and abs(ev[0] + 5e-10) < 1e-12

# B1: sum_{t=0}^{50} L^t for L = 1.1 and L = 0.9
s11 = sum(1.1**t for t in range(51)); s09 = sum(0.9**t for t in range(51))
show("B1 1.1^50, sum(1.1^t), sum(0.9^t)", (round(1.1**50, 1), round(s11, 1), round(s09, 2)))
close(1.1**50, 117.4); close(s11, 1281.3); close(s09, 9.95)

# B3: sampled error 0.02 + (L_NN + L_MPC) * r/2 with sum 4 and grid spacing 0.005
close(0.02 + 4 * 0.005 / 2, 0.03)

# B4: disagreement of two 1-Lipschitz members is 2-Lipschitz
close(0.05 + 2 * 1 * 0.1, 0.25)

print("all worked-example numbers check out")

# Extra checks added with the page text (2026-10-01)
# T1: the noise-free posterior std at 0.5 equals ||g||_k, so the bound |f(0.5) - 0| <= B * 0.1745
Kd = np.array([[1, k(0, 1)], [k(0, 1), 1]]); kv = np.array([k(0.5, 0), k(0.5, 1)])
sig = math.sqrt(1 - kv @ np.linalg.solve(Kd, kv))
close(sig, math.sqrt(norm2), 1e-9); close(1 * sig, 0.1745); close(20 * sig, 3.49)
# B3: coarsest admissible grid spacing for L = 4 vs L = 400 (0.02 + L r / 2 <= 0.05)
close(2 * (0.05 - 0.02) / 4, 0.015); close(2 * (0.05 - 0.02) / 400, 0.00015); close(0.015 / 0.00015, 100)
# R5: relative violation of the true limit
close((true_cost - 0.3) / 0.3, 0.444, 2e-3)
# P1: relative gaps of the product bound and LipSDP
close((4 - math.sqrt(5)) / math.sqrt(5), 0.789, 2e-3); close((4 / math.sqrt(3) - math.sqrt(5)) / math.sqrt(5), 0.033, 2e-2)
# T4: error / spread
assert (6 - 2) / float(np.std(preds)) > 25
# S1: only one of the new errors is covered by the 1.2 m bar
assert sum(e <= 1.2 for e in (1.0, 1.5, 1.8, 2.0)) == 1
# notation table: 0.99^100, ||c k(.,x)||_k = |c| sqrt(k(x,x)), Phi^{-1}(0.9)
close(0.99**100, 0.366); close(2 * math.sqrt(k(0, 0)), 2); close(Phi_inv(0.9), 1.28, 2e-3)
print("extra checks pass")

# B1 (after review 2): parameter sensitivity e_t <= L_theta |dtheta| sum_{s<t} L^s, tested on F(x, th) = 0.9 sin(x) + 0.5 th
rng = np.random.default_rng(0)
for _ in range(200):
    th, th2, x0 = rng.normal(size=3)
    xa = xb = x0
    for t in range(1, 30):
        xa, xb = 0.9 * math.sin(xa) + 0.5 * th, 0.9 * math.sin(xb) + 0.5 * th2
        assert abs(xa - xb) <= 0.5 * abs(th - th2) * sum(0.9**s for s in range(t)) + 1e-12
# R1 (after review 2): a sure crash at step 300 with gamma = 0.99 has discounted cost below 0.05
close(0.99**300, 0.0490, 2e-3); assert 0.99**300 < 0.05
print("review-2 checks pass")
