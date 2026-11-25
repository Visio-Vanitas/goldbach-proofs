#!/usr/bin/env python3
"""
Standalone 100% IEEE-754-Float-Free Pure-Integer Interval Certification for D_{1,2}(N)
at Classical Level 1/2 (Pan-Ding Mean-Value Theorem + Chen Switching K = 8, z = 3/40)
--------------------------------------------------------------------------------------
Companion pure-integer certification script for `research/diagnostics/SwitchedSieveAndDiagnostics.md`.

Uses ONLY Python 3 standard-library exact integer and rational arithmetic (`ast`,
`collections`, `fractions`, `pathlib`, `time`). Zero floating-point literals,
`float(...)` conversions, `math.*`, `numpy`, `scipy`, or `decimal` imports appear
anywhere in this file (verified at startup via AST scan).

Normalisation (matching Chen 1973, Wu 2004 `arXiv:0705.1652`, Wu 2008 `arXiv:0709.3764`,
and Runbo Li `arXiv:2405.05727v4`):
  Theta(N) := C(N) * N / (log N)^2,
  C(N)     := prod_{p | N, p > 2} ((p - 1)/(p - 2)) * prod_{p > 2} (1 - 1/(p - 1)^2),
  D_{1,2}(N) := #{p <= N : Omega(N - p) <= 2}.

Certifies two published level-1/2 calibration benchmarks alongside three standalone
rational-coefficient Buchstab-switching identities at distribution level theta = 1/2
and classical Rosser-Iwaniec switched upper-bound factor K = 8 (zero double sieve,
zero Fouvry 5/9, zero post-2020 large-modulus preprints), at fixed-point scale
S = 10**18 (guard 10**24):

  B1. BENCH_CHEN_HR_1973 (z = 1/10, K = 8, Chen 1973 / Halberstam-Richert 1974 Ch. 11,
      constant S1 weight -1/2 on [1/10, 1/3), denom 2):
        Reproduces the published constant 0.689 (certified >= +0.689065 * Theta(N)
        vs exact continuous integral 0.689517).
  B2. BENCH_WU08_PURE_K8 (kappa_1 = 100/1327, kappa_2 = 25/206, Wu 2008 arXiv:0709.3764
      Lemma 2.2 six direct observables at pure K = 8, no double sieve, no Fouvry, denom 4):
        Reproduces S0(kappa_1) >= 14.900902 (Wu 14.900897), S0(kappa_2) >= 9.103016
        (Wu 9.103015), r = 3 slack measure <= 0.370097 (Wu exact 0.370056), and
        certifies D_{1,2}(N) >= +0.877232 * Theta(N) (+0.0149 above Wu's pure-K=8
        0.862327 via exact cell-slack accounting on r >= 5).
  1. D12_BV22_S2 (22-edge BV22 grid, z = 3/40, S0..S2 ONLY, 39 active terms, denom 672):
       Certifies D_{1,2}(N) >= +0.930457 * Theta(N) without any 3-prime observables S3.
  2. D12_BV22_S3 (22-edge BV22 grid, z = 3/40, S0..S3, 58 active terms, denom 20782):
       Certifies D_{1,2}(N) >= +0.958320 * Theta(N) directly on the BV22 grid and
       D_{1, 1000/529}(N) >= +0.029278 * Theta(N) via 8 * ln(529/471).
  3. D12_REF18_S3 (18-edge REF18 grid, z = 3/40, S0..S3, 87 active terms, denom 24000):
       Certifies D_{1,2}(N) >= +0.961226 * Theta(N) on a 17-bin partition of [3/40, 1)
       and D_{1, 1000/529}(N) >= +0.032184 * Theta(N) via sub-cell switching at 471/1000.

Pointwise inequality convention on every ordered prime-exponent bin cell C (1 <= r <= 13):
  target_D12(C) := 1 if r <= 2 else 0,
  W_dir(C) - s_C <= target_D12(C)   (equivalently target_D12(C) - W_dir(C) + s_C >= 0),
with s_C = 0 on ALL r <= 2 cells (zero switched semiprime cells) and s_C >= 0 on r >= 3.
"""

import ast
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import time


# ============================================================================
# 0. Self-Audit: AST Verification of Zero Float / Math / External Dependencies
# ============================================================================

def audit_ast_zero_float() -> tuple[int, int, int]:
    src = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(src, filename=str(__file__))
    forbidden_imports = {"math", "cmath", "numpy", "scipy", "decimal"}
    float_literals = 0
    float_calls = 0
    bad_imports = 0

    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
            float_literals += 1
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in {"float", "complex"}:
            float_calls += 1
        elif isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name.split(".")[0] in forbidden_imports:
                    bad_imports += 1
        elif isinstance(node, ast.ImportFrom):
            if node.module and node.module.split(".")[0] in forbidden_imports:
                bad_imports += 1

    assert float_literals == 0, f"Found {float_literals} float/complex literals!"
    assert float_calls == 0, f"Found {float_calls} float()/complex() calls!"
    assert bad_imports == 0, f"Found {bad_imports} forbidden imports!"
    return float_literals, float_calls, bad_imports


# ============================================================================
# 1. Pure-Integer Fixed-Point Primitives (FP_S = 10**18, Guard FP_G = 10**24)
# ============================================================================

FP_S = 10 ** 18
FP_GUARD = 10 ** 6
FP_G = FP_S * FP_GUARD


def _gcd(a: int, b: int) -> int:
    a = abs(a)
    b = abs(b)
    while b:
        a, b = b, a % b
    return a


def _lcm(a: int, b: int) -> int:
    return (a // _gcd(a, b)) * b


def _factorial(n: int) -> int:
    res = 1
    for k in range(2, n + 1):
        res *= k
    return res


def _cdiv(num: int, den: int) -> int:
    """Exact ceiling division ceil(num / den) for any int num and den > 0."""
    return -((-num) // den)


def _fp_fmt(val_s: int, digits: int = 6, signed: bool = False, mode: str = "near") -> str:
    """Pure-integer decimal formatting of val_s / 10**18 with outward floor/ceil option."""
    assert isinstance(val_s, int)
    scale_d = 10 ** (18 - digits)
    if mode == "floor":
        q = val_s // scale_d
    elif mode == "ceil":
        q = _cdiv(val_s, scale_d)
    else:
        q = (val_s + scale_d // 2) // scale_d if val_s >= 0 else -((-val_s + scale_d // 2) // scale_d)
    neg = q < 0
    vq = -q if neg else q
    ten_d = 10 ** digits
    whole, frac = vq // ten_d, vq % ten_d
    sgn = "-" if neg else ("+" if signed else "")
    return f"{sgn}{whole}.{frac:0{digits}d}"


def _fp_rat_iv(p: int, q: int, scale: int = FP_S) -> tuple[int, int]:
    """Outward-rounded integer interval [lo, hi] for p / q at given scale (q > 0)."""
    return (p * scale) // q, _cdiv(p * scale, q)


def _fp_mul_nn(a_lo: int, a_hi: int, b_lo: int, b_hi: int, scale: int = FP_S) -> tuple[int, int]:
    """Outward-rounded multiplication for non-negative intervals."""
    return (a_lo * b_lo) // scale, _cdiv(a_hi * b_hi, scale)


def _fp_mul_signed(a_lo: int, a_hi: int, b_lo: int, b_hi: int, scale: int = FP_S) -> tuple[int, int]:
    """Outward-rounded multiplication for signed integer intervals."""
    p1, p2, p3, p4 = a_lo * b_lo, a_lo * b_hi, a_hi * b_lo, a_hi * b_hi
    return min(p1, p2, p3, p4) // scale, _cdiv(max(p1, p2, p3, p4), scale)


def build_pure_int_math():
    """
    Constructs pure-integer outward-rounded natural logarithm `ln_rat_iv`, Euler-Mascheroni
    constant `gamma`, `e^gamma`, and `e^-gamma` from Taylor / Euler-Maclaurin series with
    explicit analytical remainder bounds at guard scale FP_G = 10**24.
    """
    def _artanh_rat_g(p: int, q: int, terms: int = 16) -> tuple[int, int]:
        if p == 0:
            return 0, 0
        assert 0 < p and p * 5 <= q
        p2, q2 = p * p, q * q
        lo_acc, hi_acc = 0, 0
        t_lo = (2 * FP_G * p) // q
        t_hi = _cdiv(2 * FP_G * p, q)
        for k in range(terms):
            denom = 2 * k + 1
            lo_acc += t_lo // denom
            hi_acc += _cdiv(t_hi, denom)
            t_lo = (t_lo * p2) // q2
            t_hi = _cdiv(t_hi * p2, q2)
        tail_hi = _cdiv(t_hi * q2, (2 * terms + 1) * (q2 - p2)) + 1
        return lo_acc, hi_acc + tail_hi

    ln2_lo_g, ln2_hi_g = 0, 0
    t_lo = (2 * FP_G) // 3
    t_hi = _cdiv(2 * FP_G, 3)
    for k in range(28):
        ln2_lo_g += t_lo // (2 * k + 1)
        ln2_hi_g += _cdiv(t_hi, 2 * k + 1)
        t_lo //= 9
        t_hi = _cdiv(t_hi, 9)
    ln2_hi_g += 2

    ln_k8_g = {8: (0, 0)}
    for k in (5, 6, 7, 9, 10, 11):
        diff = abs(k - 8)
        summ = k + 8
        d2, s2 = diff * diff, summ * summ
        a_lo, a_hi = 0, 0
        u_lo = (2 * FP_G * diff) // summ
        u_hi = _cdiv(2 * FP_G * diff, summ)
        for j in range(22):
            a_lo += u_lo // (2 * j + 1)
            a_hi += _cdiv(u_hi, 2 * j + 1)
            u_lo = (u_lo * d2) // s2
            u_hi = _cdiv(u_hi * d2, s2)
        a_hi += 2
        ln_k8_g[k] = (a_lo, a_hi) if k > 8 else (-a_hi, -a_lo)

    def ln_rat_iv_g(num: int, den: int) -> tuple[int, int]:
        assert num > 0 and den > 0
        if num == den:
            return 0, 0
        if num < den:
            if (den - num) * 64 <= num:
                lo_pos, hi_pos = ln_rat_iv_g(den, num)
                return -hi_pos, -lo_pos
        else:
            p = num - den
            if p * 1024 <= den:
                t_lo_s = (FP_G * p) // den
                t_hi_s = _cdiv(FP_G * p, den)
                s_lo, s_hi = t_lo_s, t_hi_s
                for j in range(2, 8):
                    t_lo_s = (t_lo_s * p) // den
                    t_hi_s = _cdiv(t_hi_s * p, den)
                    if j & 1:
                        s_lo += t_lo_s // j
                        s_hi += _cdiv(t_hi_s, j)
                    else:
                        s_lo -= _cdiv(t_hi_s, j)
                        s_hi -= t_lo_s // j
                rem8_hi = _cdiv(t_hi_s * p, den * 8) + 1
                return s_lo - rem8_hi, s_hi
            if p * 64 <= den:
                t_lo_s = (FP_G * p) // den
                t_hi_s = _cdiv(FP_G * p, den)
                s_lo, s_hi = 0, 0
                for j in range(1, 16):
                    if j & 1:
                        s_lo += t_lo_s // j
                        s_hi += _cdiv(t_hi_s, j)
                    else:
                        s_lo -= _cdiv(t_hi_s, j)
                        s_hi -= t_lo_s // j
                    if j < 15:
                        t_lo_s = (t_lo_s * p) // den
                        t_hi_s = _cdiv(t_hi_s * p, den)
                rem16_hi = _cdiv(t_hi_s * p, den * 16) + 1
                return s_lo - rem16_hi, s_hi

        m = num.bit_length() - den.bit_length()
        n1, d1 = (num, den << m) if m >= 0 else (num << (-m), den)
        while 3 * n1 < 2 * d1:
            m -= 1
            n1 <<= 1
        while 3 * n1 > 4 * d1:
            m += 1
            d1 <<= 1
        k = max(5, min(11, (8 * n1 + (d1 >> 1)) // d1))
        n2, d2 = 8 * n1, k * d1
        if n2 >= d2:
            r_lo, r_hi = _artanh_rat_g(n2 - d2, n2 + d2, terms=11)
        else:
            a_lo, a_hi = _artanh_rat_g(d2 - n2, n2 + d2, terms=11)
            r_lo, r_hi = -a_hi, -a_lo
        k_lo, k_hi = ln_k8_g[k]
        if m >= 0:
            m_lo, m_hi = m * ln2_lo_g, m * ln2_hi_g
        else:
            m_lo, m_hi = m * ln2_hi_g, m * ln2_lo_g
        return m_lo + k_lo + r_lo, m_hi + k_hi + r_hi

    def ln_rat_iv(num: int, den: int) -> tuple[int, int]:
        lo_g, hi_g = ln_rat_iv_g(num, den)
        return lo_g // FP_GUARD, _cdiv(hi_g, FP_GUARD)

    N_em = 1000
    H_lo = sum(FP_G // k for k in range(1, N_em + 1))
    H_hi = sum(_cdiv(FP_G, k) for k in range(1, N_em + 1))
    lnN_lo, lnN_hi = ln_rat_iv_g(N_em, 1)
    corr_frac = (
        -Fraction(1, 2 * N_em)
        + Fraction(1, 12 * N_em ** 2)
        - Fraction(1, 120 * N_em ** 4)
        + Fraction(1, 252 * N_em ** 6)
    )
    c_lo, c_hi = _fp_rat_iv(corr_frac.numerator, corr_frac.denominator, FP_G)
    gamma_lo_g = H_lo - lnN_hi + c_lo - 1
    gamma_hi_g = H_hi - lnN_lo + c_hi

    def exp_pos_iv_g(x_lo_g: int, x_hi_g: int) -> tuple[int, int]:
        assert 0 <= x_lo_g <= x_hi_g <= FP_G
        s_lo, s_hi = FP_G, FP_G
        t_lo_e, t_hi_e = FP_G, FP_G
        for deg in range(1, 27):
            t_lo_e = (t_lo_e * x_lo_g) // (FP_G * deg)
            t_hi_e = _cdiv(t_hi_e * x_hi_g, FP_G * deg)
            s_lo += t_lo_e
            s_hi += t_hi_e
        return s_lo, s_hi + 2

    eg_lo_g, eg_hi_g = exp_pos_iv_g(gamma_lo_g, gamma_hi_g)
    emg_lo_g = (FP_G * FP_G) // eg_hi_g
    emg_hi_g = _cdiv(FP_G * FP_G, eg_lo_g)

    consts = {
        "gamma_s": (gamma_lo_g // FP_GUARD, _cdiv(gamma_hi_g, FP_GUARD)),
        "exp_gamma_g": (eg_lo_g, eg_hi_g),
        "exp_gamma_s": (eg_lo_g // FP_GUARD, _cdiv(eg_hi_g, FP_GUARD)),
        "exp_mgamma_s": (emg_lo_g // FP_GUARD, _cdiv(emg_hi_g, FP_GUARD)),
    }
    return ln_rat_iv_g, ln_rat_iv, consts


# ============================================================================
# 2. Pure-Integer Delay-ODE Enclosures for F(s) and f(s) up to s = 20
# ============================================================================

def build_fp_ode_enclosures(ln_rat_iv_g, consts, M: int = 600, K_MAX: int = 20):
    """
    Propagates convex Phi(s) = s * F(s) and concave phi(s) = s * f(s) on [1, K_MAX]
    at guard scale FP_G = 10**24 using exact secant/tangent bounds, exposing outward
    F_hi_s(s_lo_s) and f_lo_s(s_lo_s) at public scale FP_S = 10**18.
    """
    N_grid = K_MAX * M
    Phi_lo = [0] * (N_grid + 1)
    Phi_hi = [0] * (N_grid + 1)
    phi_lo = [0] * (N_grid + 1)
    phi_hi = [0] * (N_grid + 1)

    eg_lo_g, eg_hi_g = consts["exp_gamma_g"]
    c2eg_lo = 2 * eg_lo_g
    c2eg_hi = 2 * eg_hi_g

    ln_sec_lo = [0] * N_grid
    ln_sec_hi = [0] * N_grid
    ln_t1_lo = [0] * N_grid
    ln_t1_hi = [0] * N_grid
    ln_t2_lo = [0] * N_grid
    ln_t2_hi = [0] * N_grid
    for n in range(M, (K_MAX - 1) * M + 1):
        ln_sec_lo[n], ln_sec_hi[n] = ln_rat_iv_g(n + 1, n)
        ln_t1_lo[n], ln_t1_hi[n] = ln_rat_iv_g(2 * n + 1, 2 * n)
        ln_t2_lo[n], ln_t2_hi[n] = ln_rat_iv_g(2 * n + 2, 2 * n + 1)

    for i in range(M, 3 * M + 1):
        Phi_lo[i] = c2eg_lo
        Phi_hi[i] = c2eg_hi

    for i in range(2 * M + 1, 4 * M + 1):
        l_lo, l_hi = ln_rat_iv_g(i - M, M)
        phi_lo[i], _ = _fp_mul_nn(c2eg_lo, c2eg_hi, l_lo, l_hi, FP_G)
        _, phi_hi[i] = _fp_mul_nn(c2eg_lo, c2eg_hi, l_lo, l_hi, FP_G)

    two_M = 2 * M
    for k in range(3, K_MAX):
        for j in range(M):
            idx = k * M + j
            n = idx - M
            pa_lo, pb_lo = phi_lo[n], phi_lo[n + 1]
            coef_sec = (n + 1) * pa_lo - n * pb_lo
            t_sec_lo, _ = _fp_mul_signed(coef_sec, coef_sec, ln_sec_lo[n], ln_sec_hi[n], FP_G)
            int_lo = t_sec_lo + (pb_lo - pa_lo)

            pa_hi, pb_hi = phi_hi[n], phi_hi[n + 1]
            sl_a_hi = _cdiv(M * Phi_hi[n - M], n - M)
            sl_b_lo = (M * Phi_lo[n + 1 - M]) // (n + 1 - M)
            c_left_hi = pa_hi - (n * sl_a_hi) // M
            _, t1_hi = _fp_mul_signed(c_left_hi, c_left_hi, ln_t1_lo[n], ln_t1_hi[n], FP_G)
            c_right_hi = pb_hi - ((n + 1) * sl_b_lo) // M
            _, t2_hi = _fp_mul_signed(c_right_hi, c_right_hi, ln_t2_lo[n], ln_t2_hi[n], FP_G)
            int_hi = t1_hi + _cdiv(sl_a_hi, two_M) + t2_hi + _cdiv(sl_b_lo, two_M)

            Phi_lo[idx + 1] = Phi_lo[idx] + int_lo
            Phi_hi[idx + 1] = Phi_hi[idx] + int_hi

        if k + 1 <= K_MAX - 1:
            for j in range(M):
                idx = (k + 1) * M + j
                n = idx - M
                Pa_hi, Pb_hi = Phi_hi[n], Phi_hi[n + 1]
                coef_sec = (n + 1) * Pa_hi - n * Pb_hi
                _, t_sec_hi = _fp_mul_signed(coef_sec, coef_sec, ln_sec_lo[n], ln_sec_hi[n], FP_G)
                int_hi = t_sec_hi + (Pb_hi - Pa_hi)

                Pa_lo, Pb_lo = Phi_lo[n], Phi_lo[n + 1]
                sl_a_lo = (M * phi_lo[n - M]) // (n - M)
                sl_b_hi = _cdiv(M * phi_hi[n + 1 - M], n + 1 - M)
                c_left_lo = Pa_lo - _cdiv(n * sl_a_lo, M)
                t1_lo, _ = _fp_mul_signed(c_left_lo, c_left_lo, ln_t1_lo[n], ln_t1_hi[n], FP_G)
                c_right_lo = Pb_lo - _cdiv((n + 1) * sl_b_hi, M)
                t2_lo, _ = _fp_mul_signed(c_right_lo, c_right_lo, ln_t2_lo[n], ln_t2_hi[n], FP_G)
                int_lo = t1_lo + (sl_a_lo // two_M) + t2_lo + (sl_b_hi // two_M)

                phi_lo[idx + 1] = phi_lo[idx] + int_lo
                phi_hi[idx + 1] = phi_hi[idx] + int_hi

    Phi_hi_s = [_cdiv(v, FP_GUARD) for v in Phi_hi]
    phi_lo_s = [max(0, v // FP_GUARD) for v in phi_lo]
    c2eg_hi_s = _cdiv(c2eg_hi, FP_GUARD)

    F_at_K_hi_s = _cdiv(Phi_hi_s[K_MAX * M], K_MAX)
    f_at_K_lo_s = phi_lo_s[K_MAX * M] // K_MAX

    def F_hi_s(s_lo_s: int) -> int:
        assert s_lo_s > 0
        if s_lo_s <= 3 * FP_S:
            return _cdiv(c2eg_hi_s * FP_S, s_lo_s)
        if s_lo_s >= K_MAX * FP_S:
            return F_at_K_hi_s
        sm = s_lo_s * M
        idx = sm // FP_S
        if idx >= K_MAX * M:
            return F_at_K_hi_s
        rem = sm - idx * FP_S
        d_phi = Phi_hi_s[idx + 1] - Phi_hi_s[idx]
        Phi_sec_hi = Phi_hi_s[idx] + (_cdiv(d_phi * rem, FP_S) if d_phi >= 0 else -(((-d_phi) * rem) // FP_S))
        return _cdiv(Phi_sec_hi * FP_S, s_lo_s)

    def f_lo_s(s_lo_s: int) -> int:
        if s_lo_s <= 2 * FP_S:
            return 0
        if s_lo_s >= K_MAX * FP_S:
            return f_at_K_lo_s
        sm = s_lo_s * M
        idx = sm // FP_S
        if idx >= K_MAX * M:
            return f_at_K_lo_s
        rem = sm - idx * FP_S
        phi_sec_lo = phi_lo_s[idx] + ((phi_lo_s[idx + 1] - phi_lo_s[idx]) * rem) // FP_S
        return (phi_sec_lo * FP_S) // s_lo_s

    meta = {
        "F20_hi_s": F_at_K_hi_s,
        "f20_lo_s": f_at_K_lo_s,
    }
    return F_hi_s, f_lo_s, meta


# ============================================================================
# 3. Step A: Complete DFS Enumeration & Direct D_{1,2} Pointwise Verification
# ============================================================================

def enumerate_configs_exact(edges_f: list[Fraction]) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]]]:
    """
    Complete deterministic DFS enumeration in 100% exact scaled-integer arithmetic
    (zero epsilons, zero sampling) of all ordered bin tuples C = (b_1, ..., b_r)
    for 1 <= r <= floor(1 / alpha_0) = 13:
      - `configs`: all interior cells with sum E[b_j] < L_grid < sum E[b_j + 1] (plus (M-1,));
      - `bdry_configs`: all upper-boundary tuples with sum E[b_j + 1] == L_grid (mu(C) = 0).
    """
    M = len(edges_f) - 1
    assert Fraction(1, 20) <= edges_f[0] <= Fraction(1, 5), "Direct D_{1,2} certifier requires alpha_0 in [1/20, 1/5]"
    assert edges_f[M - 1] == Fraction(1, 2) and edges_f[M] == Fraction(1, 1)
    for i in range(M):
        assert edges_f[i] < edges_f[i + 1]

    L_grid = 1
    for e in edges_f:
        L_grid = _lcm(L_grid, e.denominator)
    E = [int(e * L_grid) for e in edges_f]
    L_half = L_grid // 2
    assert E[M - 1] == L_half and E[M] == L_grid

    r_max = int(Fraction(1, 1) // edges_f[0])
    assert 5 <= r_max <= 20
    configs: list[tuple[int, ...]] = [(M - 1,)]
    bdry_configs: list[tuple[int, ...]] = []

    def dfs_gt_half(min_b: int, rem_r: int, cur_lo: int, prefix: tuple[int, ...]) -> None:
        if rem_r == 0:
            if cur_lo < L_half:
                configs.append(prefix + (M - 1,))
            return
        for b in range(min_b, M - 1):
            if cur_lo + rem_r * E[b] >= L_half:
                break
            dfs_gt_half(b, rem_r - 1, cur_lo + E[b], prefix + (b,))

    def dfs_lt_half(min_b: int, rem_r: int, cur_lo: int, cur_hi: int, prefix: tuple[int, ...]) -> None:
        if rem_r == 0:
            if cur_lo < L_grid < cur_hi:
                configs.append(prefix)
            elif cur_lo < L_grid and cur_hi == L_grid:
                bdry_configs.append(prefix)
            return
        for b in range(min_b, M - 1):
            if cur_lo + rem_r * E[b] >= L_grid:
                break
            if cur_hi + rem_r * E[M - 1] < L_grid:
                continue
            dfs_lt_half(b, rem_r - 1, cur_lo + E[b], cur_hi + E[b + 1], prefix + (b,))

    for r in range(2, r_max + 1):
        if (r - 1) * E[0] < L_half:
            dfs_gt_half(0, r - 1, 0, ())
        dfs_lt_half(0, r, 0, 0, ())

    return configs, bdry_configs


def eval_obs_multiplicity_on_cell(spec: tuple, c: tuple[int, ...]) -> int:
    """Exact integer sieve multiplicity Phi_m(C) from the prime-tuple definition at kz = 0."""
    kind = spec[0]
    rc = len(c)
    if kind == "S0":
        kz = spec[1]
        assert kz >= 0
        return 1 if c[0] >= kz else 0
    if kind == "S1":
        b, kz = spec[1], spec[2]
        assert kz == 0
        cnt = 0
        for i1 in range(rc):
            if c[i1] == b and all(c[l] >= kz for l in range(rc) if l != i1):
                cnt += 1
        return cnt
    if kind == "S2":
        b1, b2, kz = spec[1], spec[2], spec[3]
        assert kz == 0
        cnt = 0
        for i1 in range(rc):
            if c[i1] != b1:
                continue
            for i2 in range(i1 + 1, rc):
                if c[i2] != b2:
                    continue
                if all(c[l] >= kz for l in range(rc) if l != i1 and l != i2):
                    cnt += 1
        return cnt
    if kind == "S3":
        b1, b2, b3, kz = spec[1], spec[2], spec[3], spec[4]
        assert kz == 0
        cnt = 0
        for i1 in range(rc):
            if c[i1] != b1:
                continue
            for i2 in range(i1 + 1, rc):
                if c[i2] != b2:
                    continue
                for i3 in range(i2 + 1, rc):
                    if c[i3] != b3:
                        continue
                    if all(c[l] >= kz for l in range(rc) if l != i1 and l != i2 and l != i3):
                        cnt += 1
        return cnt
    raise ValueError(f"Unknown observable spec: {spec}")


def verify_d12_observable_domains(edges_f: list[Fraction], terms: list[tuple[int, tuple]], allow_s3: bool) -> dict:
    """Verifies exact level-1/2 modulus and sifting-range hypotheses on every active observable."""
    M = len(edges_f) - 1
    z = edges_f[0]
    assert Fraction(1, 20) <= z <= Fraction(1, 5)
    counts_by_kind: dict[str, int] = defaultdict(int)
    min_s_by_kind: dict[str, Fraction] = {}

    for coef_num, spec in terms:
        assert coef_num != 0
        kind = spec[0]
        counts_by_kind[kind] += 1
        if kind == "S0":
            kz_s0 = spec[1]
            assert coef_num > 0 and 0 <= kz_s0 < M - 1 and edges_f[kz_s0] <= Fraction(1, 3)
            s_min = Fraction(1, 2) / edges_f[kz_s0]
        elif kind == "S1":
            b, kz = spec[1], spec[2]
            assert coef_num < 0 and kz == 0 and 0 <= b < M - 1
            assert edges_f[b + 1] <= Fraction(1, 3)
            s_min = (Fraction(1, 2) - edges_f[b + 1]) / z
        elif kind == "S2":
            b1, b2, kz = spec[1], spec[2], spec[3]
            assert coef_num > 0 and kz == 0 and 0 <= b1 <= b2 < M - 1
            sum_hi = edges_f[b1 + 1] + edges_f[b2 + 1]
            assert sum_hi < Fraction(1, 2) and sum_hi < Fraction(1, 1) - z
            s_min = (Fraction(1, 2) - sum_hi) / z
        elif kind == "S3":
            assert allow_s3, "S3 observable encountered in S2-only identity!"
            b1, b2, b3, kz = spec[1], spec[2], spec[3], spec[4]
            assert coef_num < 0 and kz == 0 and 0 <= b1 <= b2 <= b3 < M - 1
            sum_hi = edges_f[b1 + 1] + edges_f[b2 + 1] + edges_f[b3 + 1]
            assert sum_hi < Fraction(1, 2) and sum_hi < Fraction(1, 1) - z
            s_min = (Fraction(1, 2) - sum_hi) / z
        else:
            raise ValueError(f"Unknown observable: {spec}")

        if kind not in min_s_by_kind or s_min < min_s_by_kind[kind]:
            min_s_by_kind[kind] = s_min

    return {
        "counts_by_kind": dict(counts_by_kind),
        "min_s_by_kind": dict(min_s_by_kind),
    }


def step_a_verify_pointwise_d12(
    configs: list[tuple[int, ...]],
    bdry_configs: list[tuple[int, ...]],
    denom: int,
    terms: list[tuple[int, tuple]],
) -> dict:
    """
    Verifies the direct D_{1,2} pointwise inequality across ALL r = 1..13 cells
    (both interior `configs` and mu = 0 upper-boundary `bdry_configs`):
      - target_D12(C) = 1 for all r <= 2, and 0 for all r >= 3;
      - W_dir(C) - s_C <= target_D12(C)  (i.e. target_D12(C) - W_dir(C) + s_C >= 0);
      - s_C == 0 for ALL r <= 2 cells (zero switched r <= 2 cells!).
    """
    n_cfg = len(configs)
    W_num = [0] * n_cfg
    for ic, c in enumerate(configs):
        acc = 0
        for coef_num, spec in terms:
            mult = eval_obs_multiplicity_on_cell(spec, c)
            if mult:
                acc += coef_num * mult
        W_num[ic] = acc

    violations = 0
    r2_slacked = 0
    slacked_cells: list[tuple[tuple[int, ...], int]] = []
    slacked_counts_by_r: dict[int, int] = defaultdict(int)
    min_w_r2 = Fraction(10, 1)
    max_w_r2 = Fraction(-10, 1)
    max_w_by_r: dict[int, Fraction] = {}
    cells_by_r: dict[int, int] = defaultdict(int)

    for ic, c in enumerate(configs):
        r = len(c)
        cells_by_r[r] += 1
        rhs_num = denom if r <= 2 else 0
        w_frac = Fraction(W_num[ic], denom)
        if r == 2:
            if w_frac < min_w_r2:
                min_w_r2 = w_frac
            if w_frac > max_w_r2:
                max_w_r2 = w_frac
        if r not in max_w_by_r or w_frac > max_w_by_r[r]:
            max_w_by_r[r] = w_frac

        s_num = max(0, W_num[ic] - rhs_num)
        # Equivalent forms: W_dir(C) - s_C <= target(C) <==> (target(C) - W_dir(C)) + s_C >= 0
        if s_num < 0 or W_num[ic] - s_num > rhs_num:
            violations += 1
        if r <= 2 and s_num > 0:
            r2_slacked += 1
            violations += 1
        if s_num > 0:
            slacked_cells.append((c, s_num))
            slacked_counts_by_r[r] += 1

    assert Fraction(W_num[0], denom) == Fraction(1, 1), "Prime cell r = 1 must have W_dir == 1"

    bdry_slacked = 0
    for c_b in bdry_configs:
        rb = len(c_b)
        rhs_b = denom if rb <= 2 else 0
        acc_b = sum(coef_num * eval_obs_multiplicity_on_cell(spec, c_b) for coef_num, spec in terms)
        if rb <= 2 and acc_b > rhs_b:
            violations += 1
        if acc_b > rhs_b:
            bdry_slacked += 1

    assert violations == 0, f"Pointwise inequality violations: {violations}"
    assert r2_slacked == 0, f"Switched r <= 2 cells encountered: {r2_slacked}"

    return {
        "cells_by_r": dict(sorted(cells_by_r.items())),
        "slacked_cells": slacked_cells,
        "slacked_counts_by_r": dict(sorted(slacked_counts_by_r.items())),
        "min_w_r2": min_w_r2,
        "max_w_r2": max_w_r2,
        "max_w_by_r": dict(sorted(max_w_by_r.items())),
        "violations": violations,
        "r2_slacked": r2_slacked,
        "bdry_checked": len(bdry_configs),
        "bdry_slacked_mu0": bdry_slacked,
    }


# ============================================================================
# 4. Step B: Pure-Integer 10**18 Outward Enclosures of S0, S1, S2, S3 at theta=1/2
# ============================================================================

SLOT_BITS = 160
SLOT_MASK = (1 << SLOT_BITS) - 1


def build_bin_grid_weights_hi_lo(edges_f: list[Fraction], ln_rat_iv, G: int):
    """
    Splits each bin I_b = [edges_f[b], edges_f[b+1]) (0 <= b < M-1) by the uniform 1/G
    rational grid, returning exact pure-integer outward upper and lower 160-bit packed
    convolution polynomials W_hi_packed[b], W_lo_packed[b] at scale FP_S = 10**18.
    """
    M = len(edges_f) - 1
    W_hi_packed = [None] * M
    W_lo_packed = [None] * M
    for b in range(M - 1):
        lo_f, hi_f = edges_f[b], edges_f[b + 1]
        k_start = (lo_f.numerator * G) // lo_f.denominator
        k_end = _cdiv(hi_f.numerator * G, hi_f.denominator)
        vals_hi = []
        vals_lo = []
        for k in range(k_start, k_end):
            a_f = lo_f if lo_f * G >= k else Fraction(k, G)
            b_f = hi_f if hi_f * G <= k + 1 else Fraction(k + 1, G)
            if b_f > a_f:
                rat = b_f / a_f
                w_lo, w_hi = ln_rat_iv(rat.numerator, rat.denominator)
                vals_hi.append(w_hi)
                vals_lo.append(w_lo)
            else:
                vals_hi.append(0)
                vals_lo.append(0)
        pack_hi = 0
        pack_lo = 0
        for idx_v, (vlo, vhi) in enumerate(zip(vals_lo, vals_hi)):
            if vhi:
                pack_hi |= vhi << (idx_v * SLOT_BITS)
            if vlo:
                pack_lo |= vlo << (idx_v * SLOT_BITS)
        W_hi_packed[b] = (k_start, len(vals_hi), pack_hi)
        W_lo_packed[b] = (k_start, len(vals_lo), pack_lo)
    return W_hi_packed, W_lo_packed


def step_b_enclose_bv_observables(
    edges_f: list[Fraction],
    terms: list[tuple[int, tuple]],
    consts: dict,
    F_hi_s,
    f_lo_s,
    W_hi_packed: list,
    W_lo_packed: list,
    G_conv: int,
) -> dict[tuple, int]:
    """
    Outward-rounded 10**18 integer bounds for all active S0..S3 observables at theta = 1/2:
      - coef_num > 0 (S0, S2): certified lower bound using f_lo_s and emg_lo_s;
      - coef_num < 0 (S1, S3): certified upper bound using F_hi_s and emg_hi_s.
    """
    emg_lo_s, emg_hi_s = consts["exp_mgamma_s"]
    z = edges_f[0]
    z_num, z_den = z.numerator, z.denominator
    pref_lo = (2 * emg_lo_s * z_den) // z_num
    pref_hi = _cdiv(2 * emg_hi_s * z_den, z_num)
    bounds_map: dict[tuple, int] = {}

    for coef_num, spec in terms:
        if spec in bounds_map:
            continue
        kind = spec[0]

        if kind == "S0":
            kz_s0 = spec[1]
            assert coef_num > 0 and kz_s0 >= 0
            z_s0 = edges_f[kz_s0]
            pref_s0_lo = (2 * emg_lo_s * z_s0.denominator) // z_s0.numerator
            s_rat = Fraction(1, 2) / z_s0
            s_lo_s, _ = _fp_rat_iv(s_rat.numerator, s_rat.denominator)
            bounds_map[spec] = (pref_s0_lo * f_lo_s(s_lo_s)) // FP_S

        elif kind == "S1":
            assert coef_num < 0 and spec[2] == 0
            b = spec[1]
            lo_f, hi_f = edges_f[b], edges_f[b + 1]
            n_seg = 4000
            D_u = lo_f.denominator * hi_f.denominator * n_seg
            ua_base = lo_f.numerator * hi_f.denominator * n_seg
            u_step = hi_f.numerator * lo_f.denominator - lo_f.numerator * hi_f.denominator
            s_den = 2 * D_u * z_num
            c0_num = D_u * z_den
            c1_mul = 2 * z_den
            acc_s1_hi = 0
            u0_i = ua_base
            for _ in range(n_seg):
                u1_i = u0_i + u_step
                s_num = c0_num - c1_mul * u1_i
                s_lo_s = (s_num * FP_S) // s_den
                F_val_hi = F_hi_s(s_lo_s)
                ln_hi = _cdiv(u_step * FP_S, u0_i)
                acc_s1_hi += _cdiv(F_val_hi * ln_hi, FP_S)
                u0_i = u1_i
            bounds_map[spec] = _cdiv(pref_hi * acc_s1_hi, FP_S)

        elif kind == "S2":
            assert coef_num > 0 and spec[3] == 0
            b1, b2 = spec[1], spec[2]
            sym_div = 2 if b1 == b2 else 1
            o1, l1, p1 = W_lo_packed[b1]
            o2, l2, p2 = W_lo_packed[b2]
            p12_raw = p1 * p2
            l12 = l1 + l2 - 1
            off12 = o1 + o2
            acc_s2_lo = 0
            cur = p12_raw
            for idx_s in range(l12):
                sl = cur & SLOT_MASK
                cur >>= SLOT_BITS
                if not sl:
                    continue
                w_ij_lo = sl // FP_S
                K_idx = off12 + idx_s
                rem_num = G_conv - 2 * (K_idx + 2)
                if rem_num <= 0:
                    continue
                s_lo_s = (rem_num * z_den * FP_S) // (2 * G_conv * z_num)
                fv_lo = f_lo_s(s_lo_s)
                if fv_lo:
                    acc_s2_lo += (w_ij_lo * fv_lo) // FP_S
            acc_s2_lo //= sym_div
            bounds_map[spec] = (pref_lo * acc_s2_lo) // FP_S

        elif kind == "S3":
            assert coef_num < 0 and spec[4] == 0
            b1, b2, b3 = spec[1], spec[2], spec[3]
            if b1 == b2 == b3:
                sym_div = 6
            elif b1 == b2 or b2 == b3:
                sym_div = 2
            else:
                sym_div = 1

            o1, l1, p1 = W_hi_packed[b1]
            o2, l2, p2 = W_hi_packed[b2]
            o3, l3, p3 = W_hi_packed[b3]
            fp_m1 = FP_S - 1

            p12_raw = p1 * p2
            l12 = l1 + l2 - 1
            p12 = 0
            cur = p12_raw
            for idx_s in range(l12):
                sl = cur & SLOT_MASK
                cur >>= SLOT_BITS
                if sl:
                    p12 |= ((sl + fp_m1) // FP_S) << (idx_s * SLOT_BITS)

            p123_raw = p12 * p3
            l123 = l12 + l3 - 1
            off123 = o1 + o2 + o3
            acc_s3 = 0
            cur = p123_raw
            for idx_s in range(l123):
                sl = cur & SLOT_MASK
                cur >>= SLOT_BITS
                if not sl:
                    continue
                w_ijk_hi = (sl + fp_m1) // FP_S
                K_idx = off123 + idx_s
                rem_num = G_conv - 2 * (K_idx + 3)
                assert rem_num > 0
                s_lo_s = (rem_num * z_den * FP_S) // (2 * G_conv * z_num)
                F_val_hi = F_hi_s(s_lo_s)
                acc_s3 += _cdiv(w_ijk_hi * F_val_hi, FP_S)

            acc_s3 = _cdiv(acc_s3, sym_div)
            bounds_map[spec] = _cdiv(pref_hi * acc_s3, FP_S)

    return bounds_map


# ============================================================================
# 5. Step C: Pure-Integer 10**18 Outward Upper Bounds mu_hi(C) >= mu(C) (r >= 3)
# ============================================================================

def enclose_r3_cell_hi(edges_f: list[Fraction], c: tuple[int, ...], ln_rat_iv, n_sub: int = 3200) -> int:
    """
    Rigorous outward upper bound on mu(C) for r = 3 cell C = (b1, b2, b3):
    clips u_1 to the exact rational active domain, splits at all 6 rational inner-endpoint
    kinks, and bounds the inner log outward on pure-integer scaled sub-intervals.
    """
    b1, b2, b3 = c
    one = Fraction(1, 1)
    half = Fraction(1, 2)
    e2_lo, e2_hi = edges_f[b2], edges_f[b2 + 1]
    e3_lo, e3_hi = edges_f[b3], edges_f[b3 + 1]

    u1_lo = max(edges_f[b1], one - 2 * e3_hi, one - e2_hi - e3_hi)
    u1_hi = min(
        edges_f[b1 + 1],
        Fraction(1, 3),
        e2_hi,
        half * (one - e3_lo),
        one - 2 * e2_lo,
        one - e2_lo - e3_lo,
    )
    if u1_hi <= u1_lo:
        return 0

    kinks = {u1_lo, u1_hi}
    for kp in (
        e2_lo,
        half * (one - e3_hi),
        one - e2_lo - e3_hi,
        one - 2 * e2_hi,
        one - 2 * e3_lo,
        one - e2_hi - e3_lo,
    ):
        if u1_lo < kp < u1_hi:
            kinks.add(kp)
    segs = sorted(kinks)
    tot_w = u1_hi - u1_lo

    base_den = _lcm(_lcm(e2_lo.denominator, e2_hi.denominator), _lcm(e3_lo.denominator, e3_hi.denominator))
    acc_hi = 0
    fp_m1 = FP_S - 1

    for sa, sb in zip(segs[:-1], segs[1:]):
        ratio_f = (sb - sa) / tot_w
        n_loc = max(24, _cdiv(ratio_f.numerator * n_sub, ratio_f.denominator))
        D = _lcm(base_den, _lcm(sa.denominator, sb.denominator)) * n_loc
        sa_i = int(sa * D)
        sb_i = int(sb * D)
        st_i = (sb_i - sa_i) // n_loc
        e2_lo_i = int(e2_lo * D)
        e2_hi_i = int(e2_hi * D)
        e3_lo_i = int(e3_lo * D)
        e3_hi_i = int(e3_hi * D)

        ua_i = sa_i
        for _ in range(n_loc):
            ub_i = ua_i + st_i
            om_ua = D - ua_i
            om_ub = D - ub_i

            m1_n = ua_i if ua_i >= e2_lo_i else e2_lo_i
            m2_n = om_ub - e3_hi_i
            if m1_n * om_ub >= m2_n * om_ua:
                tmin_n, tmin_d = m1_n, om_ua
            else:
                tmin_n, tmin_d = m2_n, om_ub

            tmax_n, tmax_d = 1, 2
            if e2_hi_i * tmax_d < tmax_n * om_ub:
                tmax_n, tmax_d = e2_hi_i, om_ub
            n3_n = om_ua - e3_lo_i
            if n3_n * tmax_d < tmax_n * om_ua:
                tmax_n, tmax_d = n3_n, om_ua

            if tmax_n * tmin_d > tmin_n * tmax_d:
                r_num = tmax_n * (tmin_d - tmin_n)
                r_den = tmin_n * (tmax_d - tmax_n)
                _, ln_in_hi = ln_rat_iv(r_num, r_den)
                inner_hi = (ln_in_hi * D + om_ub - 1) // om_ub
                ln_u1_hi = (st_i * FP_S + ua_i - 1) // ua_i
                acc_hi += (inner_hi * ln_u1_hi + fp_m1) // FP_S
            ua_i = ub_i
    return acc_hi


def enclose_r4plus_cells_dp_hi(
    edges_f: list[Fraction],
    r4_cells: list[tuple[int, ...]],
    W_packed: list,
    G: int,
) -> dict[tuple[int, ...], int]:
    """
    Exact pure-integer 160-bit Kronecker-packed sum-state trie-DP outward upper bound
    mu_hi(C) >= mu(C) for all slacked cells C with 4 <= r <= 13, dividing upward by
    the equal-bin symmetry factorial Gamma(C) = prod_b (count_b(C))!.
    """
    edges_nd = [(e.numerator, e.denominator) for e in edges_f]
    by_prefix = defaultdict(list)
    prefixes_by_len = defaultdict(set)
    for c in r4_cells:
        pref = c[:-1]
        by_prefix[pref].append(c)
        for d in range(1, len(pref) + 1):
            prefixes_by_len[d].add(pref[:d])

    dp_map = {(): (0, 1, FP_S)}
    max_d = max(prefixes_by_len.keys(), default=0)
    fp_m1 = FP_S - 1

    for d in range(1, max_d + 1):
        for pref in sorted(prefixes_by_len[d]):
            off0, len0, pack0 = dp_map[pref[:-1]]
            wb_off, wb_len, wb_pack = W_packed[pref[-1]]
            k_min = off0 + wb_off
            if len0 == 0 or wb_len == 0 or k_min >= G:
                dp_map[pref] = (G, 0, 0)
                continue
            conv_len = min(len0 + wb_len - 1, G - k_min)
            prod = pack0 * wb_pack
            out_pack = 0
            cur = prod
            for idx_s in range(conv_len):
                slot = cur & SLOT_MASK
                cur >>= SLOT_BITS
                if slot:
                    assert slot < (1 << (SLOT_BITS - 4)), "160-bit slot overflow guard"
                    v_hi = (slot + fp_m1) // FP_S
                    out_pack |= v_hi << (idx_s * SLOT_BITS)
            dp_map[pref] = (k_min, conv_len, out_pack)

    res_hi: dict[tuple[int, ...], int] = {}
    for pref, cells_for_pref in by_prefix.items():
        off, clen, pack = dp_map[pref]
        if clen == 0:
            for c in cells_for_pref:
                res_hi[c] = 0
            continue
        arr = [0] * clen
        cur = pack
        for idx_s in range(clen):
            arr[idx_s] = cur & SLOT_MASK
            cur >>= SLOT_BITS

        rm1 = len(pref)
        for c in cells_for_pref:
            br = c[-1]
            ln_r, ld_r = edges_nd[br]
            hn_r, hd_r = edges_nd[br + 1]

            gamma_c = 1
            run = 1
            for j in range(1, len(c)):
                if c[j] == c[j - 1]:
                    run += 1
                else:
                    gamma_c *= _factorial(run)
                    run = 1
            gamma_c *= _factorial(run)

            K_hi = G - 1 - (G * ln_r) // ld_r
            K_lo = G - rm1 + 1 - _cdiv(G * hn_r, hd_r)
            i_start = max(0, K_lo - off)
            i_stop = min(clen - 1, K_hi - off)
            acc = 0
            G_ln = G * ln_r
            for idx_i in range(i_start, i_stop + 1):
                p_val = arr[idx_i]
                if not p_val:
                    continue
                rem_lo = G - (off + idx_i) - rm1
                if G_ln >= rem_lo * ld_r:
                    acc += (p_val * ld_r + ln_r - 1) // ln_r
                else:
                    acc += (p_val * G + rem_lo - 1) // rem_lo
            res_hi[c] = (acc + gamma_c - 1) // gamma_c

    return res_hi


def enclose_all_slacked_measures_hi(
    edges_f: list[Fraction],
    slacked_set: set[tuple[int, ...]],
    ln_rat_iv,
    W_packed_fine: list,
    G_fine: int,
    W_packed_coarse: list,
    G_coarse: int,
) -> dict[tuple[int, ...], int]:
    """Outward upper bounds mu_hi(C) >= mu(C) across all slacked cells (all satisfy r >= 3)."""
    mu_hi_map: dict[tuple[int, ...], int] = {}
    r4_6_list: list[tuple[int, ...]] = []
    r7p_list: list[tuple[int, ...]] = []
    for c in sorted(slacked_set):
        r = len(c)
        assert r >= 3, f"Unexpected r <= 2 slacked cell in D_{{1,2}}: {c}"
        if r == 3:
            mu_hi_map[c] = enclose_r3_cell_hi(edges_f, c, ln_rat_iv, n_sub=3200)
        elif r <= 6:
            r4_6_list.append(c)
        else:
            r7p_list.append(c)
    if r4_6_list:
        mu_hi_map.update(enclose_r4plus_cells_dp_hi(edges_f, r4_6_list, W_packed_fine, G=G_fine))
    if r7p_list:
        mu_hi_map.update(enclose_r4plus_cells_dp_hi(edges_f, r7p_list, W_packed_coarse, G=G_coarse))
    return mu_hi_map


def combine_certified_lower_bound(
    denom: int,
    terms: list[tuple[int, tuple]],
    obs_bounds_s: dict[tuple, int],
    slacked_cells: list[tuple[tuple[int, ...], int]],
    mu_hi_map: dict[tuple[int, ...], int],
    K_sw_exact_s: int,
) -> tuple[int, int, int, int, dict[int, int]]:
    """
    Combines exact rational coefficients (coef_num / denom), outward observable bounds,
    and outward cell measures into a certified pure-integer lower bound at scale FP_S:
      c_cert * FP_S = main_lo_s - slack_cost_hi_s.
    """
    pos_num_acc = 0
    neg_num_acc = 0
    for coef_num, spec in terms:
        bnd_s = obs_bounds_s[spec]
        if coef_num > 0:
            pos_num_acc += coef_num * bnd_s
        else:
            neg_num_acc += (-coef_num) * bnd_s
    main_lo_s = pos_num_acc // denom - _cdiv(neg_num_acc, denom)

    slack_by_r_num: dict[int, int] = defaultdict(int)
    tot_slack_num = 0
    for c, s_num in slacked_cells:
        contrib = s_num * mu_hi_map[c]
        slack_by_r_num[len(c)] += contrib
        tot_slack_num += contrib

    slack_meas_hi_s = _cdiv(tot_slack_num, denom)
    slack_cost_hi_s = _cdiv(K_sw_exact_s * slack_meas_hi_s, FP_S)
    slack_meas_by_r_hi_s = {r: _cdiv(v, denom) for r, v in sorted(slack_by_r_num.items())}
    lb_s = main_lo_s - slack_cost_hi_s
    return lb_s, main_lo_s, slack_meas_hi_s, slack_cost_hi_s, slack_meas_by_r_hi_s


# ============================================================================
# 6. Static Rational Grids, Published Calibration Benchmarks & LP Tables
# ============================================================================

# Benchmark B1: Chen (1973) / Halberstam-Richert (1974, Ch. 11) at z = 1/10, K = 8
# Exact identity: D_{1,2}(N) >= S_0(1/10) - (1/2) * S_1([1/10, 1/3); 1/10) - (1/2) * S_sw,
# subdividing [1/10, 1/3) into 8 uniform bins with identical weight -1/2 (denom = 2).
GRID_CHEN_HR = [
    Fraction(10, 100), Fraction(13, 100), Fraction(16, 100), Fraction(19, 100),
    Fraction(22, 100), Fraction(25, 100), Fraction(28, 100), Fraction(31, 100),
    Fraction(1, 3), Fraction(1, 2), Fraction(1, 1),
]
BENCH_CHEN_HR_DEN = 2
BENCH_CHEN_HR_TERMS = [(2, ("S0", 0))] + [(-1, ("S1", b, 0)) for b in range(8)]

# Benchmark B2: Wu (2008, arXiv:0709.3764, Lemma 2.2 & Sec. 5) 6 direct observables
# at kappa_1 = 100/1327 = 1/13.27, kappa_2 = 25/206 = 1/8.24, sigma = 1/2 - 3*kappa_1 = 727/2654,
# evaluated at pure level 1/2 (K = 8, zero double sieve, zero Fouvry 5/9, denom = 4):
#   (3 * S_0(kappa_1) + 1 * S_0(kappa_2) - 2 * S_1([kappa_1, sigma); kappa_1)
#    - 1 * S_1([sigma, 1/3); kappa_1) + 1 * S_2([kappa_1, kappa_2)^2; kappa_1)
#    + 1 * S_2([kappa_1, kappa_2) x [kappa_2, sigma) cap {u_1+u_2 < 1/2 - 2*kappa_1}; kappa_1)) / 4.
GRID_WU08 = [
    Fraction(100, 1327), Fraction(88, 1000), Fraction(100, 1000), Fraction(111, 1000),
    Fraction(25, 206), Fraction(145, 1000), Fraction(170, 1000), Fraction(195, 1000),
    Fraction(220, 1000), Fraction(247, 1000), Fraction(727, 2654), Fraction(304, 1000),
    Fraction(1, 3), Fraction(1, 2), Fraction(1, 1),
]
BENCH_WU08_DEN = 4
BENCH_WU08_TERMS = (
    [(3, ("S0", 0)), (1, ("S0", 4))]
    + [(-2, ("S1", b, 0)) for b in range(10)]
    + [(-1, ("S1", b, 0)) for b in range(10, 12)]
    + [(1, ("S2", b1, b2, 0)) for b1 in range(4) for b2 in range(b1, 4)]
    + [
        (1, ("S2", b1, b2, 0))
        for b1 in range(4)
        for b2 in range(4, 10)
        if GRID_WU08[b1] + GRID_WU08[b2] < Fraction(1, 2) - 2 * Fraction(100, 1327)
        and GRID_WU08[b1 + 1] + GRID_WU08[b2 + 1] <= Fraction(1, 2) - 2 * Fraction(100, 1327) + Fraction(12, 1000)
    ]
)

GRID_BV22 = [
    Fraction(75, 1000), Fraction(88, 1000), Fraction(105, 1000), Fraction(125, 1000),
    Fraction(147, 1000), Fraction(172, 1000), Fraction(198, 1000), Fraction(224, 1000),
    Fraction(250, 1000), Fraction(285, 1000), Fraction(1, 3), Fraction(380, 1000),
    Fraction(425, 1000), Fraction(464, 1000), Fraction(466, 1000), Fraction(467, 1000),
    Fraction(468, 1000), Fraction(469, 1000), Fraction(471, 1000), Fraction(474, 1000),
    Fraction(1, 2), Fraction(1, 1),
]

GRID_REF18 = [
    Fraction(75, 1000), Fraction(86, 1000), Fraction(98, 1000), Fraction(112, 1000),
    Fraction(128, 1000), Fraction(146, 1000), Fraction(166, 1000), Fraction(188, 1000),
    Fraction(212, 1000), Fraction(238, 1000), Fraction(266, 1000), Fraction(298, 1000),
    Fraction(1, 3), Fraction(375, 1000), Fraction(420, 1000), Fraction(460, 1000),
    Fraction(1, 2), Fraction(1, 1),
]

# 1. D12_BV22_S2: Exact LP vertex on BV22 using S0..S2 ONLY (39 active terms, denom = 672)
D12_BV22_S2_DEN = 672
D12_BV22_S2_TERMS = [
    (672, ("S0", 0)),
    (-434, ("S1", 0, 0)),
    (-432, ("S1", 1, 0)),
    (-430, ("S1", 2, 0)),
    (-426, ("S1", 3, 0)),
    (-407, ("S1", 4, 0)),
    (-384, ("S1", 5, 0)),
    (-288, ("S1", 6, 0)),
    (-265, ("S1", 7, 0)),
    (-246, ("S1", 8, 0)),
    (-240, ("S1", 9, 0)),
    (196, ("S2", 0, 0, 0)),
    (194, ("S2", 0, 1, 0)),
    (192, ("S2", 0, 2, 0)),
    (188, ("S2", 0, 3, 0)),
    (169, ("S2", 0, 4, 0)),
    (146, ("S2", 0, 5, 0)),
    (50, ("S2", 0, 6, 0)),
    (27, ("S2", 0, 7, 0)),
    (8, ("S2", 0, 8, 0)),
    (192, ("S2", 1, 1, 0)),
    (190, ("S2", 1, 2, 0)),
    (186, ("S2", 1, 3, 0)),
    (167, ("S2", 1, 4, 0)),
    (144, ("S2", 1, 5, 0)),
    (48, ("S2", 1, 6, 0)),
    (25, ("S2", 1, 7, 0)),
    (188, ("S2", 2, 2, 0)),
    (184, ("S2", 2, 3, 0)),
    (165, ("S2", 2, 4, 0)),
    (142, ("S2", 2, 5, 0)),
    (46, ("S2", 2, 6, 0)),
    (23, ("S2", 2, 7, 0)),
    (180, ("S2", 3, 3, 0)),
    (161, ("S2", 3, 4, 0)),
    (138, ("S2", 3, 5, 0)),
    (42, ("S2", 3, 6, 0)),
    (142, ("S2", 4, 4, 0)),
    (119, ("S2", 4, 5, 0)),
]

# 2. D12_BV22_S3: Exact LP vertex on BV22 using S0..S3 (58 active terms, denom = 20782)
D12_BV22_S3_DEN = 20782
D12_BV22_S3_TERMS = [
    (20782, ("S0", 0)),
    (-15337, ("S1", 0, 0)),
    (-14590, ("S1", 1, 0)),
    (-13843, ("S1", 2, 0)),
    (-13202, ("S1", 3, 0)),
    (-11708, ("S1", 4, 0)),
    (-10701, ("S1", 5, 0)),
    (-10081, ("S1", 6, 0)),
    (-9074, ("S1", 7, 0)),
    (-7580, ("S1", 8, 0)),
    (-6192, ("S1", 9, 0)),
    (9892, ("S2", 0, 0, 0)),
    (9145, ("S2", 0, 1, 0)),
    (8398, ("S2", 0, 2, 0)),
    (7757, ("S2", 0, 3, 0)),
    (6263, ("S2", 0, 4, 0)),
    (5256, ("S2", 0, 5, 0)),
    (4636, ("S2", 0, 6, 0)),
    (3629, ("S2", 0, 7, 0)),
    (2135, ("S2", 0, 8, 0)),
    (8398, ("S2", 1, 1, 0)),
    (7651, ("S2", 1, 2, 0)),
    (7010, ("S2", 1, 3, 0)),
    (5516, ("S2", 1, 4, 0)),
    (4509, ("S2", 1, 5, 0)),
    (3889, ("S2", 1, 6, 0)),
    (2882, ("S2", 1, 7, 0)),
    (6904, ("S2", 2, 2, 0)),
    (6263, ("S2", 2, 3, 0)),
    (4769, ("S2", 2, 4, 0)),
    (3762, ("S2", 2, 5, 0)),
    (3142, ("S2", 2, 6, 0)),
    (2135, ("S2", 2, 7, 0)),
    (5622, ("S2", 3, 3, 0)),
    (4128, ("S2", 3, 4, 0)),
    (3121, ("S2", 3, 5, 0)),
    (2501, ("S2", 3, 6, 0)),
    (2634, ("S2", 4, 4, 0)),
    (1627, ("S2", 4, 5, 0)),
    (-5924, ("S3", 0, 0, 0, 0)),
    (-5002, ("S3", 0, 0, 1, 0)),
    (-4760, ("S3", 0, 0, 2, 0)),
    (-4004, ("S3", 0, 0, 3, 0)),
    (-2256, ("S3", 0, 0, 4, 0)),
    (-4827, ("S3", 0, 1, 1, 0)),
    (-3792, ("S3", 0, 1, 2, 0)),
    (-3224, ("S3", 0, 1, 3, 0)),
    (-1388, ("S3", 0, 1, 4, 0)),
    (-2872, ("S3", 0, 2, 2, 0)),
    (-2256, ("S3", 0, 2, 3, 0)),
    (-974, ("S3", 0, 3, 3, 0)),
    (-3792, ("S3", 1, 1, 1, 0)),
    (-2901, ("S3", 1, 1, 2, 0)),
    (-2108, ("S3", 1, 1, 3, 0)),
    (-165, ("S3", 1, 1, 4, 0)),
    (-2044, ("S3", 1, 2, 2, 0)),
    (-762, ("S3", 1, 2, 3, 0)),
    (-1206, ("S3", 2, 2, 2, 0)),
]

# 3. D12_REF18_S3: Rationalized LP identity on REF18 using S0..S3 (87 active terms, denom = 24000)
D12_REF18_S3_DEN = 24000
D12_REF18_S3_TERMS = [
    (24000, ("S0", 0)),
    (-17790, ("S1", 0, 0)),
    (-17073, ("S1", 1, 0)),
    (-16507, ("S1", 2, 0)),
    (-15854, ("S1", 3, 0)),
    (-14680, ("S1", 4, 0)),
    (-13766, ("S1", 5, 0)),
    (-12852, ("S1", 6, 0)),
    (-12000, ("S1", 7, 0)),
    (-11149, ("S1", 8, 0)),
    (-9321, ("S1", 9, 0)),
    (-8147, ("S1", 10, 0)),
    (-6928, ("S1", 11, 0)),
    (11580, ("S2", 0, 0, 0)),
    (10863, ("S2", 0, 1, 0)),
    (10296, ("S2", 0, 2, 0)),
    (9644, ("S2", 0, 3, 0)),
    (8469, ("S2", 0, 4, 0)),
    (7555, ("S2", 0, 5, 0)),
    (6642, ("S2", 0, 6, 0)),
    (5790, ("S2", 0, 7, 0)),
    (4938, ("S2", 0, 8, 0)),
    (3111, ("S2", 0, 9, 0)),
    (10145, ("S2", 1, 1, 0)),
    (9579, ("S2", 1, 2, 0)),
    (8927, ("S2", 1, 3, 0)),
    (7752, ("S2", 1, 4, 0)),
    (6838, ("S2", 1, 5, 0)),
    (5925, ("S2", 1, 6, 0)),
    (5073, ("S2", 1, 7, 0)),
    (4221, ("S2", 1, 8, 0)),
    (2394, ("S2", 1, 9, 0)),
    (9012, ("S2", 2, 2, 0)),
    (8360, ("S2", 2, 3, 0)),
    (7185, ("S2", 2, 4, 0)),
    (6272, ("S2", 2, 5, 0)),
    (5358, ("S2", 2, 6, 0)),
    (4506, ("S2", 2, 7, 0)),
    (3654, ("S2", 2, 8, 0)),
    (7708, ("S2", 3, 3, 0)),
    (6533, ("S2", 3, 4, 0)),
    (5619, ("S2", 3, 5, 0)),
    (4706, ("S2", 3, 6, 0)),
    (3854, ("S2", 3, 7, 0)),
    (3002, ("S2", 3, 8, 0)),
    (5358, ("S2", 4, 4, 0)),
    (4445, ("S2", 4, 5, 0)),
    (3531, ("S2", 4, 6, 0)),
    (2679, ("S2", 4, 7, 0)),
    (3531, ("S2", 5, 5, 0)),
    (2617, ("S2", 5, 6, 0)),
    (-6765, ("S3", 0, 0, 0, 0)),
    (-5822, ("S3", 0, 0, 1, 0)),
    (-5547, ("S3", 0, 0, 2, 0)),
    (-5163, ("S3", 0, 0, 3, 0)),
    (-4329, ("S3", 0, 0, 4, 0)),
    (-2502, ("S3", 0, 0, 5, 0)),
    (-1893, ("S3", 0, 0, 6, 0)),
    (-5511, ("S3", 0, 1, 1, 0)),
    (-5034, ("S3", 0, 1, 2, 0)),
    (-4479, ("S3", 0, 1, 3, 0)),
    (-3083, ("S3", 0, 1, 4, 0)),
    (-2394, ("S3", 0, 1, 5, 0)),
    (-566, ("S3", 0, 1, 6, 0)),
    (-4093, ("S3", 0, 2, 2, 0)),
    (-4300, ("S3", 0, 2, 3, 0)),
    (-2891, ("S3", 0, 2, 4, 0)),
    (-1827, ("S3", 0, 2, 5, 0)),
    (-2995, ("S3", 0, 3, 3, 0)),
    (-2313, ("S3", 0, 3, 4, 0)),
    (-522, ("S3", 0, 3, 5, 0)),
    (-5254, ("S3", 1, 1, 1, 0)),
    (-3890, ("S3", 1, 1, 2, 0)),
    (-3999, ("S3", 1, 1, 3, 0)),
    (-2627, ("S3", 1, 1, 4, 0)),
    (-1526, ("S3", 1, 1, 5, 0)),
    (-4170, ("S3", 1, 2, 2, 0)),
    (-2866, ("S3", 1, 2, 3, 0)),
    (-2136, ("S3", 1, 2, 4, 0)),
    (-393, ("S3", 1, 2, 5, 0)),
    (-2886, ("S3", 1, 3, 3, 0)),
    (-915, ("S3", 1, 3, 4, 0)),
    (-3037, ("S3", 2, 2, 2, 0)),
    (-2569, ("S3", 2, 2, 3, 0)),
    (-1087, ("S3", 2, 2, 4, 0)),
    (-1956, ("S3", 2, 3, 3, 0)),
    (-191, ("S3", 3, 3, 3, 0)),
]


# ============================================================================
# 7. Main Certification Driver
# ============================================================================

def main() -> None:
    t0_ns = time.perf_counter_ns()
    fl_lit, fl_call, bad_imp = audit_ast_zero_float()

    print("=== Standalone 10**18 Pure-Integer Certification of Direct D_{1,2}(N) at Level 1/2 (K = 8) ===")
    print(f"  [AST Audit] float/complex literals = {fl_lit} | float()/complex() calls = {fl_call} | math/numpy/scipy imports = {bad_imp} [PASS]")
    print("  [Normalisation] Theta(N) = C(N) * N / (log N)^2  (matching Chen 1973, Wu 2004, Wu 2008, Runbo Li 2026)")

    ln_rat_iv_g, ln_rat_iv, consts = build_pure_int_math()
    gam_lo, gam_hi = consts["gamma_s"]
    emg_lo, emg_hi = consts["exp_mgamma_s"]
    print(f"  [Constants] gamma   in [{_fp_fmt(gam_lo, 15, mode='floor')}, {_fp_fmt(gam_hi, 15, mode='ceil')}] (width = {gam_hi - gam_lo}e-18)")
    print(f"  [Constants] e^-gam  in [{_fp_fmt(emg_lo, 15, mode='floor')}, {_fp_fmt(emg_hi, 15, mode='ceil')}] (width = {emg_hi - emg_lo}e-18)")

    F_hi_s, f_lo_s, ode_meta = build_fp_ode_enclosures(ln_rat_iv_g, consts, M=600, K_MAX=20)
    print(f"  [Delay ODE] M = 600 on s in [1, 20]: F(20) <= {_fp_fmt(ode_meta['F20_hi_s'], 15, mode='ceil')}, f(20) >= {_fp_fmt(ode_meta['f20_lo_s'], 15, mode='floor')}")

    K_BV_exact = 8 * FP_S
    G_FINE = 18000
    G_COARSE = 4500

    # ------------------------------------------------------------------------
    # BENCHMARK B1: Chen (1973) / Halberstam-Richert (1974) at z = 1/10, K = 8
    # ------------------------------------------------------------------------
    t_ch = time.perf_counter_ns()
    dom_ch = verify_d12_observable_domains(GRID_CHEN_HR, BENCH_CHEN_HR_TERMS, allow_s3=False)
    cfgs_ch, bdry_ch = enumerate_configs_exact(GRID_CHEN_HR)
    assert len(cfgs_ch) == 845 and len(bdry_ch) == 21
    step_a_ch = step_a_verify_pointwise_d12(cfgs_ch, bdry_ch, BENCH_CHEN_HR_DEN, BENCH_CHEN_HR_TERMS)
    W_ch_hi, W_ch_lo = build_bin_grid_weights_hi_lo(GRID_CHEN_HR, ln_rat_iv, G=G_FINE)
    W_ch_hi_c, _ = build_bin_grid_weights_hi_lo(GRID_CHEN_HR, ln_rat_iv, G=G_COARSE)
    obs_b_ch = step_b_enclose_bv_observables(
        GRID_CHEN_HR, BENCH_CHEN_HR_TERMS, consts, F_hi_s, f_lo_s,
        W_hi_packed=W_ch_hi, W_lo_packed=W_ch_lo, G_conv=G_FINE,
    )
    sl_set_ch = {c for c, _ in step_a_ch["slacked_cells"]}
    mu_hi_ch = enclose_all_slacked_measures_hi(GRID_CHEN_HR, sl_set_ch, ln_rat_iv, W_ch_hi, G_FINE, W_ch_hi_c, G_COARSE)
    lb_ch, main_ch, sm_ch, sc_ch, smr_ch = combine_certified_lower_bound(
        BENCH_CHEN_HR_DEN, BENCH_CHEN_HR_TERMS, obs_b_ch, step_a_ch["slacked_cells"], mu_hi_ch, K_BV_exact
    )
    dt_ch_ms = (time.perf_counter_ns() - t_ch) // 1_000_000
    assert lb_ch >= 689065 * (10 ** 12), f"BENCH_CHEN_HR_1973 LB below +0.689065: {lb_ch}"

    print(f"\n--- B1. BENCH_CHEN_HR_1973 (Chen 1973 / Halberstam-Richert 1974, z = 1/10, K = 8, w = -1/2 on [1/10, 1/3), {len(cfgs_ch)}+{len(bdry_ch)} cells) ({dt_ch_ms} ms) ---")
    print(f"  Observable counts: {dom_ch['counts_by_kind']} | min sieve arg s by kind: { {k: str(v) for k, v in dom_ch['min_s_by_kind'].items()} }")
    print(f"  Step A (r = 1..10 complete DFS): violations = {step_a_ch['violations']}, r <= 2 slacked = {step_a_ch['r2_slacked']}, slacked by r = {step_a_ch['slacked_counts_by_r']} (r >= 4 slacked = 0)")
    print(f"  Step B/C: S0(1/10) >= {_fp_fmt(obs_b_ch[('S0', 0)], 6, mode='floor')} | main >= {_fp_fmt(main_ch, 6, mode='floor')} | slack_meas <= {_fp_fmt(sm_ch, 6, mode='ceil')} | 8*slack <= {_fp_fmt(sc_ch, 6, mode='ceil')}")
    print(f"  ==> BENCHMARK CERTIFIED D_{{1,2}}(N) >= {_fp_fmt(lb_ch, 6, signed=True, mode='floor')} * Theta(N)  [PASS >= +0.689065; HR 1974 published: 0.689]")

    # ------------------------------------------------------------------------
    # BENCHMARK B2: Wu (2008, arXiv:0709.3764, Lemma 2.2) at pure K = 8 (no DS)
    # ------------------------------------------------------------------------
    t_wu = time.perf_counter_ns()
    dom_wu = verify_d12_observable_domains(GRID_WU08, BENCH_WU08_TERMS, allow_s3=False)
    cfgs_wu, bdry_wu = enumerate_configs_exact(GRID_WU08)
    assert len(cfgs_wu) > 0 and len(bdry_wu) >= 0
    step_a_wu = step_a_verify_pointwise_d12(cfgs_wu, bdry_wu, BENCH_WU08_DEN, BENCH_WU08_TERMS)
    W_wu_hi, W_wu_lo = build_bin_grid_weights_hi_lo(GRID_WU08, ln_rat_iv, G=G_FINE)
    W_wu_hi_c, _ = build_bin_grid_weights_hi_lo(GRID_WU08, ln_rat_iv, G=G_COARSE)
    obs_b_wu = step_b_enclose_bv_observables(
        GRID_WU08, BENCH_WU08_TERMS, consts, F_hi_s, f_lo_s,
        W_hi_packed=W_wu_hi, W_lo_packed=W_wu_lo, G_conv=G_FINE,
    )
    sl_set_wu = {c for c, _ in step_a_wu["slacked_cells"]}
    mu_hi_wu = enclose_all_slacked_measures_hi(GRID_WU08, sl_set_wu, ln_rat_iv, W_wu_hi, G_FINE, W_wu_hi_c, G_COARSE)
    lb_wu, main_wu, sm_wu, sc_wu, smr_wu = combine_certified_lower_bound(
        BENCH_WU08_DEN, BENCH_WU08_TERMS, obs_b_wu, step_a_wu["slacked_cells"], mu_hi_wu, K_BV_exact
    )
    dt_wu_ms = (time.perf_counter_ns() - t_wu) // 1_000_000
    assert lb_wu >= 877232 * (10 ** 12), f"BENCH_WU08_PURE_K8 LB below +0.877232: {lb_wu}"

    print(f"\n--- B2. BENCH_WU08_PURE_K8 (Wu 2008 Lemma 2.2 weights, kappa_1=100/1327, kappa_2=25/206, pure K = 8, no DS, {len(cfgs_wu)}+{len(bdry_wu)} cells) ({dt_wu_ms} ms) ---")
    print(f"  Observable counts: {dom_wu['counts_by_kind']} | S0(kappa_1) >= {_fp_fmt(obs_b_wu[('S0', 0)], 6, mode='floor')} (Wu: 14.900897) | S0(kappa_2) >= {_fp_fmt(obs_b_wu[('S0', 4)], 6, mode='floor')} (Wu: 9.103015)")
    print(f"  Step A (r = 1..13 complete DFS): violations = {step_a_wu['violations']}, r <= 2 slacked = {step_a_wu['r2_slacked']}, r = 4 max W_dir = {step_a_wu['max_w_by_r'][4]}")
    print(f"  Step C slack measure ub by r: { {r: _fp_fmt(v, 6, mode='ceil') for r, v in smr_wu.items() if v > 10**12} } (Wu exact r=3: 0.370056)")
    print(f"  Step B/C: main >= {_fp_fmt(main_wu, 6, mode='floor')} | slack_meas <= {_fp_fmt(sm_wu, 6, mode='ceil')} | 8*slack <= {_fp_fmt(sc_wu, 6, mode='ceil')}")
    print(f"  ==> BENCHMARK CERTIFIED D_{{1,2}}(N) >= {_fp_fmt(lb_wu, 6, signed=True, mode='floor')} * Theta(N)  [PASS >= +0.877232; +0.0149 over Wu pure-K=8 0.862327 via exact r>=5 cell slack]")

    # ------------------------------------------------------------------------
    # GRID 1: BV22 (22 edges, z = 3/40) -- D12_BV22_S2 & D12_BV22_S3
    # ------------------------------------------------------------------------
    t_bv22 = time.perf_counter_ns()
    dom_s2 = verify_d12_observable_domains(GRID_BV22, D12_BV22_S2_TERMS, allow_s3=False)
    dom_s3 = verify_d12_observable_domains(GRID_BV22, D12_BV22_S3_TERMS, allow_s3=True)
    cfgs_bv22, bdry_bv22 = enumerate_configs_exact(GRID_BV22)
    assert len(cfgs_bv22) == 10702 and len(bdry_bv22) == 46

    step_a_s2 = step_a_verify_pointwise_d12(cfgs_bv22, bdry_bv22, D12_BV22_S2_DEN, D12_BV22_S2_TERMS)
    step_a_s3 = step_a_verify_pointwise_d12(cfgs_bv22, bdry_bv22, D12_BV22_S3_DEN, D12_BV22_S3_TERMS)

    W22_hi, W22_lo = build_bin_grid_weights_hi_lo(GRID_BV22, ln_rat_iv, G=G_FINE)
    W22_hi_c, _ = build_bin_grid_weights_hi_lo(GRID_BV22, ln_rat_iv, G=G_COARSE)
    obs_b_22 = step_b_enclose_bv_observables(
        GRID_BV22, D12_BV22_S2_TERMS + D12_BV22_S3_TERMS, consts, F_hi_s, f_lo_s,
        W_hi_packed=W22_hi, W_lo_packed=W22_lo, G_conv=G_FINE,
    )
    sl_set_22 = {c for c, _ in step_a_s2["slacked_cells"]} | {c for c, _ in step_a_s3["slacked_cells"]}
    mu_hi_22 = enclose_all_slacked_measures_hi(GRID_BV22, sl_set_22, ln_rat_iv, W22_hi, G_FINE, W22_hi_c, G_COARSE)

    lb_22_s2, main_22_s2, sm_22_s2, sc_22_s2, smr_22_s2 = combine_certified_lower_bound(
        D12_BV22_S2_DEN, D12_BV22_S2_TERMS, obs_b_22, step_a_s2["slacked_cells"], mu_hi_22, K_BV_exact
    )
    lb_22_s3, main_22_s3, sm_22_s3, sc_22_s3, smr_22_s3 = combine_certified_lower_bound(
        D12_BV22_S3_DEN, D12_BV22_S3_TERMS, obs_b_22, step_a_s3["slacked_cells"], mu_hi_22, K_BV_exact
    )
    dt_bv22_ms = (time.perf_counter_ns() - t_bv22) // 1_000_000
    assert lb_22_s2 >= 930457 * (10 ** 12), f"D12_BV22_S2 LB below +0.930457: {lb_22_s2}"
    assert lb_22_s3 >= 958320 * (10 ** 12), f"D12_BV22_S3 LB below +0.958320: {lb_22_s3}"
    assert step_a_s2["max_w_by_r"][4] <= 0 and step_a_s3["max_w_by_r"][4] <= 0
    assert all(step_a_s3["max_w_by_r"][r] <= 0 for r in range(10, 14))

    print(f"\n--- 1. D12_BV22_S2 (S0..S2 ONLY, z = 3/40, 22 edges, {len(cfgs_bv22)}+{len(bdry_bv22)} cells, 39 terms, denom = 672) (shared {dt_bv22_ms} ms) ---")
    print(f"  Observable counts: {dom_s2['counts_by_kind']} | min sieve arg s by kind: { {k: str(v) for k, v in dom_s2['min_s_by_kind'].items()} }")
    print(f"  Step A (r = 1..13 complete DFS): violations = {step_a_s2['violations']}, r <= 2 slacked = {step_a_s2['r2_slacked']}, bdry checked = {step_a_s2['bdry_checked']} (r=4 max W_dir = {step_a_s2['max_w_by_r'][4]})")
    print(f"  Step A r = 2 weight range: W_dir in [{step_a_s2['min_w_r2']}, {step_a_s2['max_w_r2']}] (all <= 1, s_C = 0)")
    print(f"  Step A slacked cells by r (all r >= 3): {step_a_s2['slacked_counts_by_r']} (total = {len(step_a_s2['slacked_cells'])})")
    print(f"  Step C slack measure ub by r: { {r: _fp_fmt(v, 6, mode='ceil') for r, v in smr_22_s2.items() if v > 10**12} }")
    print(f"  Step B/C: main >= {_fp_fmt(main_22_s2, 6, mode='floor')} | slack_meas <= {_fp_fmt(sm_22_s2, 6, mode='ceil')} | 8*slack <= {_fp_fmt(sc_22_s2, 6, mode='ceil')}")
    print(f"  ==> CERTIFIED D_{{1,2}}(N) >= {_fp_fmt(lb_22_s2, 6, signed=True, mode='floor')} * Theta(N)  [PASS >= +0.930457, S0..S2 only]")

    print(f"\n--- 2. D12_BV22_S3 (S0..S3, z = 3/40, 22 edges, {len(cfgs_bv22)}+{len(bdry_bv22)} cells, 58 terms, denom = 20782) ---")
    print(f"  Observable counts: {dom_s3['counts_by_kind']} | min sieve arg s by kind: { {k: str(v) for k, v in dom_s3['min_s_by_kind'].items()} }")
    print(f"  Step A (r = 1..13 complete DFS): violations = {step_a_s3['violations']}, r <= 2 slacked = {step_a_s3['r2_slacked']}, bdry checked = {step_a_s3['bdry_checked']} (r=4 max W_dir = {step_a_s3['max_w_by_r'][4]}, r>=10 max W_dir = {max(step_a_s3['max_w_by_r'][r] for r in range(10, 14))})")
    print(f"  Step A r = 2 weight range: W_dir in [{step_a_s3['min_w_r2']}, {step_a_s3['max_w_r2']}] (all <= 1, s_C = 0)")
    print(f"  Step A slacked cells by r (all r >= 3): {step_a_s3['slacked_counts_by_r']} (total = {len(step_a_s3['slacked_cells'])})")
    print(f"  Step C slack measure ub by r: { {r: _fp_fmt(v, 6, mode='ceil') for r, v in smr_22_s3.items() if v > 10**12} }")
    print(f"  Step B/C: main >= {_fp_fmt(main_22_s3, 6, mode='floor')} | slack_meas <= {_fp_fmt(sm_22_s3, 6, mode='ceil')} | 8*slack <= {_fp_fmt(sc_22_s3, 6, mode='ceil')}")
    print(f"  ==> CERTIFIED D_{{1,2}}(N) >= {_fp_fmt(lb_22_s3, 6, signed=True, mode='floor')} * Theta(N)  [PASS >= +0.958320]")

    # Verify exact conversion to tau = 471/1000 (a = 1000/529):
    _, ln_529_471_hi = ln_rat_iv(529, 471)
    conv_cost_hi = 8 * ln_529_471_hi
    d1a_from_d12_lo = lb_22_s3 - conv_cost_hi
    assert d1a_from_d12_lo >= 29278 * (10 ** 12), f"BV22 D_{{1,a}} LB below +0.029278: {d1a_from_d12_lo}"
    print(f"  [Conversion Check] 8*ln(529/471) <= {_fp_fmt(conv_cost_hi, 6, mode='ceil')} ==> D_{{1, 1000/529}}(N) >= {_fp_fmt(d1a_from_d12_lo, 6, signed=True, mode='floor')} * Theta(N) [PASS >= +0.029278]")

    # ------------------------------------------------------------------------
    # GRID 2: REF18 (18 edges, z = 3/40) -- D12_REF18_S3
    # ------------------------------------------------------------------------
    t_ref18 = time.perf_counter_ns()
    dom_ref = verify_d12_observable_domains(GRID_REF18, D12_REF18_S3_TERMS, allow_s3=True)
    cfgs_ref18, bdry_ref18 = enumerate_configs_exact(GRID_REF18)
    assert len(cfgs_ref18) == 21280 and len(bdry_ref18) == 176

    step_a_ref = step_a_verify_pointwise_d12(cfgs_ref18, bdry_ref18, D12_REF18_S3_DEN, D12_REF18_S3_TERMS)
    W18_hi, W18_lo = build_bin_grid_weights_hi_lo(GRID_REF18, ln_rat_iv, G=G_FINE)
    W18_hi_c, _ = build_bin_grid_weights_hi_lo(GRID_REF18, ln_rat_iv, G=G_COARSE)
    obs_b_18 = step_b_enclose_bv_observables(
        GRID_REF18, D12_REF18_S3_TERMS, consts, F_hi_s, f_lo_s,
        W_hi_packed=W18_hi, W_lo_packed=W18_lo, G_conv=G_FINE,
    )
    sl_set_18 = {c for c, _ in step_a_ref["slacked_cells"]}
    mu_hi_18 = enclose_all_slacked_measures_hi(GRID_REF18, sl_set_18, ln_rat_iv, W18_hi, G_FINE, W18_hi_c, G_COARSE)

    lb_18_s3, main_18_s3, sm_18_s3, sc_18_s3, smr_18_s3 = combine_certified_lower_bound(
        D12_REF18_S3_DEN, D12_REF18_S3_TERMS, obs_b_18, step_a_ref["slacked_cells"], mu_hi_18, K_BV_exact
    )
    dt_ref18_ms = (time.perf_counter_ns() - t_ref18) // 1_000_000
    assert lb_18_s3 >= 961226 * (10 ** 12), f"D12_REF18_S3 LB below +0.961226: {lb_18_s3}"
    assert step_a_ref["max_w_by_r"][4] <= 0 and all(step_a_ref["max_w_by_r"][r] <= 0 for r in range(10, 14))

    print(f"\n--- 3. D12_REF18_S3 (S0..S3, z = 3/40, 18 edges, {len(cfgs_ref18)}+{len(bdry_ref18)} cells, 87 terms, denom = 24000) ({dt_ref18_ms} ms) ---")
    print(f"  Observable counts: {dom_ref['counts_by_kind']} | min sieve arg s by kind: { {k: str(v) for k, v in dom_ref['min_s_by_kind'].items()} }")
    print(f"  Step A (r = 1..13 complete DFS): violations = {step_a_ref['violations']}, r <= 2 slacked = {step_a_ref['r2_slacked']}, bdry checked = {step_a_ref['bdry_checked']} (r=4 max W_dir = {step_a_ref['max_w_by_r'][4]}, r>=10 max W_dir = {max(step_a_ref['max_w_by_r'][r] for r in range(10, 14))})")
    print(f"  Step A r = 2 weight range: W_dir in [{step_a_ref['min_w_r2']}, {step_a_ref['max_w_r2']}] (all <= 1, s_C = 0)")
    print(f"  Step A slacked cells by r (all r >= 3): {step_a_ref['slacked_counts_by_r']} (total = {len(step_a_ref['slacked_cells'])})")
    print(f"  Step C slack measure ub by r: { {r: _fp_fmt(v, 6, mode='ceil') for r, v in smr_18_s3.items() if v > 10**12} }")
    print(f"  Step B/C: main >= {_fp_fmt(main_18_s3, 6, mode='floor')} | slack_meas <= {_fp_fmt(sm_18_s3, 6, mode='ceil')} | 8*slack <= {_fp_fmt(sc_18_s3, 6, mode='ceil')}")
    print(f"  ==> CERTIFIED D_{{1,2}}(N) >= {_fp_fmt(lb_18_s3, 6, signed=True, mode='floor')} * Theta(N)  [PASS >= +0.961226]")

    d1a_ref18_lo = lb_18_s3 - conv_cost_hi
    assert d1a_ref18_lo >= 32184 * (10 ** 12), f"REF18 D_{{1,a}} LB below +0.032184: {d1a_ref18_lo}"
    print(f"  [Sub-Cell Conversion Check] At tau = 471/1000: D_{{1, 1000/529}}(N) >= {_fp_fmt(d1a_ref18_lo, 6, signed=True, mode='floor')} * Theta(N) [PASS >= +0.032184]")

    tot_cs = (time.perf_counter_ns() - t0_ns) // 10_000_000
    print(f"\n=== ALL 2 BENCHMARKS + 3 DIRECT D_{{1,2}} IDENTITIES CERTIFIED | Total runtime: {tot_cs // 100}.{tot_cs % 100:02d}s | IEEE-754 floats used: 0 ===")


if __name__ == "__main__":
    main()
