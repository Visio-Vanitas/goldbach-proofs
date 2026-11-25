# Effective Switched-Sieve Bounds, Grid-LP Certificates, and Route Diagnostics

This diagnostic note and the four formal proof files in `lean/PEqualNP/Outside/` accompany the roadmap supplement submitted against `research/ROADMAP.md`. All results here are for independent mathematical review and audit; they do not alter the frozen statements in `research/gaps.json` without maintainer review.

## 1. Upstream GRH Premise & Scope

Following the upstream Lean 4.33.1 formalization of the Riemann Hypothesis and Dirichlet GRH by Alpöge [1] (in collaboration with Claude; commit `dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9`, `src/Main.lean` theorems `riemannHypothesis` and `LFunction_eq_zero_re`, independently kernel-replayed by Sutherland [10]), all non-trivial zeros of Dirichlet $L$-functions lie on $\Re(s)=1/2$, eliminating Siegel zeros and ineffective implied constants [5]. In this project's `Lean 4.36.0` propositions (`research/gaps.json`), upstream zero-location hypotheses remain explicit assumptions until the upstream library is ported to `v4.36.0`.

## 2. Summary of Verified Components & Reproducibility

1. **Pure-Integer Certification at Level $1/2$ (`certify_d12_level_half.py`)**
   - Uses Python 3 standard-library exact integer and rational arithmetic (`0` IEEE-754 floats, verified at runtime via AST inspection; fixed-point scale $10^{18}$, guard scale $10^{24}$), grounded in the Rosser–Iwaniec linear sieve [7, 11] and Pan–Ding weighted mean-value setup [11, Lemma 2.3].
   - Reproduces Chen–Halberstam–Richert (`0.689065` vs `0.689` [4, 6]) and Wu [12, Lemma 2.2] (pure `$K=8$`: `$0.877232$`) under the same evaluator, isolating the printed vs integrated discrepancy on $F_{11}$ (`0.543858` at eq. `(5.6)`/`§5` vs `0.576185`) in Wu [12].
   - Certifies $D_{1,2}(N) \ge 0.961226\,\Theta(N)$ at pure level $1/2$ ($K = 8$, $z = 3/40$) on an 18-edge partition (`D12_REF18_S3`) and $D_{1,2}(N) \ge 0.958320\,\Theta(N)$ on `D12_BV22_S3`, without double-sieving or dispersion levels [8] or explicit sieve remainder tracking [2, 3, 9].
   - Reproduction command from repository root:
     ```bash
     python3 research/diagnostics/certify_d12_level_half.py
     ```

2. **Four Companion Lean 4.36.0 Proofs (`lean/PEqualNP/Outside/`)**
   Each proof imports only `Mathlib`, avoids `sorry` / custom axioms / `native_decide`, and passes both `.github/scripts/outside-guard.mjs` and `tools/check-lean.mjs`:
   - `PEqualNP.Outside.L_goldbach_u1n_lorentz_reflection` (`TH-0092`, `theta-reflection`): indefinite unitary $U(N-1,1)$ discrete Fourier pairing identity and spacelike norm criterion.
   - `PEqualNP.Outside.L_goldbach_separable_kernel_phase_barrier` (`OC-0102`, `odd-character-interference`): off-diagonal square completion showing rank-2 separable zero-pair weights cancel sum phases and settle at $-\sum (\|W_1\|^2 + \|W_2\|^2)$.
   - `PEqualNP.Outside.L_goldbach_cell_lp_dual_certificate` (`representations`): finite cell linear-programming dual certificate with switched slack bound.
   - `PEqualNP.Outside.L_goldbach_moving_cutoff_freeze_budget` (`rh-moving-weights`): moving-cutoff bin-freezing triangle bound and square-root bin cardinality Cauchy–Schwarz budget.

## 3. References

1. L. Alpöge, *[Announcement of the Lean formalization of the Riemann Hypothesis and GRH for Dirichlet $L$-functions]* (in collaboration with Claude), note dated November 20, 2026, <https://alpo.ge/remark.pdf>; Lean 4 repository `leanprover-community/riemann-hypothesis`, commit `dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9`.
2. M. Bordignon and V. Starichkova, *An explicit version of Chen's theorem assuming the Generalized Riemann Hypothesis*, *Ramanujan J.* **64** (2024), no. 4, 1213–1242, doi: `10.1007/s11139-024-00866-x`, `arXiv:2211.08844v1`.
3. M. Bordignon, D. R. Johnston, and V. Starichkova, *An explicit version of Chen's theorem and the linear sieve*, *Int. J. Number Theory* **21** (2025), no. 10, 2497–2572, doi: `10.1142/S1793042125501192`, `arXiv:2207.09452v6`.
4. J. R. Chen, *On the representation of a larger even integer as the sum of a prime and the product of at most two primes*, *Sci. Sinica* **16** (1973), no. 2, 157–176.
5. H. Davenport, *Multiplicative Number Theory*, 3rd ed., rev. by H. L. Montgomery, Grad. Texts in Math., vol. **74**, Springer-Verlag, New York, 2000, ISBN `978-0-387-95097-6`.
6. H. Halberstam and H.-E. Richert, *Sieve Methods*, London Math. Soc. Monographs, No. **4**, Academic Press, London–New York, 1974, ISBN `978-0-12-318250-0`.
7. H. Iwaniec, *A new form of the error term in the linear sieve*, *Acta Arith.* **37** (1980), 307–320, doi: `10.4064/aa-37-1-307-320`.
8. J. D. Lichtman (with an appendix by S. Drappeau), *Primes in arithmetic progressions to large moduli, and Goldbach beyond the square-root barrier*, preprint (2023), `arXiv:2309.08522v1`, doi: `10.48550/arXiv.2309.08522`.
9. G. Lü, Z. Wang, and J. Wu, *On the Hardy–Littlewood–Chowla conjecture*, preprint (2026), `arXiv:2610.20242v2`.
10. A. V. Sutherland, *Verification files for the Lean proof of the Riemann Hypothesis*, MIT verification archive (updated November 24, 2026), <https://math.mit.edu/~drew/grh/>.
11. J. Wu, *Chen's double sieve, Goldbach's conjecture and the twin prime problem*, *Acta Arith.* **114** (2004), no. 3, 215–273, doi: `10.4064/aa114-3-2`, `arXiv:0705.1652v1`.
12. J. Wu, *Chen's double sieve, Goldbach's conjecture and the twin prime problem, 2*, *Acta Arith.* **131** (2008), no. 4, 367–387, doi: `10.4064/aa131-4-5`, `arXiv:0709.3764v1`.
