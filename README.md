# Machine-Checked SKQD Convergence in Lean

[![Lean CI](https://github.com/samarth777/skqd-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/samarth777/skqd-lean/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.0-blue)](https://github.com/leanprover-community/mathlib4)

A Lean 4 formalization of the ideal convergence guarantee for
**Sample-based Krylov Quantum Diagonalization (SKQD)** from:

> J. Yu et al., [*Sample-based Krylov Quantum Diagonalization*](https://arxiv.org/abs/2501.09702),
> arXiv:2501.09702v1 (2025).

The development machine-checks the mathematical argument in Section III and
Appendices A–B: construction of the low-energy Krylov state, transfer of energy
error to state error and sparsity, recovery of important basis strings by
independent Born sampling, and the final variational energy guarantee.

## Main result

Let $H$ have normalized ground state $\lvert\phi_0\rangle$, ground energy
$E_0$, spectral gap $\Delta>0$, and bandwidth at most $W$. Let the normalized
reference state $\lvert\psi_0\rangle$ have squared ground overlap

$$
g=\left\lvert\langle\phi_0\mid\psi_0\rangle\right\rvert^2>0.
$$

For Krylov dimension $d$, define the preceding odd dimension

$$
d_{\mathrm{eff}}
=2\left\lfloor\frac{d-1}{2}\right\rfloor+1
$$

and the KQD error bound

$$
\varepsilon
=8W\frac{1-g}{g}
\left(1+\frac{\pi\Delta}{W}\right)^{-(d_{\mathrm{eff}}-1)}.
$$

If the ground state is $(\alpha,\beta)$-sparse on $L$ important computational
basis strings, set

$$
\widetilde\varepsilon
=2\left(1-\sqrt{1-\frac{\varepsilon}{\Delta}}\right).
$$

Under the paper's parameter conditions and with

$$
M\ge
\frac{d^2\log(L/\eta)}
{g\left(\beta-2\sqrt{\widetilde\varepsilon}\right)}
$$

independent Born samples from each Krylov state, Lean proves

$$
\Pr\!\left[
E_{\mathrm{SKQD}}-E_0
\le
\sqrt8\,\lVert H\rVert\sqrt{1-\sqrt\alpha}
\right]
\ge1-\eta.
$$

The paper-level theorem is
[`SKQD.paper_theorem1`](LeanExperiments/SKQD/Paper.lean). It does **not**
assume the existence of a low-energy Krylov combination: that witness is
constructed from the spectral assumptions.

[`SKQD.paper_theorem1_constructive`](LeanExperiments/SKQD/ConstructiveBudget.lean)
also chooses sufficient natural-number values of $d$ and $M$, discharging the
energy-domain, retained-sparsity, and sample-threshold conditions automatically.

## What is formalized

- Exact Hamiltonian time evolution $e^{-itH}$ and the finite Krylov family.
- The Chebyshev filter, off-band suppression, finite Fourier expansion, and
  coefficient bounds used in the paper's KQD theorem.
- Identification of the spectral filter with a finite combination of physical
  time-evolved states, including the ground-energy phase correction.
- The paper's exponential KQD energy bound for every positive dimension.
- The endpoint $\Delta=W$, the dimension-one case, and even dimensions.
- Appendix B Lemmas 1–5.
- Measurable independent sampling with exact Born marginals.
- The random sampled support and existence of its exact variational minimizer.
- Theorem 1 as both a failure-probability bound and a $1-\eta$ success bound.
- Explicit sufficient dimension and shot counts.
- Formal `Asymptotics.IsBigO` bounds for dimension, shots, total samples, and
  maximum evolution time.

The complete equation-by-equation explanation is in
[`SKQD_LEAN_RESEARCH_REPORT.md`](SKQD_LEAN_RESEARCH_REPORT.md). A compact proof
and assumption audit is in [`SKQD_COMPLETION_REPORT.md`](SKQD_COMPLETION_REPORT.md).

## Proof architecture

```text
spectral data + exact time evolution
                 │
       Chebyshev/Fourier filter
                 │
       normalized Krylov witness
                 │
       energy-to-state estimate
                 │
          sparsity transfer
                 │
   per-string Krylov hit probability
                 │
 independent sampling + union bound
                 │
 sampled-subspace variational minimum
                 │
                 ▼
       SKQD success probability ≥ 1 − η
```

## Repository layout

| Path | Contents |
|---|---|
| [`LeanExperiments/SKQD/Paper.lean`](LeanExperiments/SKQD/Paper.lean) | Paper-level convergence theorem from spectral and sampling assumptions |
| [`LeanExperiments/SKQD/ConstructiveBudget.lean`](LeanExperiments/SKQD/ConstructiveBudget.lean) | End-to-end theorem with chosen dimension and shots |
| [`LeanExperiments/SKQD/Filter.lean`](LeanExperiments/SKQD/Filter.lean) | Concrete Chebyshev filter and decay bounds |
| [`LeanExperiments/SKQD/Fourier.lean`](LeanExperiments/SKQD/Fourier.lean) | Finite Fourier representation and coefficient control |
| [`LeanExperiments/SKQD/SpectralFilter.lean`](LeanExperiments/SKQD/SpectralFilter.lean) | Spectral Rayleigh-quotient proof |
| [`LeanExperiments/SKQD/FilterBridge.lean`](LeanExperiments/SKQD/FilterBridge.lean) | Equality between the filter and physical Krylov sum |
| [`LeanExperiments/SKQD/Witness.lean`](LeanExperiments/SKQD/Witness.lean) | Odd-dimensional Krylov witness |
| [`LeanExperiments/SKQD/Endpoint.lean`](LeanExperiments/SKQD/Endpoint.lean) | Bandwidth endpoint and dimension-one cases |
| [`LeanExperiments/SKQD/Parity.lean`](LeanExperiments/SKQD/Parity.lean) | Even-dimension reduction |
| [`LeanExperiments/SKQD/Basic.lean`](LeanExperiments/SKQD/Basic.lean) | Hilbert-space estimates and Appendix B Lemmas 1 and 4 |
| [`LeanExperiments/SKQD/Sparsity.lean`](LeanExperiments/SKQD/Sparsity.lean) | Sparsity and Appendix B Lemmas 2, 3, and 5 |
| [`LeanExperiments/SKQD/Sampling.lean`](LeanExperiments/SKQD/Sampling.lean) | Probability model, sampled support, and exact minimizer |
| [`LeanExperiments/SKQD/PolynomialResources.lean`](LeanExperiments/SKQD/PolynomialResources.lean) | Finite and asymptotic resource bounds |
| [`LeanExperiments/SKQD/Audit.lean`](LeanExperiments/SKQD/Audit.lean) | Guarded axiom and edge-case regression audit |

## Building and checking

The project pins Lean and Mathlib at version `v4.33.0`.

Install [Lean through elan](https://lean-lang.org/lean4/doc/quickstart.html),
then run:

```bash
git clone https://github.com/samarth777/skqd-lean.git
cd skqd-lean
lake exe cache get
lake build
lake env lean LeanExperiments/SKQD/Audit.lean
```

To scan for prohibited proof placeholders:

```bash
rg -n '\bsorry\b|\badmit\b|^axiom\b|sorryAx|native_decide' \
  LeanExperiments/SKQD LeanExperiments/SKQD.lean
```

A successful scan has no output. GitHub Actions runs the complete build and
the guarded audit on every push and pull request.

## Trust boundary

The audited principal theorems use only the standard foundations appearing in
this Mathlib development:

```text
propext
Classical.choice
Quot.sound
```

There are no `sorry`, `admit`, custom `axiom`, `sorryAx`, or `native_decide`
occurrences in the SKQD proof sources.

The theorem is intentionally about the paper's ideal mathematical model. Exact
operator exponentials, exact Born marginals, and an exact sampled-subspace
minimizer are used. This repository does not verify Trotterization, hardware
noise, floating-point eigensolvers, configuration recovery, or the paper's
experiments. Appendix E's model-specific Ising sparsity theorem is also outside
the convergence proof; sparsity is assumed exactly as in Theorem 1.

## Documentation

- [Research-style paper-to-Lean report](SKQD_LEAN_RESEARCH_REPORT.md)
- [Completion and assumption audit](SKQD_COMPLETION_REPORT.md)
- [Historical development report](SKQD_FORMALIZATION_REPORT.md)

## Citation

If you use the underlying SKQD result, cite the original paper:

```bibtex
@article{yu2025skqd,
  title   = {Sample-based Krylov Quantum Diagonalization},
  author  = {Yu, Jeffery and others},
  journal = {arXiv preprint arXiv:2501.09702},
  year    = {2025}
}
```
