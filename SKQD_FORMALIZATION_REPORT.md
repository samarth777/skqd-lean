# SKQD convergence proof: paper-to-Lean formalization report

> Historical report: its statements about the missing spectral witness are
> superseded by [the current completion report](SKQD_COMPLETION_REPORT.md).
> The spectral construction, endpoint, parity reduction, and final theorem
> from spectral assumptions have now been implemented. The detailed
> Appendix B explanations below remain useful, but this is not the current
> completion-status document.

## 1. Scope and conclusion

This report compares the convergence proof in **Sample-based Krylov Quantum
Diagonalization**, arXiv:2501.09702v1, with the Lean development in this
repository.

Paper: <https://arxiv.org/html/2501.09702v1>

The current development machine-checks the deterministic Hilbert-space
argument in Appendix B, the sparsity-transfer argument, the important-string
probability lower bound, independent Born sampling, the finite union bound,
existence of an exact minimizer on the sampled subspace, and the final
probability-of-bad-energy conclusion.

It also proves exact unitary time evolution and common-time-shift invariance,
global phase alignment, the concrete Chebyshev filter's normalization and
off-band decay, existence of a finite exponential expansion with bounded
coefficients, and Parseval bounds. The exact-family probability theorem uses
the initial-state overlap directly.

The remaining external dependency is the quantitative KQD approximation
result used as Theorem 2 in Appendix A. The SKQD paper attributes this result
to Theorem 3.1 of Epperly, Lin, and Nakatsukasa, *A Theory of Quantum Subspace
Diagonalization*. In the present Lean theorem, the normalized low-energy
Krylov combination and its coefficient bound are explicit hypotheses.

Accordingly, the present status is:

- **Appendix B / SKQD reduction:** machine-checked, including its probability
  space and exact sampled-subspace minimizer.
- **Exact unitary Krylov states:** defined and normalization-preservation
  machine-checked.
- **Appendix A filter, Eqs. (33)–(35):** filter normalization, global bound,
  off-band decay, finite expansion, and coefficient bounds proved.
- **Appendix A spectral Rayleigh-quotient estimate, Eqs. (36)–(39):** not yet
  assembled into a proof of the quantitative KQD witness.
- **Informal polynomial-time corollary:** not yet formalized as an asymptotic
  theorem over a family of Hamiltonians.

No declaration in the SKQD development uses `sorry`, `admit`, or a custom
axiom. `lake build` succeeds.

## 2. Source layout

| Lean file | Role |
|---|---|
| [`Basic.lean`](LeanExperiments/SKQD/Basic.lean) | Abstract ground-state gap, Hilbert-space identities, Lemma 1, variational principle, and the analytic part of Lemma 4. |
| [`Krylov.lean`](LeanExperiments/SKQD/Krylov.lean) | Exact operator exponential, Krylov family, and unitary normalization. |
| [`Sparsity.lean`](LeanExperiments/SKQD/Sparsity.lean) | Born probabilities, Definition 1, Lemmas 2, 3, and 5. |
| [`Theorem1.lean`](LeanExperiments/SKQD/Theorem1.lean) | Deterministic composition of Appendix B.1 and the paper's sample-count formula. |
| [`Sampling.lean`](LeanExperiments/SKQD/Sampling.lean) | Random samples, independent Born measurements, sampled support, failure event, exact diagonalization, and the probabilistic theorem. |
| [`Phase.lean`](LeanExperiments/SKQD/Phase.lean) | Phase selection preserving norm, energy, and coefficient norms. |
| [`Filter.lean`](LeanExperiments/SKQD/Filter.lean) | Eq. (34) and the bounds of Eq. (33). |
| [`Trigonometric.lean`](LeanExperiments/SKQD/Trigonometric.lean) | Finite frequency support and exponential expansion. |
| [`Fourier.lean`](LeanExperiments/SKQD/Fourier.lean) | Integral coefficient bounds, Parseval, and bounded finite expansion. |
| [`Resources.lean`](LeanExperiments/SKQD/Resources.lean) | Scalar error formula, odd dimension, retained sparsity, and integer shot choices. |
| [`ExactGuarantee.lean`](LeanExperiments/SKQD/ExactGuarantee.lean) | Conditional exact-family probability theorem and explicit remaining witness obligation. |
| [`SKQD.lean`](LeanExperiments/SKQD.lean) | Public aggregate import. |

## 3. Mathematical representation

### 3.1 Finite Hilbert space

For the computational-basis results, the paper's `N`-dimensional Hilbert
space is represented by

```lean
EuclideanSpace ℂ ι
```

where `ι` is a finite type. An element `j : ι` labels a computational-basis
string, and `ψ j : ℂ` is its amplitude. This is slightly more general than
fixing `ι = Fin (2^n)`; the SKQD proof uses only finiteness and a distinguished
computational basis.

The operator `H` is represented as a bounded complex-linear operator:

```lean
H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι
```

### 3.2 Ground state and spectral gap

Paper assumptions about the ground state and first spectral gap are bundled
in [`GroundStateGap`](LeanExperiments/SKQD/Basic.lean#L15):

```lean
structure GroundStateGap (H : E →L[ℂ] E) (φ₀ : E)
    (E₀ ΔE₁ : ℝ) : Prop where
  normalized : ‖φ₀‖ = 1
  eigen : H φ₀ = (E₀ : ℂ) • φ₀
  symmetric : (H : E →ₗ[ℂ] E).IsSymmetric
  gap_pos : 0 < ΔE₁
  gap : ∀ ψ, inner ℂ φ₀ ψ = 0 → ‖ψ‖ = 1 →
    E₀ + ΔE₁ ≤ (inner ℂ ψ (H ψ)).re
```

The last field is the operational form of the spectral-gap condition needed
by the proof: every normalized vector orthogonal to the ground state has
energy at least `E₀ + ΔE₁`. It also excludes ground-state degeneracy, in line
with the paper's use of a positive first gap.

### 3.3 Complex phases

Lean distinguishes carefully between complex inner products and their real
parts. Energy expectations are consistently represented by

```lean
(inner ℂ ψ (H ψ)).re
```

The paper's Lemma 1 says that the ground-state overlap is real, but its final
step also requires it to be nonnegative. Lean therefore assumes both

```lean
(inner ℂ φ₀ ψ).im = 0
0 ≤ (inner ℂ φ₀ ψ).re
```

These remain premises of the low-level Lemma 1, but are no longer premises
of `theorem1_probabilistic`. `exists_aligning_phase` proves phase selection,
including zero overlap. `align_combination` proves that applying this phase
to every coefficient preserves coefficient norms, state norm, and energy.
The probability theorem performs this operation internally.

## 4. Paper-to-Lean correspondence

| Paper item | Mathematical content | Lean declaration | Status |
|---|---|---|---|
| Eq. (1), Eq. (26) | `ψₖ = exp(-ikHΔt)ψ₀` | [`timeEvolution`](LeanExperiments/SKQD/Krylov.lean#L15), [`krylovFamily`](LeanExperiments/SKQD/Krylov.lean#L19) | Checked definition |
| Unitarity used below Eq. (32) | Time evolution preserves norms | [`timeEvolution_norm`](LeanExperiments/SKQD/Krylov.lean#L28), [`krylovFamily_normalized`](LeanExperiments/SKQD/Krylov.lean#L47) | Checked |
| Definition 1 / Eqs. (5)–(7), (40)–(42) | `(α,β)` sparsity | [`hitProb`](LeanExperiments/SKQD/Sparsity.lean#L18), [`Sparse`](LeanExperiments/SKQD/Sparsity.lean#L39) | Checked |
| Theorem 2 / Eqs. (31), (64) | Quantitative KQD error bound | Low-energy and coefficient assumptions of [`theorem1`](LeanExperiments/SKQD/Theorem1.lean#L110) and [`theorem1_probabilistic`](LeanExperiments/SKQD/Sampling.lean#L271) | External dependency |
| Lemma 1 / Eqs. (45)–(48) | Low energy implies state closeness | [`lemma1_state_error`](LeanExperiments/SKQD/Basic.lean#L211) | Checked |
| Lemma 2 / Eqs. (49)–(56) | Sparsity survives perturbation | [`lemma2_sparsity_transfer`](LeanExperiments/SKQD/Sparsity.lean#L108) | Checked |
| Lemma 3 / Eqs. (57)–(58) | Each important string has probability at least `p` in some Krylov state | [`lemma3_krylov_hit`](LeanExperiments/SKQD/Sparsity.lean#L166) | Checked |
| Lemma 4 / Eq. (59) | Repeated-shot and union bounds | [`iidBornMiss_of_independent`](LeanExperiments/SKQD/Sampling.lean#L50), [`samplingFailure_measure_le`](LeanExperiments/SKQD/Sampling.lean#L113), [`failure_bound_le_exp`](LeanExperiments/SKQD/Basic.lean#L293) | Checked |
| Lemma 5 / Eqs. (60)–(63) | Energy of normalized truncation | [`lemma5_truncated_energy`](LeanExperiments/SKQD/Sparsity.lean#L309) | Checked |
| Appendix B.1 / Eqs. (65)–(68) | Compose state error, sparsity, and hit probability | [`epsTilde`](LeanExperiments/SKQD/Theorem1.lean#L22), [`hitLowerBound`](LeanExperiments/SKQD/Theorem1.lean#L39), [`theorem1`](LeanExperiments/SKQD/Theorem1.lean#L110) | Checked conditionally on KQD input |
| Eq. (69) | Actual probability of missing an important string | [`samplingFailure`](LeanExperiments/SKQD/Sampling.lean#L38), [`theorem1_probabilistic`](LeanExperiments/SKQD/Sampling.lean#L271) | Checked |
| Eq. (70) | Energy bound for sampled-subspace result | [`badEnergy_subset_samplingFailure`](LeanExperiments/SKQD/Sampling.lean#L236), [`theorem1_probabilistic`](LeanExperiments/SKQD/Sampling.lean#L271) | Checked |
| Classical projected diagonalization | Lowest-energy unit vector on sampled coordinate subspace | [`MinimizerOn`](LeanExperiments/SKQD/Sampling.lean#L171), [`exists_minimizerOn`](LeanExperiments/SKQD/Sampling.lean#L181), [`exactSKQDOutput`](LeanExperiments/SKQD/Sampling.lean#L220) | Checked |

## 5. Detailed proof correspondence

### 5.1 Exact Krylov evolution: paper Eqs. (1), (26), and (32)

[`timeEvolution`](LeanExperiments/SKQD/Krylov.lean#L15) defines

```lean
NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)
```

which is the bounded-operator exponential `exp(-itH)`. The finite family
[`krylovFamily`](LeanExperiments/SKQD/Krylov.lean#L19) evaluates this at
`t = kΔt` for `k : Fin d`.

[`krylovFamily_zero`](LeanExperiments/SKQD/Krylov.lean#L23) proves that the
zeroth Krylov state is exactly the reference state.

For a symmetric `H`, [`timeEvolution_norm`](LeanExperiments/SKQD/Krylov.lean#L28)
turns `-tH` into a self-adjoint element, uses Mathlib's exponential-unitary
construction for `exp(i(-tH))`, and applies the norm-preservation theorem for
unitary continuous linear maps. Consequently,
[`krylovFamily_normalized`](LeanExperiments/SKQD/Krylov.lean#L47) derives
normalization of every Krylov state from normalization of `ψ₀`.

What is not yet proved here is that the specific Chebyshev-filtered linear
combination described in Appendix A satisfies Equation (31).

### 5.2 Definition 1: sparsity

The Born probability of basis outcome `j` is

```lean
hitProb ψ j = ‖ψ j‖².
```

[`sum_hitProb`](LeanExperiments/SKQD/Sparsity.lean#L23) proves that these
probabilities sum to `‖ψ‖²`; hence they sum to one for normalized states.

[`Sparse`](LeanExperiments/SKQD/Sparsity.lean#L39) says

```lean
α ≤ ∑ i ∈ s, hitProb ψ i
∀ i ∈ s, β ≤ hitProb ψ i.
```

This matches Equations (6)–(7). Lean does not encode that `s` consists of the
top `L` amplitudes in sorted order. The later proof does not use the ordering;
it only uses the two inequalities. Thus the Lean statement is a valid
generalization to any designated finite set satisfying them, with `L = s.card`.

### 5.3 Lemma 1: low energy implies closeness

Paper claim:

```text
‖ψ - φ₀‖² ≤ 2(1 - sqrt(1 - ε/ΔE₁)).
```

Lean implementation:
[`lemma1_state_error`](LeanExperiments/SKQD/Basic.lean#L211).

The Lean proof follows the paper's decomposition but makes every intermediate
claim explicit:

1. Define `χ = ⟪φ₀,ψ⟫` and `δ = ψ - χ • φ₀`.
2. Prove `δ ⟂ φ₀` with
   [`remainder_orthogonal`](LeanExperiments/SKQD/Basic.lean#L157).
3. Prove the Pythagorean identity
   `‖ψ‖² = ‖χ‖² + ‖δ‖²` with
   [`remainder_pythagoras`](LeanExperiments/SKQD/Basic.lean#L163).
4. Expand the energy and eliminate cross terms using symmetry and the
   eigenvector equation in
   [`re_energy_decomposition`](LeanExperiments/SKQD/Basic.lean#L131).
5. Apply the gap to the normalized orthogonal remainder via
   [`orthogonal_energy_gap`](LeanExperiments/SKQD/Basic.lean#L180), obtaining
   `‖δ‖² ΔE₁ ≤ ε`.
6. Convert this into a lower bound on `‖χ‖`, use the real nonnegative phase,
   and apply the normalized-vector distance identity
   [`dist_sq_of_normalized`](LeanExperiments/SKQD/Basic.lean#L97).

Lean uses non-strict inequalities (`≤`) where the paper often writes `<`.
This is the natural closed version and is sufficient for every subsequent
bound.

The assumptions `0 ≤ ε` and `ε ≤ ΔE₁` ensure the square root is real. They
are implicit domain requirements in the paper but explicit in Lean.

### 5.4 Lemma 2: transfer of sparsity

Lean implementation:
[`lemma2_sparsity_transfer`](LeanExperiments/SKQD/Sparsity.lean#L108).

For the total mass on `s`, Lean formalizes the paper's expansion

```text
|cᵢ + (aᵢ-cᵢ)|² ≥ |cᵢ|² - 2|cᵢ||aᵢ-cᵢ|
```

as [`amp_sq_sub_bound`](LeanExperiments/SKQD/Sparsity.lean#L60). The sum of
the cross terms is bounded using the finite Cauchy–Schwarz inequality in
[`sum_amp_cs`](LeanExperiments/SKQD/Sparsity.lean#L77).

For the pointwise `β` bound, [`coord_diff_le_dist`](LeanExperiments/SKQD/Sparsity.lean#L54)
shows that every coordinate difference is at most the full vector distance,
and [`norm_coord_le_one`](LeanExperiments/SKQD/Sparsity.lean#L99) bounds a
coordinate of a normalized vector by one.

The result is exactly

```text
Sparse ψ s (α - 2√ε) (β - 2√ε).
```

### 5.5 Lemma 3: an important bitstring appears in a Krylov state

Lean implementation:
[`lemma3_krylov_hit`](LeanExperiments/SKQD/Sparsity.lean#L166).

Suppose

```text
φ = Σₖ dₖ ψₖ,
|dₖ||γ₀| ≤ 1,
β ≤ |φ(j)|².
```

The proof expands the `j`th coordinate using
[`coord_linear_combination`](LeanExperiments/SKQD/Sparsity.lean#L158), then
uses the triangle inequality to derive

```text
|γ₀|√β ≤ Σₖ |ψₖ(j)|.
```

A maximum term in this finite sum must be at least the average. Squaring gives

```text
∃ k, |γ₀|² β / d² ≤ hitProb (ψₖ) j.
```

This matches Equations (57)–(58). The Lean type `κ` is an arbitrary nonempty
finite index type and `d` is represented by `Fintype.card κ`.

### 5.6 Lemma 4: independent sampling and union bound

The initial version of the formalization contained only the real-number
inequality `L(1-p)^M ≤ η`. The current version additionally models the random
experiment.

[`Samples`](LeanExperiments/SKQD/Sampling.lean#L27) represents an outcome as

```lean
κ → Fin M → Ω → ι,
```

meaning: Krylov-state index, shot index, random run, and observed bitstring.

[`iidBornMiss_of_independent`](LeanExperiments/SKQD/Sampling.lean#L50) assumes
that each shot is measurable, the `M` shots for each Krylov state are
independent, and the one-shot marginal is the Born probability. It then proves

```text
P(all M shots from ψₖ miss j) = (1 - hitProb ψₖ j)^M.
```

This proof uses the measure of a complement and Mathlib's finite-intersection
formula for independent random variables. Thus `(1-p)^M` is derived rather
than postulated in the final probabilistic theorem.

[`sampledSupport`](LeanExperiments/SKQD/Sampling.lean#L30) is the union of all
observed outcomes. [`samplingFailure`](LeanExperiments/SKQD/Sampling.lean#L38)
is the event that some `j ∈ s` occurs in none of the shots from any Krylov
state.

For each `j`, Lemma 3 supplies one Krylov state whose hit probability is at
least `p`. Missing `j` globally implies missing it in that particular state.
[`samplingFailure_measure_le`](LeanExperiments/SKQD/Sampling.lean#L113) then
applies the finite union bound:

```text
P(samplingFailure) ≤ |s| (1-p)^M.
```

The remaining analytic steps are:

- [`failure_bound_le_exp`](LeanExperiments/SKQD/Basic.lean#L293):
  `L(1-p)^M ≤ L exp(-Mp)`.
- [`exp_failure_le_eta`](LeanExperiments/SKQD/Basic.lean#L306):
  `log(L/η) ≤ Mp` implies `L exp(-Mp) ≤ η`.
- [`paper_sample_threshold`](LeanExperiments/SKQD/Basic.lean#L337): converts
  the paper's formula for `M` into `log(L/η) ≤ Mp`.
- [`paper_sampling_failure_le_eta`](LeanExperiments/SKQD/Basic.lean#L354):
  composes the preceding inequalities.

### 5.7 Lemma 5: energy of the truncated ground state

[`restrict`](LeanExperiments/SKQD/Sparsity.lean#L222) zeroes all coordinates
outside `s`. [`truncated`](LeanExperiments/SKQD/Sparsity.lean#L274) normalizes
that restriction by dividing by the square root of its support mass.

Lean proves:

- [`restrict_norm_sq`](LeanExperiments/SKQD/Sparsity.lean#L249): the squared
  norm of the restriction equals its support mass.
- [`truncated_normalized`](LeanExperiments/SKQD/Sparsity.lean#L278): the
  truncated vector is normalized when `α > 0`.
- [`truncated_overlap`](LeanExperiments/SKQD/Sparsity.lean#L290): its overlap
  with the original vector is exactly the square root of the support mass.

The general estimate
[`energy_expectation_lipschitz`](LeanExperiments/SKQD/Basic.lean#L25) proves

```text
|⟨ψ,Hψ⟩ - ⟨φ,Hφ⟩| ≤ 2 ‖H‖ ‖ψ-φ‖
```

for normalized vectors. Combining it with the overlap-distance identity gives
[`truncated_energy_bound`](LeanExperiments/SKQD/Basic.lean#L57), and finally
[`lemma5_truncated_energy`](LeanExperiments/SKQD/Sparsity.lean#L309):

```text
|E(truncated φ s) - E(φ)|
  ≤ √8 ‖H‖ √(1 - √α).
```

The Lean result bounds the absolute energy difference, which is at least as
strong as the paper's one-sided inequality. Self-adjointness is not needed for
the Lipschitz estimate itself.

### 5.8 Exact diagonalization on the sampled subspace

The paper says to project `H` into the sampled computational-basis subspace
and return its lowest-energy state. Lean makes this precise.

[`SupportedOn`](LeanExperiments/SKQD/Sampling.lean#L142) means that a vector's
coordinates vanish outside a finite set. [`supportedSubmodule`](LeanExperiments/SKQD/Sampling.lean#L146)
packages these vectors as a complex submodule.

[`MinimizerOn`](LeanExperiments/SKQD/Sampling.lean#L171) specifies a normalized
supported vector whose energy is no greater than that of any other normalized
vector with the same support constraint.

[`exists_minimizerOn`](LeanExperiments/SKQD/Sampling.lean#L181) proves such a
state exists whenever the support is nonempty:

1. Intersect the unit sphere with the finite-dimensional coordinate subspace.
2. Show the intersection is compact and nonempty.
3. Show the energy expectation is continuous.
4. Apply the extreme-value theorem.

[`exactSKQDOutput`](LeanExperiments/SKQD/Sampling.lean#L220) chooses one such
minimizer, and [`exactSKQDOutput_spec`](LeanExperiments/SKQD/Sampling.lean#L227)
proves its specification. This is a mathematical exact-diagonalization model;
it does not verify a concrete numerical eigensolver or floating-point error.

### 5.9 Appendix B.1 and the final probability statement

[`epsTilde`](LeanExperiments/SKQD/Theorem1.lean#L22) is

```text
2(1 - sqrt(1 - ε/ΔE₁)),
```

matching Equations (65)–(66). [`hitLowerBound`](LeanExperiments/SKQD/Theorem1.lean#L39)
is

```text
|γ₀|² (β₀ - 2√epsTilde) / d²,
```

matching Equation (68).

[`theorem1`](LeanExperiments/SKQD/Theorem1.lean#L110) composes the deterministic
lemmas and proves the analytic expression `L(1-p)^M ≤ η`. It deliberately does
not claim that this expression is itself an event probability.

[`badEnergy_subset_samplingFailure`](LeanExperiments/SKQD/Sampling.lean#L236)
provides the algorithmic bridge. If all important strings were sampled, the
truncated ground state lies in the sampled subspace. Exact minimization can
only improve its energy. Therefore a run whose energy exceeds the Lemma 5
bound must belong to the sampling-failure event.

Finally, [`theorem1_probabilistic`](LeanExperiments/SKQD/Sampling.lean#L271)
proves

```text
P(E(output) - E₀ > √8 ‖H‖ √(1 - √α)) ≤ η.
```

Its overlap parameter is tied to
`inner ℂ φ₀ (krylov k₀)`, rather than being a free unrelated scalar. Its
sampling conclusion is derived from measurable independent shots with exact
Born-rule marginals, and its output is the proved-to-exist exact minimizer.

## 6. Assumptions of the final probabilistic theorem

The inputs to `theorem1_probabilistic` can be grouped as follows.

### Hamiltonian assumptions

- `φ₀` is normalized.
- `H φ₀ = E₀ φ₀`.
- `H` is symmetric/self-adjoint.
- `ΔE₁ > 0` and bounds every normalized orthogonal state's energy above
  `E₀`.

These are contained in `GroundStateGap`.

### KQD approximation assumptions

- A finite family `krylov` of normalized states.
- A normalized combination `Σₖ coeffₖ • krylovₖ`.
- Energy error at most `ε`.
- Coefficient bound `|coeffₖ||γ₀| ≤ 1`.

There is no phase assumption in the public probability theorem: phase
alignment is proved internally.

The paper obtains these from its Appendix A construction and the theorem
cited from Epperly et al. This derivation is the remaining unformalized part.

### Sparsity and parameter-domain assumptions

- `Sparse φ₀ s α β`.
- `0 < α ≤ 1`.
- `0 ≤ ε ≤ ΔE₁`.
- `β - 2√epsTilde > 0`, so the lower hit probability is useful.
- `s` and the Krylov family are nonempty.
- `η > 0` and the paper's sample threshold holds.

For the usual interpretation of `η` as a failure tolerance one would normally
also choose `η ≤ 1`; the inequality remains mathematically valid without
requiring that redundant restriction explicitly.

### Sampling assumptions

- Each sample function is measurable.
- The shots taken from each fixed Krylov state are independent.
- Each shot has the exact Born-rule marginal distribution.

The repeated-shot probability and union bound are theorems derived from these
assumptions.

## 7. Strengthenings and intentional generalizations

The Lean statements differ from the paper in several harmless or beneficial
ways:

1. `Sparse` works for any finite important set, not only an explicitly sorted
   prefix of basis strings.
2. Lemma 5 proves an absolute energy-difference bound.
3. Lemma 1 explicitly records all square-root domain assumptions.
4. Phase alignment, including nonnegativity, is constructed and proved rather
   than assumed by the probability theorem.
5. Krylov indices may be any finite type in the generic Appendix B lemmas.
6. The probability theorem describes a genuine event on a probability space,
   not merely a numerical upper-bound expression.
7. The existence of the exact projected minimizer is proved rather than
   assumed in the final theorem.

## 8. Remaining work for a fully closed quantitative convergence theorem

### 8.1 Formalize the imported KQD theorem

The largest missing component is Appendix A, Theorem 2 / Equation (31):

```text
ε = 8 ΔEmax ((1-|γ₀|²)/|γ₀|²)
      (1 + π ΔE₁/ΔEmax)^(-(d-1)).
```

A complete Lean derivation would require:

1. A finite-dimensional spectral decomposition of the self-adjoint operator.
2. The shifted and unshifted Krylov subspaces and proof that their projected
   minima coincide.
3. Definition of the Chebyshev trigonometric filter in Equation (34): **done**.
4. Its normalization at zero and uniform off-target estimate in Equation
   (33): **done** for `0 ≤ a < π`.
5. Its finite exponential expansion and coefficient norm bounds: **done**.
   Parseval bounds for the integral-defined coefficients are also proved.
6. Construction and normalization of the filtered Krylov vector.
7. The resulting Rayleigh-quotient bound and coefficient bound.

The remaining construction must apply these results to one spectral-filtered
state, normalize it, transfer it to the nonnegative time indices, and prove
both fields of `ExactKrylovWitness`. The endpoint `a = π`, where Eq. (34) has
a zero denominator, needs a separate spectral argument. Even dimensions need
the paper's reduction to the previous odd dimension.

### 8.2 Connect the generic final theorem directly to `krylovFamily`

**Done, conditionally on the Krylov witness.** `exact_krylov_probabilistic`
in `ExactGuarantee.lean` instantiates

```lean
krylov := krylovFamily H ψ₀ (π / ΔEmax) d
```

and discharges normalization using `krylovFamily_normalized`. It replaces the
designated reference-state overlap by `inner ℂ φ₀ ψ₀`. It does not discharge
the witness itself. Bundling the missing fields into a structure is an API
boundary, not a proof of them.

### 8.3 State the polynomial-time corollary precisely

The paper describes `ΔEmax` as “not growing too quickly,” `ΔE₁` as “not too
small,” and the ground-state overlap and sparsity parameters as polynomially
controlled. These phrases are not a single formal proposition.

For a Lean asymptotic theorem one must introduce a family indexed by qubit
count `n` and state explicit bounds, for example:

- `ΔEmax(n) ≤ polynomial(n)`;
- `1/ΔE₁(n) ≤ polynomial(n)`;
- `1/|γ₀(n)|² ≤ polynomial(n)`;
- `L(n)` and `1/β(n)` are polynomially bounded;
- the requested accuracy and failure tolerance have specified encodings.

One can then prove polynomial bounds for `d`, `M`, sampled-subspace dimension,
and classical diagonalization cost. Until those functions and encodings are
chosen, “polynomial time” is an informal corollary rather than a uniquely
determined Lean statement.

### 8.4 Approximate time evolution and numerical diagonalization

The analytical theorem uses exact `exp(-itH)`, exact Born measurements, and an
exact subspace minimizer. The experimental paper uses Trotterized dynamics,
device noise, mitigation, and numerical eigensolvers. Verifying those
approximations would be a separate robustness theorem and is not part of the
ideal convergence statement currently formalized.

## 9. Apparent typographical issues in arXiv v1 Appendix A

These do not invalidate the intended KQD result, but they matter when turning
the displayed derivation into formal code:

- Equation (37) writes the modulus squared of
  `⟨φ̃K|φ̃K⟩`; the subsequent expression behaves like the squared norm itself,
  not its square again.
- Equation (38) uses `γ_i` inside a sum indexed by `j` and one displayed inner
  sum appears to omit the Fourier coefficient `c_k`.
- Equation (38) changes from energy gaps `E_j-E₀` to `E_j`; that replacement
  requires a shift convention or an additional sign assumption.
- Equation (39) uses exponent `-d`, whereas the polynomial degree was defined
  as `(d-1)/2` and Equation (31)/(64) uses exponent `-(d-1)` after squaring.

The formalization of the remaining KQD component should therefore use the
precise statement and proof of the cited Epperly–Lin–Nakatsukasa theorem,
rather than translating these v1 display equations literally.

## 10. Verification procedure

The project uses Lean 4.33.0 and Mathlib v4.33.0. From the repository root:

```bash
lake build
rg -n "sorry|admit|axiom" LeanExperiments/SKQD LeanExperiments/SKQD.lean
```

`lake build` checks the aggregate, including the new modules. Searching
source text is only a preliminary check; `Audit.lean` also uses `#print axioms`
on the central declarations. Standard Lean dependencies such as
`Classical.choice`, `propext`, and `Quot.sound` are distinct from a custom
axiom or `sorryAx`.

Latest local verification: `lake build` succeeded (17,426 jobs). The eight
audited declarations depend only on those three standard axioms. The audit
uses `#guard_msgs` to make a changed dependency list a failing regression
check, and CI runs this file explicitly.

## 11. Overall assessment

The Lean development is a sound and substantially stronger formalization of
the SKQD-specific Appendix B argument than the initial version: probability,
sampling, and projected minimization are now mathematical objects linked to
the energy conclusion.

It should currently be described as a **machine-checked reduction from the
quantitative KQD witness to the probabilistic SKQD energy guarantee**. It
should not yet be described as a completely closed verification of the KQD
error rate or of the paper's informal polynomial-time claim. Closing that last
boundary requires the spectral filtered-state construction and its
Rayleigh-quotient estimate, endpoint/parity handling, and precise asymptotic
assumptions for a Hamiltonian family. The scalar ceiling formulas in
`Resources.lean` do not by themselves prove a polynomial-time algorithm.

## 12. Newly proved Appendix A components

| Paper step | Lean declaration | What is checked |
|---|---|---|
| Eq. (32) | `centered_krylov_eq_shift`, `timeEvolution_energy_inner` | A common time shift preserves Gram and Hamiltonian entries. |
| Eq. (34) | `chebyshevFilter` | The concrete normalized Chebyshev expression. |
| Eq. (33), value at zero | `chebyshevFilter_zero` | `p(0)=1`, including degree zero. |
| Uniform bound | `chebyshevFilter_abs_le_one` | `|p(θ)|≤1` for all real `θ`. |
| Eq. (33), off-band | `chebyshevFilter_off_band` | `|p(θ)|≤2/(1+a)^m` when `a≤|θ|≤π`. |
| Eq. (35), finite expansion | `chebyshevFilter_exists_expansion` | Frequencies lie in `[-m,m]`. |
| Eq. (35), coefficient control | `chebyshevFilter_bounded_expansion` | The same finite expansion has every coefficient norm at most one. |
| Parseval bound | `filterFourierCoeff_sum_sq_le_one` | Any finite sum of squared integral-defined coefficient norms is at most one. |
| Dimension selection | `sufficientOddDimension_error` | An explicit odd integer makes the scalar geometric error at most a target. |
| Positive sampling denominator | `retained_sparsity_ge_half` | `ε≤gap*β²/32` retains at least `β/2`. |
| Integer shots | `sufficientShots_meets_threshold` | A positive integer shot count meets the real threshold. |

The filter decay proof rewrites its denominator argument as
`1+2*tan(a/2)^2`. The inequality `a/2≤tan(a/2)` implies that the
hyperbolic-Chebyshev growth base is at least `1+a`. The finite-expansion proof
tracks frequency intervals through multiplication and the Chebyshev
recurrence. Coefficient extraction uses orthogonality of circle characters.
No estimate on the desired Krylov energy is inserted into these proofs.
