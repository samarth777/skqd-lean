# SKQD: current proof and assumption audit

Source: [arXiv:2501.09702v1](https://arxiv.org/html/2501.09702v1), ideal
convergence guarantee, Appendix A and Appendix B.

## Outcome

`SKQD.paper_theorem1` in [Paper.lean](LeanExperiments/SKQD/Paper.lean)
derives the quantitative SKQD probability guarantee from spectral,
sparsity, parameter-domain, and independent Born-sampling assumptions.
It does **not** assume a low-energy Krylov combination, a bound on its
coefficients, a phase convention, or `ExactKrylovWitness`.

The witness is now constructed in Lean. This closes the main gap identified
in the previous report. All positive Krylov dimensions are covered, including
the two-level endpoint and the paper's preceding-odd-dimension rule.

`paper_theorem1_constructive` in
[ConstructiveBudget.lean](LeanExperiments/SKQD/ConstructiveBudget.lean) goes
further: it chooses dimension and shots, derives the required energy and
retained-sparsity conditions, and proves the `1-η` success statement directly.
`resourceCounts_isBigO` and `evolutionTime_isBigO` in
[PolynomialResources.lean](LeanExperiments/SKQD/PolynomialResources.lean)
formalize polynomial scaling over families indexed by system size.

The theorem describes exact mathematics. It does not verify the runtime or
roundoff behavior of an executable eigensolver, Trotter approximation,
configuration recovery, or the experiments in the paper.

## Final statement

Write `g = ‖inner ℂ (b j₀) ψ₀‖²`, `W` for the spectral bandwidth bound,
and `gap` for the positive excitation-gap bound. Define

```text
d_eff = 2 * floor((d-1)/2) + 1
ε = [8 W (1-g)/g] / (1 + π gap/W)^(d_eff-1)
et = 2 (1 - sqrt(1-ε/gap))
B_energy = sqrt(8) ‖H‖ sqrt(1-sqrt(α)).
```

For an important basis-string set `s` of cardinality `L`, the theorem proves

```text
Pr[energy(exactSKQDOutput)-E₀ > B_energy] ≤ η
```

provided

```text
M ≥ d² log(L/η) / [g (β - 2 sqrt(et))].
```

`measurable_exactSKQDOutput` proves that the chosen exact minimizer is a
measurable random state. `success_probability_of_bad_probability` converts
the bad-event bound into the equivalent success statement

```text
Pr[energy(exactSKQDOutput)-E₀ ≤ B_energy] ≥ 1-η.
```

## Assumptions: what is and is not accepted as input

| Input | Meaning and justification |
|---|---|
| Finite-dimensional complex Hilbert space | The paper's finite quantum state space. |
| Orthonormal eigenbasis `b`, real energies `e`, eigenvector equations | The spectral representation explicitly used in Appendix A. |
| Self-adjointness of `H` | The Hamiltonian assumption. |
| Normalized `ψ₀`, nonzero overlap with `b j₀` | The reference-state assumptions. |
| `0 < gap ≤ W`, and every excited energy gap lies in `[gap,W]` | The spectral assumptions. Bounds suffice; equality with the extremal gaps is allowed. |
| `Sparse (b j₀) s α β`, `0 < α ≤ 1`, `L > 0` | Ground-state sparsity on the important strings. |
| Positive `d`, `M`, and `η` | Valid dimension, shot count, and failure tolerance. |
| `ε` equals the displayed formula, `ε ≤ gap`, positive retained sparsity | The parameter domain in which the state-error and sample-count estimates apply. |
| Measurable independent shots with exact Born marginals | The ideal measurement experiment. Independence is needed within each Krylov state's shots. |
| The displayed lower bound on `M` | The paper's sample-complexity requirement. |

`ε ≥ 0` and the abstract `GroundStateGap` used by Appendix B are derived.
No spectral error bound is inserted as an axiom or supplied as an extra
input. The eigenbasis is input data, not a supplied energy-approximation
conclusion.

## Appendix A correspondence

| Paper item | Lean declarations | Explanation |
|---|---|---|
| Eqs. (26), (30) | `krylovFamily`, `timeEvolution_eigenbasis` | Actual operator exponentials and their action in the eigenbasis. |
| Eq. (32), time shift | `timeEvolution_add`, `timeEvolution_inner`, `timeEvolution_energy_inner`, `unshift_centered_sum` | Norms, inner products, and energies are preserved by the common shift; integer frequencies are reindexed to `Fin d`. |
| Eqs. (33)–(34) | `chebyshevFilter_zero`, `chebyshevFilter_abs_le_one`, `chebyshevFilter_off_band` | Concrete filter, normalization, uniform bound, and exponential suppression. |
| Eq. (35), finite expansion | `chebyshevFilter_exists_expansion` | The frequency support is contained in `[-m,m]`. |
| Eq. (35), coefficient control | `chebyshevFilter_bounded_expansion`, `filterFourierCoeff_sum_sq_le_one` | Bounded coefficients for the same finite expansion; Parseval for integral-defined coefficients. |
| Eq. (36), filtered state | `centered_filter_identity` | The spectral filter equals the centered physical time-evolution sum, including the ground-energy phase correction. |
| Eq. (37), norm lower bound | `filteredCoordinates_ground_lower`, `normalizedCoordinates_norm` | The ground coordinate is preserved; the filtered norm is at least the initial overlap. |
| Eqs. (38)–(39), Rayleigh quotient | `eigenbasis_energy`, `filtered_numerator_bound`, `filtered_rayleigh_bound`, `spectral_chebyshev_energy` | Energy gaps are weighted by filtered spectral probabilities; normalization and the filter bound give the stated error. |
| Simultaneous witness | `exists_centered_krylov_witness`, `exists_exactKrylovWitness_odd` | Normalization, coefficient control, and energy control hold for one and the same state. |
| Endpoint `gap = W` | `two_level_projection`, `exists_exactKrylovWitness_two_levels` | Two time samples isolate the ground component exactly; the singular Chebyshev formula is not used. |
| Dimension one | `exists_exactKrylovWitness_one` | The initial state directly satisfies the loose bound. |
| Even dimension | `ExactKrylovWitness.pad`, `effectiveOddDimension_cases` | Add a zero coefficient and retain the preceding odd dimension's error. |
| Complete witness interface | `exists_exactKrylovWitness` | Supplies the witness for every positive dimension from the spectral inputs. |

The spectral proof uses `E_j-E₀`, not an unjustified replacement by `E_j`.
The norm denominator is the squared norm, not its square again. These are
the mathematically intended quantities despite the v1 display issues.

## Appendix B correspondence

| Paper item | Lean declarations |
|---|---|
| Sparsity definition | `Sparse`, `hitProb`, `supportMass` |
| Lemma 1: energy to state error | `lemma1_state_error`; phase is supplied by `align_combination` |
| Lemma 2: transfer of sparsity | `lemma2_sparsity_transfer` |
| Lemma 3: some Krylov state hits each important string | `lemma3_krylov_hit` |
| Lemma 4: independent sampling and union bound | `iidBornMiss_of_independent`, `samplingFailure_measure_le`, `paper_sampling_failure_le_eta` |
| Lemma 5: truncated ground-state energy | `lemma5_truncated_energy`, `theorem1_energy` |
| Exact sampled-space minimization | `exists_minimizerOn`, `exactSKQDOutput_spec` |
| Successful sampling implies good energy | `badEnergy_subset_samplingFailure` |
| Final composition | `paper_theorem1` |
| Measurable success probability | `measurable_exactSKQDOutput`, `success_probability_of_bad_probability` |

## Resource bounds and their scope

`Resources.lean` proves the logarithmic odd-dimension choice
`sufficientOddDimension_error`, positivity and rounding of integer shot
counts, and the retained-sparsity estimate

```text
ε ≤ gap β²/32  ⇒  β - 2 sqrt(et) ≥ β/2.
```

It also proves an explicitly polynomial, looser choice. For `C ≥ 0`, `a > 0`,
and target `τ > 0`, set

```text
d = 2 ceil(C/(2τa)) + 1.
```

Then `C/(1+a)^(d-1) ≤ τ` and `d < C/(τa)+3`.
Taking `C=8W(1-g)/g` and `a=π gap/W` yields a rational resource bound in
the bandwidth, inverse overlap, inverse gap, and inverse target error.
`sampledSupport_card_le` bounds the projected-space dimension by `d M`.

The automatic choice uses `τ=gap β²/32`. From the ground-state sparsity
assumption and normalization, the constructive theorem derives `β≤1`,
and hence `ε≤τ≤gap`. It proves positive retained sparsity and supplies the
rounded sample count; the caller supplies none of these consequences.

For a common envelope `R≥1` satisfying

```text
W, 1/g, 1/gap, 1/β, L, log(L/η) ≤ R,
```

the proved finite bounds include

```text
d ≤ 260 R^7
M ≤ 140000 R^18
d M ≤ 36400000 R^25       (by multiplication)
d π/W ≤ 1040 R^8.
```

`ResourceEnvelope` records only individual input-parameter bounds and
positivity conditions. If `R(n)=K(n+1)^p`, `resourceCounts_isBigO` proves

```text
d(n) = O((n+1)^(7p))
M(n) = O((n+1)^(18p))
d(n) M(n) = O((n+1)^(25p)).
```

`evolutionTime_isBigO` proves the `O((n+1)^(8p))` bound on the maximum
time-evolution duration. These exponents are deliberately loose sufficient
bounds, not claims that the paper's sharper logarithmic estimates are tight.
The confidence cost is logarithmic in `1/η`, as in the paper; no polynomial
bound on `1/η` itself is assumed.

The classical sampled-subspace dimension is bounded by total samples.
Polynomial resource scaling is now formalized. There is still no verified
implementation of the classical eigensolver, its bit-complexity, or its
floating-point accuracy: the exact minimizer is a mathematical specification,
as appropriate for the ideal guarantee.

## Verification

Latest validation: `lake build` succeeded (17,444 jobs), the guarded axiom
audit succeeded, and the source scan found no proof holes, custom axioms,
`sorryAx`, or `native_decide`.

```bash
lake build
lake env lean LeanExperiments/SKQD/Audit.lean
rg -n '\bsorry\b|\badmit\b|^axiom\b|sorryAx|native_decide' LeanExperiments/SKQD
```

The dependency audit uses `#guard_msgs` around `#print axioms`. The guarded
theorems may depend on `propext`, `Classical.choice`, and `Quot.sound` only;
a changed dependency list fails the audit. This includes the final theorem
and the newly constructed witness, not merely the old conditional reduction.
CI runs the audit explicitly. Dimension-one, odd/even rounding, zero-overlap
phase selection, and integer-shot examples provide additional regression checks.
