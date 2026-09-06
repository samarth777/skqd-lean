# A Machine-Checked Convergence Proof for Sample-Based Krylov Quantum Diagonalization

## Paper-to-Lean correspondence, proof architecture, equations, and trust audit

This report documents the Lean 4 formalization of the ideal convergence guarantee in
J. Yu *et al.*, [*Sample-based Krylov Quantum Diagonalization*](https://arxiv.org/html/2501.09702v1),
arXiv:2501.09702v1 (16 January 2025). The mathematical scope is the convergence
argument in Section III and Appendices A–B: the Krylov approximation theorem,
the five sampling/sparsity lemmas, and their composition into Theorem 1.

The result proved in Lean is end-to-end at the same idealized mathematical level as
the paper. The final theorem starts from spectral data, a sparse ground state, and
independent exact Born samples. It constructs the Krylov approximation witness,
defines exact diagonalization on the sampled subspace, and proves the claimed
high-probability energy bound. A second theorem chooses the Krylov dimension and
shot count automatically.

The report deliberately separates this convergence theorem from the paper's
experimental claims. It does not formalize noisy gates, Trotter error, configuration
recovery, numerical eigensolver roundoff, or the hardware experiments.

## 1. Coverage of the paper's named mathematical results

| Paper result | Role | Lean status | Principal declaration |
|---|---|---|---|
| Definition 1 | $(\alpha_L,\beta_L)$-sparsity | Formalized | `Sparse` |
| Theorem 1 | SKQD energy and success guarantee | Formalized end-to-end | `paper_theorem1`, `paper_theorem1_constructive` |
| Theorem 2 | Ideal KQD exponential convergence | Formalized and used | `spectral_chebyshev_energy`, `exists_exactKrylovWitness` |
| Lemma 1 | Low energy implies closeness to the ground state | Formalized | `lemma1_state_error` |
| Lemma 2 | Closeness transfers sparsity | Formalized | `lemma2_sparsity_transfer` |
| Lemma 3 | Every important string is visible in a Krylov state | Formalized | `lemma3_krylov_hit` |
| Lemma 4 | Independent sampling plus union bound | Formalized measure-theoretically | `samplingFailure_measure_le`, `paper_sampling_failure_le_eta` |
| Lemma 5 | Truncating a sparse ground state preserves low energy | Formalized | `lemma5_truncated_energy` |
| Theorem 3 | Ising-model example establishing sparsity | Not part of the convergence theorem | Not formalized |

Theorem 3 in Appendix E is a model-specific argument offered as evidence for the
sparsity assumption. Theorem 1 assumes sparsity, so Theorem 3 is not a dependency
of the convergence guarantee proved here.

## 2. Mathematical setting and notation

Let $\mathcal H$ be a finite-dimensional complex Hilbert space. The Lean development
uses `EuclideanSpace ℂ ι`, where the finite type `ι` indexes both coordinates and an
orthonormal eigenbasis. Let

$$
H\lvert\phi_j\rangle=E_j\lvert\phi_j\rangle,
\qquad
\langle\phi_i\mid\phi_j\rangle=\delta_{ij}.
$$

Choose a ground-state index $j_0$, write

$$
E_0:=E_{j_0},
\qquad
\gamma_0:=\langle\phi_0\mid\psi_0\rangle,
\qquad
g:=\lvert\gamma_0\rvert^2,
$$

and assume every non-ground eigenvalue satisfies

$$
0<\Delta\le E_j-E_0\le W,
\qquad j\ne j_0.
$$

Here $\Delta$ is the spectral-gap lower bound and $W$ is the spectral-bandwidth
upper bound. The paper's choice of time step is

$$
\Delta t=\frac{\pi}{W}.
$$

The $d$ Krylov states are

$$
\lvert\psi_k\rangle=e^{-ikH\Delta t}\lvert\psi_0\rangle,
\qquad k=0,\ldots,d-1.
\tag{26}
$$

In Lean these are genuine operator exponentials:

```lean
noncomputable def timeEvolution (H : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  ((-(t : ℂ) * Complex.I) • H).exp

noncomputable def krylovFamily
    (H : E →L[ℂ] E) (ψ₀ : E) (Δt : ℝ) (d : ℕ) : Fin d → E :=
  fun k => timeEvolution H ((k : ℝ) * Δt) ψ₀
```

Self-adjointness is represented by `IsSymmetric`. It is used to prove that time
evolution preserves norms and energy expectations:

```lean
theorem timeEvolution_norm ... : ‖timeEvolution H t ψ‖ = ‖ψ‖
theorem timeEvolution_energy_inner ... :
  inner ℂ (timeEvolution H t x) (H (timeEvolution H t y)) = inner ℂ x (H y)
```

## 3. Definition 1: sparsity

For a normalized state

$$
\lvert\psi\rangle=\sum_j g_j\lvert b_j\rangle
$$

and a set $S$ of $L$ important computational-basis strings, the paper requires

$$
\sum_{j\in S}\lvert g_j\rvert^2\ge\alpha_L,
\tag{6}
$$

and

$$
\lvert g_j\rvert^2\ge\beta_L
\qquad\text{for every }j\in S.
\tag{7}
$$

The formal definition does not require an ordering of all basis strings. The finite
set `s` directly identifies the important strings, which is the invariant actually
used by the proof:

```lean
noncomputable def hitProb (ψ : EuclideanSpace ℂ ι) (j : ι) : ℝ :=
  ‖ψ j‖ ^ 2

structure Sparse (ψ : EuclideanSpace ℂ ι)
    (s : Finset ι) (α β : ℝ) : Prop where
  mass : α ≤ ∑ j ∈ s, hitProb ψ j
  pointwise : ∀ j ∈ s, β ≤ hitProb ψ j
```

Thus `Sparse ψ s α β` is exactly the pair of inequalities above.

## 4. Appendix A: formal proof of KQD convergence

### 4.1 Paper Theorem 2

For odd $d$, the paper states

$$
0\le \widetilde E_0-E_0
\le
8W\frac{1-g}{g}
\left(1+\frac{\pi\Delta}{W}\right)^{-(d-1)}.
\tag{31}
$$

For even $d$, the stated convention is to use the preceding odd dimension. Lean
therefore defines

$$
d_{\mathrm{eff}}
=2\left\lfloor\frac{d-1}{2}\right\rfloor+1
$$

and

$$
\varepsilon_K(W,\Delta,g,d)
:=
\frac{8W(1-g)/g}
{\left(1+\pi\Delta/W\right)^{d-1}}.
$$

```lean
noncomputable def paperKrylovError
    (W gap overlapSq : ℝ) (d : ℕ) : ℝ :=
  (8 * W * (1 - overlapSq) / overlapSq) /
    (1 + Real.pi * gap / W) ^ (d - 1)

def effectiveOddDimension (d : ℕ) : ℕ :=
  2 * ((d - 1) / 2) + 1
```

The public witness theorem proves that the required normalized Krylov combination
exists for every positive dimension:

```lean
theorem exists_exactKrylovWitness
    ... (d : ℕ) (gap W : ℝ)
    ... (hd : 0 < d) (hgap : 0 < gap) (hgapW : gap ≤ W)
    (he : ∀ j, j ≠ j₀ →
      gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    Nonempty (ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap
        (‖inner ℂ (b j₀) ψ₀‖ ^ 2)
        (effectiveOddDimension d)) d)
```

This theorem is stronger as an interface than merely postulating the KQD error:
it produces one combination whose normalization, coefficient bound, and energy
bound hold simultaneously.

### 4.2 Shifted Krylov space, Eq. (32)

For $d=2m+1$, Appendix A works with frequencies $k=-m,\ldots,m$:

$$
\lvert\psi_k\rangle=e^{-ikH\Delta t}\lvert\psi_0\rangle.
\tag{32}
$$

Lean proves the group law, commutation with $H$, and preservation of the relevant
quadratic forms. It then reindexes the centered sum into the original `Fin d`
family:

```lean
theorem unshift_centered_sum ... :
  (∑ j : Fin (2 * m + 1),
      c ((m : ℤ) - (j : ℕ)) • krylovFamily H ψ₀ t (2 * m + 1) j) =
    timeEvolution H ((m : ℝ) * t)
      (∑ k ∈ Finset.Icc (-(m : ℤ)) m,
        c k • timeEvolution H (-(k : ℝ) * t) ψ₀)
```

The common outer time evolution changes neither norm nor energy, so this is the
formal justification for transferring the centered filter state to the paper's
unshifted Krylov family.

### 4.3 Chebyshev filter, Eqs. (33)–(35)

With $m=(d-1)/2$ and $0<a<\pi$, the paper uses a trigonometric polynomial
$p_m^*$ such that

$$
p_m^*(0)=1,
\qquad
\lvert p_m^*(\theta)\rvert
\le 2(1+a)^{-m}
\quad\text{when }a\le\lvert\theta\rvert\le\pi.
\tag{33}
$$

Its explicit Chebyshev form is

$$
p_m^*(\theta)=
\frac{
T_m\!\left(1+2\dfrac{\cos\theta-\cos a}{1+\cos a}\right)
}{
T_m\!\left(1+2\dfrac{1-\cos a}{1+\cos a}\right)
}.
\tag{34}
$$

The Lean definition follows this formula:

```lean
noncomputable def filterArgument (a θ : ℝ) : ℝ :=
  1 + 2 * (Real.cos θ - Real.cos a) / (Real.cos a + 1)

noncomputable def chebyshevFilter (m : ℕ) (a θ : ℝ) : ℝ :=
  Polynomial.Chebyshev.T ℝ m (filterArgument a θ) /
    Polynomial.Chebyshev.T ℝ m (filterArgument a 0)
```

The corresponding machine-checked properties are:

```lean
theorem chebyshevFilter_zero ... : chebyshevFilter m a 0 = 1
theorem chebyshevFilter_abs_le_one ... : |chebyshevFilter m a θ| ≤ 1
theorem chebyshevFilter_off_band ... :
  |chebyshevFilter m a θ| ≤ 2 / (1 + a) ^ m
```

The finite Fourier expansion is

$$
p_m^*(\theta)=\sum_{k=-m}^{m}c_ke^{ik\theta},
\qquad
\sum_{k=-m}^{m}\lvert c_k\rvert^2\le1.
\tag{35}
$$

Lean proves both finite spectral support and the coefficient estimate:

```lean
theorem chebyshevFilter_bounded_expansion ... :
  ∃ c : ℤ → ℂ,
    (∀ k ∈ Finset.Icc (-(m : ℤ)) m, ‖c k‖ ≤ 1) ∧
    ∀ θ, ∑ k ∈ Finset.Icc (-(m : ℤ)) m,
      c k * phaseMode k θ = (chebyshevFilter m a θ : ℂ)

theorem filterFourierCoeff_sum_sq_le_one ... :
  ∑ k ∈ Finset.Icc (-(m : ℤ)) m,
    ‖filterFourierCoeff m a k‖ ^ 2 ≤ 1
```

The proof uses the trigonometric-span development and Parseval's inequality; the
Fourier coefficients are not introduced as uninterpreted constants.

### 4.4 Filtered state and the operator-exponential bridge, Eq. (36)

The paper's unnormalized filtered state is

$$
\lvert\widetilde\phi_K\rangle
=\sum_{k=-m}^{m}c_k\lvert\psi_k\rangle
=\sum_j\gamma_j p_m^*((E_j-E_0)\Delta t)\lvert\phi_j\rangle.
\tag{36}
$$

The phase shift by $E_0$ and the sign in $e^{-itH}$ must match exactly. Lean makes
that adjustment explicit with

```lean
noncomputable def centeredFilterCoeff
    (c : ℤ → ℂ) (E₀ t : ℝ) (k : ℤ) : ℂ :=
  c k * phaseMode k (-E₀ * t)
```

and proves the physical/spectral identity:

```lean
theorem centered_filter_identity ... :
  (∑ k ∈ Finset.Icc (-(m : ℤ)) m,
      centeredFilterCoeff c E₀ t k •
        timeEvolution H (-(k : ℝ) * t) (b.repr.symm u)) =
    b.repr.symm
      (filteredCoordinates u
        (fun j => (chebyshevFilter m a ((e j - E₀) * t) : ℂ)))
```

This closes a common formalization gap: the polynomial filter is proved to be the
same vector as a finite linear combination of actual time evolutions.

### 4.5 Norm lower bound, Eq. (37)

Since $p_m^*(0)=1$, the ground coordinate survives unchanged:

$$
\|\widetilde\phi_K\|^2
=\sum_j\lvert\gamma_j\rvert^2
  \lvert p_m^*((E_j-E_0)\Delta t)\rvert^2
\ge\lvert\gamma_0\rvert^2.
\tag{37}
$$

The core Lean lemma is

```lean
lemma filteredCoordinates_ground_lower ...
    (hq₀ : q j₀ = 1) :
    ‖u j₀‖ ≤ ‖filteredCoordinates u q‖
```

Consequently, normalizing the filter multiplies each Fourier coefficient by at
most $1/\lvert\gamma_0\rvert$. This produces precisely the coefficient contract
needed in Appendix B:

$$
\lvert d_k\rvert\,\lvert\gamma_0\rvert\le1.
\tag{44}
$$

### 4.6 Rayleigh-quotient estimate, Eqs. (38)–(39)

For the normalized filtered state, the energy error is

$$
\frac{
  \sum_{j\ne0}(E_j-E_0)\lvert\gamma_j\rvert^2
  \lvert p_m^*((E_j-E_0)\Delta t)\rvert^2
}{
  \sum_j\lvert\gamma_j\rvert^2
  \lvert p_m^*((E_j-E_0)\Delta t)\rvert^2
}.
\tag{38}
$$

The denominator is at least $g$, every excited gap is at most $W$, and the filter
is at most $2(1+\pi\Delta/W)^{-m}$. Hence Lean first obtains the sharper estimate

$$
E(\widehat\phi_K)-E_0
\le
4W\frac{1-g}{g}
\left(1+\frac{\pi\Delta}{W}\right)^{-2m},
$$

and then weakens the constant $4$ to the paper's constant $8$:

$$
E(\widehat\phi_K)-E_0
\le
8W\frac{1-g}{g}
\left(1+\frac{\pi\Delta}{W}\right)^{-(d-1)}.
\tag{39}
$$

The main formal declarations are:

```lean
theorem eigenbasis_energy ...
theorem filtered_numerator_bound ...
theorem filtered_rayleigh_bound ...
theorem normalized_eigenbasis_energy ...
theorem normalized_filtered_energy_bound ...
theorem spectral_chebyshev_energy ...
```

`spectral_chebyshev_energy` concludes both normalization and the paper's exact
error formula for $d=2m+1$.

### 4.7 Endpoint and parity cases

The Chebyshev proof naturally assumes $\Delta<W$. The paper permits
$\Delta\le W$, so Lean separately handles $\Delta=W$. In that case every excited
energy equals $E_0+W$, and two time samples project out all excited components:

$$
\frac12\lvert\psi_0\rangle
+\frac12e^{iE_0\pi/W}e^{-iH\pi/W}\lvert\psi_0\rangle
=\gamma_0\lvert\phi_0\rangle.
$$

This is `two_level_projection`. The declarations
`exists_exactKrylovWitness_two_levels` and
`exists_exactKrylovWitness_one` cover $d\ge2$ and $d=1$, respectively.

For even $d$, `ExactKrylovWitness.pad` appends a zero coefficient. The theorem
`effectiveOddDimension_cases` proves that every positive $d$ is either its
effective odd dimension or one larger. Together these results prove
`exists_exactKrylovWitness` for every $d>0$ and every $0<\Delta\le W$.

## 5. Appendix B: sparsity and sampling lemmas

Define the KQD energy error $\varepsilon$ by Theorem 2 and set

$$
\widetilde\varepsilon
=2\left(1-\sqrt{1-\frac{\varepsilon}{\Delta}}\right).
\tag{45}
$$

In Lean:

```lean
noncomputable def epsTilde (ε ΔE₁ : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (1 - ε / ΔE₁))
```

### 5.1 Lemma 1: energy error implies state error

The paper decomposes a normalized state into ground and orthogonal parts:

$$
\lvert\psi\rangle
=\chi_0\lvert\phi_0\rangle
+\chi^\perp\lvert\phi^\perp\rangle.
$$

The spectral gap gives

$$
\langle\psi\rvert H\lvert\psi\rangle-E_0
\ge(1-\lvert\chi_0\rvert^2)\Delta.
\tag{47}
$$

After choosing a global phase so that $\chi_0$ is real and nonnegative,

$$
\|\psi-\phi_0\|^2
=2-2\chi_0
\le
2\left(1-\sqrt{1-\frac{\varepsilon}{\Delta}}\right)
=\widetilde\varepsilon.
\tag{48}
$$

Lean represents the spectral-gap premise through `GroundStateGap`, including the
Rayleigh lower bound on every normalized vector orthogonal to the ground state.
The final theorem derives this structure from the eigenbasis assumptions using
`groundStateGap_of_eigenbasis`.

```lean
theorem lemma1_state_error
    ...
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hψ : ‖ψ‖ = 1)
    (hphase : (inner ℂ φ₀ ψ).im = 0)
    (hpos : 0 ≤ (inner ℂ φ₀ ψ).re)
    (hεgap : ε ≤ ΔE₁)
    (herr : (inner ℂ ψ (H ψ)).re - E₀ ≤ ε) :
    ‖ψ - φ₀‖ ^ 2 ≤
      2 * (1 - Real.sqrt (1 - ε / ΔE₁))
```

The paper states that the overlap is real. Lean uses `align_combination` to prove
that a global phase can always make it real and nonnegative without changing the
norm, coefficient magnitudes, or energy expectation.

### 5.2 Lemma 2: perturbation transfers sparsity

If $\phi_0$ is $(\alpha_L^{(0)},\beta_L^{(0)})$-sparse and
$\|\psi-\phi_0\|^2\le\delta$, then

$$
\alpha_L=\alpha_L^{(0)}-2\sqrt\delta,
\qquad
\beta_L=\beta_L^{(0)}-2\sqrt\delta.
\tag{49}
$$

For the support mass, Cauchy–Schwarz gives

$$
\sum_{j\in S}\lvert a_j\rvert^2
\ge
\alpha_L^{(0)}
-2\sqrt{
  \sum_{j\in S}\lvert c_j\rvert^2
  \sum_{j\in S}\lvert a_j-c_j\rvert^2
}
\ge\alpha_L^{(0)}-2\sqrt\delta.
\tag{50--53}
$$

Pointwise,

$$
\lvert a_j\rvert^2
\ge\lvert c_j\rvert^2-2\lvert c_j\rvert\lvert a_j-c_j\rvert
\ge\beta_L^{(0)}-2\sqrt\delta.
\tag{54--56}
$$

The corresponding theorem constructs the entire `Sparse` structure:

```lean
theorem lemma2_sparsity_transfer
    (hφ : ‖φ‖ = 1) (hε : 0 ≤ ε)
    (hs : Sparse φ s α β)
    (hdist : ‖ψ - φ‖ ^ 2 ≤ ε) :
    Sparse ψ s
      (α - 2 * Real.sqrt ε)
      (β - 2 * Real.sqrt ε)
```

### 5.3 Lemma 3: an important string appears in a Krylov state

Let

$$
\lvert\widehat\phi_K\rangle
=\sum_{k=0}^{d-1}d_k\lvert\psi_k\rangle,
\qquad
\lvert d_k\rvert\,\lvert\gamma_0\rvert\le1.
$$

For an important string $j$, its amplitude in the combination is at least
$\sqrt{\beta_L}$. The triangle inequality yields

$$
\sum_{k=0}^{d-1}\lvert c_j^{(k)}\rvert
\ge
\lvert\gamma_0\rvert\sqrt{\beta_L}.
\tag{58}
$$

Therefore at least one $k$ satisfies

$$
\lvert c_j^{(k)}\rvert^2
\ge
p,
\qquad
p:=\frac{\lvert\gamma_0\rvert^2\beta_L}{d^2}.
\tag{57}
$$

Lean proves this for an arbitrary finite index type `κ`, not only `Fin d`:

```lean
theorem lemma3_krylov_hit
    (coeff : κ → ℂ)
    (krylov : κ → EuclideanSpace ℂ ι)
    (γ : ℂ) (β : ℝ) (j : ι)
    (hd : 0 < Fintype.card κ)
    (hcoeff : ∀ k, ‖coeff k‖ * ‖γ‖ ≤ 1)
    (hβnn : 0 ≤ β)
    (hβ : β ≤ hitProb (∑ k, coeff k • krylov k) j) :
    ∃ k,
      ‖γ‖ ^ 2 * β / (Fintype.card κ : ℝ) ^ 2
        ≤ hitProb (krylov k) j
```

### 5.4 Lemma 4: independent sampling and the union bound

With $M$ independent measurements from each Krylov state, the probability of
missing an important string whose best-state Born probability is at least $p$ is
at most $(1-p)^M$. A union bound over $L$ important strings gives

$$
p_{\mathrm{fail}}
\le L(1-p)^M
\le Le^{-Mp}.
\tag{59}
$$

The Lean development models actual random variables
`samples : κ → Fin M → Ω → ι`. The theorem `iidBornMiss_of_independent` derives
the exact repeated-miss probability from measurability, independence, and exact
Born marginals. Then

```lean
theorem samplingFailure_measure_le ...
    (hhit : ∀ j ∈ s, ∃ k, p ≤ hitProb (krylov k) j) :
    μ.real (samplingFailure samples s) ≤
      (s.card : ℝ) * (1 - p) ^ M
```

and

```lean
theorem paper_sampling_failure_le_eta ...
    (hM :
      ((d : ℝ) ^ 2 * Real.log ((L : ℝ) / η)) /
        (γsq * β) ≤ (M : ℝ)) :
    failureProbability ≤ η
```

formalize both parts of the paper's probability argument. The latter uses

$$
M\ge\frac{d^2\log(L/\eta)}{g\beta_L}
\quad\Longrightarrow\quad
Le^{-Mp}\le\eta.
$$

### 5.5 Lemma 5: energy of the truncated ground state

Let $P_S$ be projection onto the important computational strings and define

$$
C:=\|P_S\phi_0\|,
\qquad
\lvert\widetilde\phi\rangle:=\frac{P_S\lvert\phi_0\rangle}{C}.
$$

Sparsity implies $C^2\ge\alpha_L^{(0)}$. Direct calculation gives

$$
\|\widetilde\phi-\phi_0\|^2=2-2C
\le2\left(1-\sqrt{\alpha_L^{(0)}}\right).
\tag{63}
$$

The energy expectation is Lipschitz on unit vectors:

$$
\left\lvert
\langle\widetilde\phi\rvert H\lvert\widetilde\phi\rangle
-\langle\phi_0\rvert H\lvert\phi_0\rangle
\right\rvert
\le2\|H\|\,\|\widetilde\phi-\phi_0\|.
\tag{61--62}
$$

Combining the two estimates gives

$$
\left\lvert
\langle\widetilde\phi\rvert H\lvert\widetilde\phi\rangle-E_0
\right\rvert
\le
\sqrt8\,\|H\|\sqrt{1-\sqrt{\alpha_L^{(0)}}}.
\tag{60}
$$

Lean defines coordinate restriction and normalization as `restrict` and
`truncated`, proves the exact norm and overlap identities, and concludes:

```lean
theorem lemma5_truncated_energy ...
    (hφ : ‖φ‖ = 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hs : Sparse φ s α β) :
    abs ((inner ℂ (truncated φ s) (H (truncated φ s))).re -
      (inner ℂ φ (H φ)).re) ≤
      Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α)
```

## 6. Exact diagonalization on the sampled subspace

For a sampling outcome $\omega$, Lean constructs the finite support

$$
B_{d,M}(\omega)
=\{a_{km}(\omega):0\le k<d,\ 0\le m<M\}.
\tag{8}
$$

`MinimizerOn H s ψ` states that $\psi$ is normalized, supported on `s`, and has
energy no larger than any other normalized vector supported there. Compactness of
the unit sphere in the finite coordinate subspace proves existence:

```lean
theorem exists_minimizerOn ...
    (s : Finset ι) (hs : s.Nonempty) :
    ∃ ψ, MinimizerOn H s ψ

noncomputable def exactSKQDOutput ... (ω : Ω) : EuclideanSpace ℂ ι :=
  Classical.choose
    (exists_minimizerOn H (sampledSupport samples ω) ...)
```

If all important strings were sampled, the truncated ground state belongs to the
sampled subspace. Variational minimality then makes the SKQD output no worse than
that truncated state. This contrapositive is formalized by

```lean
theorem badEnergy_subset_samplingFailure ... :
  {ω | bound < energy (output ω) - E₀} ⊆
    samplingFailure samples s
```

The output is a mathematical exact minimizer. `measurable_exactSKQDOutput` proves
that it is measurable as a function of the finite tuple of samples, allowing the
final success event to have an ordinary probability.

## 7. Appendix B.1 and paper Theorem 1

Substitute the KQD error

$$
\varepsilon
=8W\frac{1-g}{g}
\left(1+\frac{\pi\Delta}{W}\right)^{-(d_{\mathrm{eff}}-1)}
\tag{64}
$$

into Lemma 1 and define

$$
\varepsilon'
=\sqrt{1-\frac{\varepsilon}{\Delta}},
\qquad
\widetilde\varepsilon=2-2\varepsilon'.
\tag{65--66}
$$

Lemma 2 gives retained sparsity

$$
\alpha_L
=\alpha_L^{(0)}-2\sqrt{\widetilde\varepsilon},
\qquad
\beta_L
=\beta_L^{(0)}-2\sqrt{\widetilde\varepsilon}.
\tag{67}
$$

Lemma 3 gives the per-string hit probability

$$
p
=\frac{g}{d^2}
\left(\beta_L^{(0)}-2\sqrt{\widetilde\varepsilon}\right).
\tag{68}
$$

Lemma 4 then gives

$$
p_{\mathrm{fail}}
\le
L\exp\!\left[
-\frac{Mg}{d^2}
\left(\beta_L^{(0)}-2\sqrt{\widetilde\varepsilon}\right)
\right].
\tag{69}
$$

Thus $p_{\mathrm{fail}}\le\eta$ whenever

$$
M\ge
\frac{d^2\log(L/\eta)}
{g\left(\beta_L^{(0)}-2\sqrt{\widetilde\varepsilon}\right)}.
$$

On the complementary event, Lemma 5 and variational minimality give

$$
E_{\mathrm{SKQD}}-E_0
\le
\sqrt8\,\|H\|
\sqrt{1-\sqrt{\alpha_L^{(0)}}}.
\tag{70}
$$

The principal paper-level theorem is `paper_theorem1`. Its conclusion is the bad
event formulation

$$
\Pr\!\left[
E_{\mathrm{SKQD}}-E_0
>
\sqrt8\,\|H\|\sqrt{1-\sqrt\alpha}
\right]
\le\eta.
$$

Its Lean proof has the following high-level form:

```lean
theorem paper_theorem1 ... :
    μ.real {ω |
      Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) <
        energy (exactSKQDOutput H samples ... ω) - e j₀} ≤ η := by
  have hg := groundStateGap_of_eigenbasis ...
  obtain ⟨w⟩ := exists_exactKrylovWitness ...
  have hε : 0 ≤ ε := by ...
  exact exact_krylov_probabilistic ... hg ... w ...
```

There is no assumed `ExactKrylovWitness` in this theorem. It is constructed from
the eigenbasis, spectral gap, bandwidth, and reference overlap.

`success_probability_of_bad_probability` converts the result to the more familiar
success statement:

$$
\Pr\!\left[
E_{\mathrm{SKQD}}-E_0
\le
\sqrt8\,\|H\|\sqrt{1-\sqrt\alpha}
\right]
\ge1-\eta.
$$

## 8. Fully constructive parameter choice

The theorem `paper_theorem1_constructive` removes four obligations from the user:
it chooses $d$ and $M$, proves the KQD error lies in the required domain, proves
that retained sparsity is positive, and proves the shot inequality.

It selects the target

$$
\tau:=\frac{\Delta\beta^2}{32}
$$

and an explicit odd dimension

$$
d
=2\left\lceil
\frac{C}{2\tau a}
\right\rceil+1,
\qquad
C:=\frac{8W(1-g)}{g},
\qquad
a:=\frac{\pi\Delta}{W}.
$$

Bernoulli's inequality proves

$$
\frac{C}{(1+a)^{d-1}}\le\tau.
$$

Since $0<\beta\le1$, one has $\tau\le\Delta$. Lean also proves

$$
\widetilde\varepsilon
\le\frac{2\varepsilon}{\Delta}
$$

and therefore

$$
\varepsilon\le\frac{\Delta\beta^2}{32}
\quad\Longrightarrow\quad
\beta-2\sqrt{\widetilde\varepsilon}\ge\frac\beta2>0.
$$

The shot count is the positive natural-number ceiling of the paper threshold:

$$
M
=\max\!\left(
1,
\left\lceil
\frac{d^2\log(L/\eta)}
{g(\beta-2\sqrt{\widetilde\varepsilon})}
\right\rceil
\right).
$$

The final theorem concludes directly:

```lean
theorem paper_theorem1_constructive ... :
  1 - η ≤ μ.real {ω |
    energy (exactSKQDOutput H samples ... ω) - e j₀ ≤
      Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α)}
```

Its assumptions are only the finite-dimensional spectral data, normalized initial
state with positive ground overlap, sparse ground state, valid confidence level,
and measurable independent samples having the correct Born marginals.

## 9. Formal polynomial-resource corollaries

The paper describes polynomial convergence under polynomial control of bandwidth,
inverse gap, inverse overlap, inverse sparsity, support size, and confidence cost.
Lean records these hypotheses in `ResourceEnvelope`:

$$
W,\ g^{-1},\ \Delta^{-1},\ \beta^{-1},\ L,
\ \log(L/\eta)\le R,
\qquad R\ge1.
$$

For the explicit sufficient choices above, Lean proves the deliberately loose
finite bounds

$$
d\le260R^7,
\qquad
M\le140000R^{18},
\qquad
dM\le36400000R^{25},
$$

and a maximum time-evolution duration bounded by

$$
T_{\max}\le\frac{d\pi}{W}\le1040R^8.
$$

For an envelope $R(n)=K(n+1)^p$, the actual Mathlib asymptotic predicate
`Asymptotics.IsBigO` is used:

```lean
theorem resourceCounts_isBigO ... :
  IsBigO atTop d       (fun n => (n + 1) ^ (7 * p)) ∧
  IsBigO atTop M       (fun n => (n + 1) ^ (18 * p)) ∧
  IsBigO atTop total   (fun n => (n + 1) ^ (25 * p))

theorem evolutionTime_isBigO ... :
  IsBigO atTop maxTime (fun n => (n + 1) ^ (8 * p))
```

These exponents are sufficient upper bounds, not optimality claims. The sharper
exponential-in-$d$ KQD inequality remains available separately. The dependence on
confidence is through $\log(L/\eta)$, matching the paper rather than requiring
$1/\eta$ itself to be polynomially bounded.

## 10. Proof dependency graph

```text
operator exponential + spectral basis
                │
                ├── Chebyshev off-band estimate
                ├── finite Fourier expansion and coefficient control
                └── physical/spectral filter identity
                                │
                                ▼
                 exact normalized Krylov witness
                 (all positive d, endpoint included)
                                │
                 energy-to-state Lemma 1
                                │
                 sparsity-transfer Lemma 2
                                │
                 Krylov-hit Lemma 3
                                │
          independent sampling + union bound Lemma 4
                                │
              all important strings are sampled
                                │
       truncation Lemma 5 + exact variational minimizer
                                │
                                ▼
            paper_theorem1 / paper_theorem1_constructive
```

## 11. Assumptions and exact scope

The end-to-end theorem assumes:

1. A finite-dimensional complex Hilbert space.
2. An orthonormal eigenbasis with real eigenvalues and the eigenvector equations.
3. Self-adjointness of $H$.
4. A normalized reference state with $g>0$.
5. Spectral bounds $0<\Delta\le E_j-E_0\le W$ for every excited eigenvector.
6. $(\alpha,\beta)$-sparsity of the ground state on a nonempty finite support.
7. Positive failure tolerance $\eta$.
8. Measurable, independent, exact Born samples from every Krylov state.

It does **not** assume:

- the existence of a good Krylov combination;
- an energy approximation as a premise;
- the coefficient estimate in Eq. (44);
- a phase-alignment premise;
- an abstract ground-gap structure independent of the spectral data;
- the required dimension or sample count in the constructive theorem.

The formal theorem remains idealized in exactly the relevant ways: time evolution
is the exact operator exponential, measurement marginals are exact Born
probabilities, and classical diagonalization is specified as an exact minimizer.

## 12. Treatment of display issues in arXiv v1

The v1 HTML contains several expressions whose surrounding proof makes the intended
quantity clear. The Lean development uses the mathematically consistent forms:

- Eq. (37) is treated as the squared norm
  $\|\widetilde\phi_K\|^2=\langle\widetilde\phi_K\mid\widetilde\phi_K\rangle$,
  not the square of that inner product again.
- The normalized coefficient denominator is the norm
  $\|\widetilde\phi_K\|$, giving
  $\lvert d_k\rvert\le1/\lvert\gamma_0\rvert$.
- Spectral filtering uses the energy gaps $E_j-E_0$, with the necessary phase
  correction proved in `centered_filter_identity`.
- The occurrence of $\lvert\gamma_0^2\rvert$ in the displayed Eq. (69) is used as
  $\lvert\gamma_0\rvert^2$, consistently with Eqs. (57), (68), and Theorem 1.

These are not strengthened assumptions; they are the dimensionally and
algebraically consistent readings of the proof.

## 13. Trust and verification

The project has been checked with:

```bash
lake build
lake env lean LeanExperiments/SKQD/Audit.lean
rg -n '\bsorry\b|\badmit\b|^axiom\b|sorryAx|native_decide' \
  LeanExperiments/SKQD LeanExperiments/SKQD.lean
```

The full build succeeds. The guarded `#print axioms` audit checks the key filter,
witness, sampling, final-convergence, and resource theorems. They depend only on
Mathlib's standard logical foundations used here:

```text
propext
Classical.choice
Quot.sound
```

There are no `sorry`, `admit`, custom `axiom`, `sorryAx`, or `native_decide`
occurrences in the SKQD source tree.

## 14. Source map

| Mathematical component | Lean source |
|---|---|
| Hilbert-space energy and Lemma 1 | [`Basic.lean`](LeanExperiments/SKQD/Basic.lean) |
| Krylov evolution identities | [`Krylov.lean`](LeanExperiments/SKQD/Krylov.lean) |
| Chebyshev filter | [`Filter.lean`](LeanExperiments/SKQD/Filter.lean) |
| Trigonometric/Fourier representation | [`Trigonometric.lean`](LeanExperiments/SKQD/Trigonometric.lean), [`Fourier.lean`](LeanExperiments/SKQD/Fourier.lean) |
| Spectral Rayleigh estimate | [`SpectralFilter.lean`](LeanExperiments/SKQD/SpectralFilter.lean) |
| Physical filter identity | [`FilterBridge.lean`](LeanExperiments/SKQD/FilterBridge.lean) |
| Odd-dimensional witness | [`Witness.lean`](LeanExperiments/SKQD/Witness.lean) |
| Endpoint $\Delta=W$ | [`Endpoint.lean`](LeanExperiments/SKQD/Endpoint.lean) |
| Even dimensions | [`Parity.lean`](LeanExperiments/SKQD/Parity.lean) |
| Sparsity and Lemmas 2, 3, 5 | [`Sparsity.lean`](LeanExperiments/SKQD/Sparsity.lean) |
| Random samples and exact minimizer | [`Sampling.lean`](LeanExperiments/SKQD/Sampling.lean) |
| Theorem 1 composition | [`Theorem1.lean`](LeanExperiments/SKQD/Theorem1.lean), [`ExactGuarantee.lean`](LeanExperiments/SKQD/ExactGuarantee.lean) |
| Paper-level spectral theorem | [`Paper.lean`](LeanExperiments/SKQD/Paper.lean) |
| Measurable success statement | [`Probability.lean`](LeanExperiments/SKQD/Probability.lean) |
| Automatic parameter choice | [`Resources.lean`](LeanExperiments/SKQD/Resources.lean), [`PolynomialResources.lean`](LeanExperiments/SKQD/PolynomialResources.lean) |
| Final constructive theorem | [`ConstructiveBudget.lean`](LeanExperiments/SKQD/ConstructiveBudget.lean) |
| Axiom and regression audit | [`Audit.lean`](LeanExperiments/SKQD/Audit.lean) |

## 15. Conclusion

The Lean development proves the complete ideal convergence chain claimed by SKQD
Theorem 1. Appendix A's approximation state is constructed from a concrete
Chebyshev filter and actual Hamiltonian time evolutions. Appendix B's state-error,
sparsity-transfer, hit-probability, independent-sampling, and truncation arguments
are all machine checked. Exact minimization on the random sampled support is
defined and connected to the high-probability energy conclusion.

Accordingly, the theorem is no longer conditional on an assumed low-energy Krylov
witness. Under the paper's spectral, sparsity, and ideal-sampling assumptions, Lean
proves the same convergence guarantee and also supplies explicit sufficient
resource choices and formal polynomial asymptotics.
