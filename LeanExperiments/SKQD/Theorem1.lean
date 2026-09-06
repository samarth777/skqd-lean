import Mathlib
import LeanExperiments.SKQD.Sparsity

/-!
Deterministic and analytic composition used by Theorem 1 from
arXiv:2501.09702v1, Appendix B.1.

Krylov dimension versus `ε` (the paper's Theorem 2 / Epperly) is taken as a
hypothesis: there exists a normalized Krylov combination with energy error
`≤ ε` and coefficient bound `|d_k| ≤ 1/|γ₀|`. The actual random experiment
and returned SKQD state are formalized in `SKQD.Sampling`.
-/

namespace SKQD

open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

/-- Paper Equation (9)/(65)–(66): state-error quantity produced by Lemma 1. -/
noncomputable def epsTilde (ε ΔE₁ : ℝ) : ℝ :=
  2 * (1 - Real.sqrt (1 - ε / ΔE₁))

lemma epsTilde_nonneg {ε ΔE₁ : ℝ}
    (hε : 0 ≤ ε) (hεgap : ε ≤ ΔE₁) (hΔ : 0 < ΔE₁) :
    0 ≤ epsTilde ε ΔE₁ := by
  have hrad : 0 ≤ 1 - ε / ΔE₁ := sub_nonneg.2 (div_le_one_of_le₀ hεgap hΔ.le)
  have hsqrt : Real.sqrt (1 - ε / ΔE₁) ≤ 1 := by
    simpa [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 - ε / ΔE₁ ≤ 1 by linarith [div_nonneg hε hΔ.le])
  unfold epsTilde
  linarith

lemma epsTilde_eq_lemma1 (ε ΔE₁ : ℝ) :
    epsTilde ε ΔE₁ = 2 * (1 - Real.sqrt (1 - ε / ΔE₁)) :=
  rfl

/-- Hit probability used after Lemma 3 (Equation (68)). -/
noncomputable def hitLowerBound (d : ℕ) (γ : ℂ) (β et : ℝ) : ℝ :=
  ‖γ‖ ^ 2 * (β - 2 * Real.sqrt et) / (d : ℝ) ^ 2

theorem lemma3_on_support
    (coeff : κ → ℂ) (krylov : κ → EuclideanSpace ℂ ι)
    (γ : ℂ) (s : Finset ι) (α β : ℝ)
    (hd : 0 < Fintype.card κ)
    (hcoeff : ∀ k, ‖coeff k‖ * ‖γ‖ ≤ 1)
    (hβnn : 0 ≤ β)
    (hs : Sparse (∑ k, coeff k • krylov k) s α β) :
    ∀ j ∈ s, ∃ k, ‖γ‖ ^ 2 * β / (Fintype.card κ : ℝ) ^ 2 ≤
      hitProb (krylov k) j := by
  intro j hj
  exact lemma3_krylov_hit coeff krylov γ β j hd hcoeff hβnn (hs.pointwise j hj)

/-- Energy conclusion of Theorem 1: the truncated ground state (Lemma 5)
has the paper's energy error bound. Combined with the variational principle,
any SKQD minimizer in a subspace containing this truncation is at least as
accurate. -/
theorem theorem1_energy
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ : EuclideanSpace ℂ ι) (s : Finset ι)
    (E₀ ΔE₁ α β : ℝ)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hs : Sparse φ₀ s α β) :
    (inner ℂ (truncated φ₀ s) (H (truncated φ₀ s))).re - E₀ ≤
      Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) := by
  have hbound := lemma5_truncated_energy H φ₀ s α β hg.normalized hα0 hα1 hs
  have hE : (inner ℂ φ₀ (H φ₀)).re = E₀ := ground_rayleigh H φ₀ E₀ ΔE₁ hg
  have habs := hbound
  rw [hE] at habs
  linarith [le_abs_self
    ((inner ℂ (truncated φ₀ s) (H (truncated φ₀ s))).re - E₀)]

/-- If SKQD returns a unit vector whose energy is at most that of the
truncated ground state (true once every important bitstring has been
sampled), the energy error is at most the Lemma 5 bound. -/
theorem theorem1_skqd_energy_on_success
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ ψ_skqd : EuclideanSpace ℂ ι) (s : Finset ι)
    (E₀ ΔE₁ α β : ℝ)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hskqd : ‖ψ_skqd‖ = 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hs : Sparse φ₀ s α β)
    (hmin :
      (inner ℂ ψ_skqd (H ψ_skqd)).re ≤
        (inner ℂ (truncated φ₀ s) (H (truncated φ₀ s))).re) :
    E₀ ≤ (inner ℂ ψ_skqd (H ψ_skqd)).re ∧
      (inner ℂ ψ_skqd (H ψ_skqd)).re - E₀ ≤
        Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) := by
  have hvar := energy_ge_ground H φ₀ ψ_skqd E₀ ΔE₁ hg hskqd
  have htrunc := theorem1_energy H φ₀ s E₀ ΔE₁ α β hg hα0 hα1 hs
  exact ⟨hvar, by linarith⟩

/-- **Theorem 1** (arXiv:2501.09702v1).

From a KQD combination with energy error `≤ ε` and coefficient bound
`|d_k| ≤ 1/|γ₀|`, together with `(α,β)`-sparsity of the ground state:

* the truncated ground state (and therefore SKQD, once the important
  bitstrings are sampled) has energy error at most
  `√8 ‖H‖ √(1-√α)`;
* the analytic union-bound expression is at most `η`, with the paper's
  sample threshold.

This theorem contains no random experiment.  See `theorem1_probabilistic`
in `SKQD.Sampling` for the result about actual samples and the state returned
by diagonalization on their random support.
-/
theorem theorem1
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ : EuclideanSpace ℂ ι)
    (coeff : κ → ℂ) (krylov : κ → EuclideanSpace ℂ ι)
    (γ : ℂ) (s : Finset ι)
    (E₀ ΔE₁ ε α β η : ℝ) (M : ℕ)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hψn : ‖∑ k, coeff k • krylov k‖ = 1)
    (hkry : ∀ k, ‖krylov k‖ = 1)
    (hcoeff : ∀ k, ‖coeff k‖ * ‖γ‖ ≤ 1)
    (hphase : (inner ℂ φ₀ (∑ k, coeff k • krylov k)).im = 0)
    (hpos : 0 ≤ (inner ℂ φ₀ (∑ k, coeff k • krylov k)).re)
    (hε : 0 ≤ ε) (hεgap : ε ≤ ΔE₁)
    (herr : (inner ℂ (∑ k, coeff k • krylov k) (H (∑ k, coeff k • krylov k))).re - E₀ ≤ ε)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hβL : 0 < β - 2 * Real.sqrt (epsTilde ε ΔE₁))
    (hs0 : Sparse φ₀ s α β)
    (hL : 0 < s.card) (hη : 0 < η)
    (hγ : 0 < ‖γ‖)
    (hd : 0 < Fintype.card κ)
    (hM :
      ((Fintype.card κ : ℝ) ^ 2 * Real.log ((s.card : ℝ) / η)) /
        (‖γ‖ ^ 2 * (β - 2 * Real.sqrt (epsTilde ε ΔE₁))) ≤ (M : ℝ)) :
    ((inner ℂ (truncated φ₀ s) (H (truncated φ₀ s))).re - E₀ ≤
        Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α)) ∧
      (s.card : ℝ) *
          (1 - hitLowerBound (Fintype.card κ) γ β (epsTilde ε ΔE₁)) ^ M ≤ η := by
  set ψ := ∑ k, coeff k • krylov k
  set et := epsTilde ε ΔE₁
  set βL := β - 2 * Real.sqrt et
  set p := hitLowerBound (Fintype.card κ) γ β et
  have het : 0 ≤ et := epsTilde_nonneg hε hεgap hg.gap_pos
  have hdist : ‖ψ - φ₀‖ ^ 2 ≤ et := by
    simpa [ψ, et, epsTilde] using
      lemma1_state_error H φ₀ ψ E₀ ΔE₁ ε hg hψn hphase hpos hε hεgap herr
  have hsψ : Sparse ψ s (α - 2 * Real.sqrt et) βL :=
    lemma2_sparsity_transfer (ψ := ψ) (φ := φ₀) (s := s)
      (α := α) (β := β) (ε := et) hg.normalized het hs0 hdist
  have hβLnn : 0 ≤ βL := hβL.le
  have hhit : ∀ j ∈ s, ∃ k, p ≤ hitProb (krylov k) j := by
    intro j hj
    simpa [p, hitLowerBound, βL] using
      lemma3_krylov_hit coeff krylov γ βL j hd hcoeff hβLnn (hsψ.pointwise j hj)
  have hp_le_one : p ≤ 1 := by
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hL
    obtain ⟨k, hk⟩ := hhit j hj
    exact hk.trans (hitProb_le_one (hkry k) j)
  have hγsq : 0 < ‖γ‖ ^ 2 := by nlinarith [sq_nonneg ‖γ‖, hγ]
  have henergy := theorem1_energy H φ₀ s E₀ ΔE₁ α β hg hα0 hα1 hs0
  have hfail :
      (s.card : ℝ) * (1 - p) ^ M ≤ η := by
    refine paper_sampling_failure_le_eta
        s.card M (Fintype.card κ)
        (‖γ‖ ^ 2) βL η ((s.card : ℝ) * (1 - p) ^ M)
        hL hd hη hγsq hβL ?_ le_rfl hM
    simpa [p, hitLowerBound, βL] using hp_le_one
  exact ⟨henergy, by simpa [p] using hfail⟩

end SKQD
