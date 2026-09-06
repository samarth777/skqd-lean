import LeanExperiments.SKQD.Theorem1
import LeanExperiments.SKQD.Phase
import LeanExperiments.SKQD.Krylov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

/-!
The probabilistic and algorithmic layer of SKQD Theorem 1.

`iidBornMiss` is the operational contract for `M` independent Born-rule
measurements of each Krylov state: the probability of missing outcome `j`
in all `M` shots is `(1 - hitProb)^M`.  Starting from that contract, this
file models the actual failure event, the random sampled support, and the
state returned by diagonalizing the Hamiltonian on that support.
-/

namespace SKQD

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

set_option linter.unusedSectionVars false

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]
variable [MeasurableSpace Ω]

/-- Outcomes of `M` measurements of every Krylov state. -/
abbrev Samples (κ ι Ω : Type*) (M : ℕ) := κ → Fin M → Ω → ι

/-- The computational-basis strings observed in one run. -/
def sampledSupport {M : ℕ} (samples : Samples κ ι Ω M) (ω : Ω) : Finset ι :=
  Finset.univ.biUnion fun k => Finset.univ.image fun m => samples k m ω

/-- A string is missed when it occurs in none of the shots from any state. -/
def missedBit {M : ℕ} (samples : Samples κ ι Ω M) (j : ι) : Set Ω :=
  {ω | ∀ k m, samples k m ω ≠ j}

/-- Failure means that at least one important string was never observed. -/
def samplingFailure {M : ℕ} (samples : Samples κ ι Ω M) (s : Finset ι) : Set Ω :=
  ⋃ j ∈ s, missedBit samples j

/-- The exact consequence of `M` independent Born-rule shots needed by the
SKQD proof.  This separates the physical sampling assumption from the
deterministic Hilbert-space argument. -/
def iidBornMiss {M : ℕ} (μ : Measure Ω) (samples : Samples κ ι Ω M)
    (krylov : κ → EuclideanSpace ℂ ι) : Prop :=
  ∀ k j, μ.real {ω | ∀ m, samples k m ω ≠ j} = (1 - hitProb (krylov k) j) ^ M

/-- Measurable, independent shots with the Born-rule marginal distribution
imply the `iidBornMiss` contract; it is not an additional probabilistic axiom. -/
theorem iidBornMiss_of_independent {M : ℕ}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (samples : Samples κ ι Ω M) (krylov : κ → EuclideanSpace ℂ ι)
    (hmeas : ∀ k m, Measurable (samples k m))
    (hindep : ∀ k, ProbabilityTheory.iIndepFun (fun m => samples k m) μ)
    (hmarginal : ∀ k m j,
      μ.real {ω | samples k m ω = j} = hitProb (krylov k) j) :
    iidBornMiss μ samples krylov := by
  intro k j
  let A : Fin M → Set Ω := fun m => {ω | samples k m ω ≠ j}
  have hA : ∀ m, MeasurableSet (A m) := by
    intro m
    exact ((measurableSet_singleton j).preimage (hmeas k m)).compl
  have hA_comap : ∀ m,
      MeasurableSet[(inferInstance : MeasurableSpace ι).comap (samples k m)] (A m) := by
    intro m
    exact (measurableSet_singleton j).compl.preimage (comap_measurable _)
  have hinter := (hindep k).meas_iInter (s := A) hA_comap
  have hset : {ω | ∀ m, samples k m ω ≠ j} = ⋂ m, A m := by
    ext ω
    simp [A]
  have hmiss : ∀ m, μ.real (A m) = 1 - hitProb (krylov k) j := by
    intro m
    have hcompl : A m = {ω | samples k m ω = j}ᶜ := by
      ext ω
      simp [A]
    rw [hcompl, measureReal_compl]
    · rw [hmarginal]
      simp
    · exact (measurableSet_singleton j).preimage (hmeas k m)
  rw [hset, Measure.real, hinter, ENNReal.toReal_prod]
  change (∏ m, μ.real (A m)) = _
  simp_rw [hmiss]
  simp

lemma mem_sampledSupport_iff {M : ℕ} (samples : Samples κ ι Ω M) (ω : Ω) (j : ι) :
    j ∈ sampledSupport samples ω ↔ ∃ k m, samples k m ω = j := by
  simp [sampledSupport]

lemma not_mem_failure_iff {M : ℕ} (samples : Samples κ ι Ω M)
    (s : Finset ι) (ω : Ω) :
    ω ∉ samplingFailure samples s ↔ s ⊆ sampledSupport samples ω := by
  simp only [samplingFailure, Set.mem_iUnion, not_exists, missedBit,
    Set.mem_ofPred_eq, Finset.subset_iff]
  constructor
  · intro h j hj
    rw [mem_sampledSupport_iff]
    push Not at h
    exact h j hj
  · intro h j hj
    obtain ⟨k, m, hkm⟩ := (mem_sampledSupport_iff samples ω j).mp (h hj)
    intro hall
    exact hall k m hkm

lemma missedBit_subset_one_state {M : ℕ} (samples : Samples κ ι Ω M)
    (j : ι) (k : κ) :
    missedBit samples j ⊆ {ω | ∀ m, samples k m ω ≠ j} := by
  intro ω hω m
  exact hω k m

/-- The genuine union bound for the event that some important bitstring is
absent from the random sampled support. -/
theorem samplingFailure_measure_le {M : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (samples : Samples κ ι Ω M) (krylov : κ → EuclideanSpace ℂ ι)
    (s : Finset ι) (p : ℝ)
    (hborn : iidBornMiss μ samples krylov)
    (hkry : ∀ k, ‖krylov k‖ = 1)
    (hhit : ∀ j ∈ s, ∃ k, p ≤ hitProb (krylov k) j) :
    μ.real (samplingFailure samples s) ≤ (s.card : ℝ) * (1 - p) ^ M := by
  calc
    μ.real (samplingFailure samples s)
        ≤ ∑ j ∈ s, μ.real (missedBit samples j) := by
          simpa [samplingFailure] using measureReal_biUnion_finset_le (μ := μ) s
            (fun j => missedBit samples j)
    _ ≤ ∑ _j ∈ s, (1 - p) ^ M := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨k, hk⟩ := hhit j hj
      calc
        μ.real (missedBit samples j)
            ≤ μ.real {ω | ∀ m, samples k m ω ≠ j} :=
              measureReal_mono (missedBit_subset_one_state samples j k) (by finiteness)
        _ = (1 - hitProb (krylov k) j) ^ M := hborn k j
        _ ≤ (1 - p) ^ M := by
          exact pow_le_pow_left₀
            (sub_nonneg.mpr (hitProb_le_one (hkry k) j))
            (sub_le_sub_left hk 1) M
    _ = (s.card : ℝ) * (1 - p) ^ M := by simp

/-- A vector has computational-basis support contained in `s`. -/
def SupportedOn (ψ : EuclideanSpace ℂ ι) (s : Finset ι) : Prop :=
  ∀ j, j ∉ s → ψ j = 0

/-- The coordinate subspace spanned by the strings in `s`. -/
def supportedSubmodule (s : Finset ι) : Submodule ℂ (EuclideanSpace ℂ ι) where
  carrier := {ψ | SupportedOn ψ s}
  zero_mem' := by simp [SupportedOn]
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  smul_mem' := by
    intro c x hx j hj
    simp [hx j hj]

lemma single_supportedOn {s : Finset ι} {j : ι} (hj : j ∈ s) :
    SupportedOn (EuclideanSpace.single j (1 : ℂ)) s := by
  intro i hi
  rw [PiLp.single_apply]
  simp only [ite_eq_right_iff]
  intro hij
  exact (hi (hij ▸ hj)).elim

lemma truncated_supportedOn {ψ : EuclideanSpace ℂ ι} {s t : Finset ι}
    (hst : s ⊆ t) : SupportedOn (truncated ψ s) t := by
  intro j hj
  have hjs : j ∉ s := fun h => hj (hst h)
  simp [truncated, restrict_apply, hjs]

/-- The specification of exact diagonalization on a sampled subspace. -/
structure MinimizerOn
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (s : Finset ι) (ψ : EuclideanSpace ℂ ι) : Prop where
  normalized : ‖ψ‖ = 1
  supported : SupportedOn ψ s
  minimizes : ∀ φ, ‖φ‖ = 1 → SupportedOn φ s →
    (inner ℂ ψ (H ψ)).re ≤ (inner ℂ φ (H φ)).re

/-- Exact diagonalization on every nonempty finite coordinate subspace has a
normalized minimizing state. -/
theorem exists_minimizerOn
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (s : Finset ι) (hs : s.Nonempty) :
    ∃ ψ, MinimizerOn H s ψ := by
  let U := supportedSubmodule (ι := ι) s
  let K : Set (EuclideanSpace ℂ ι) := Metric.sphere 0 1 ∩ (U : Set _)
  have hKcompact : IsCompact K := by
    exact (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).inter_right
      U.closed_of_finiteDimensional
  obtain ⟨j, hj⟩ := hs
  let e : EuclideanSpace ℂ ι := EuclideanSpace.single j 1
  have he_norm : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have he_support : SupportedOn e s := single_supportedOn hj
  have hKnonempty : K.Nonempty := by
    refine ⟨e, ?_⟩
    exact ⟨by simp [he_norm], he_support⟩
  let energy : EuclideanSpace ℂ ι → ℝ := fun x => (inner ℂ x (H x)).re
  have henergy : Continuous energy := by
    dsimp [energy]
    fun_prop
  obtain ⟨ψ, hψK, hψmin⟩ :=
    hKcompact.exists_isMinOn hKnonempty henergy.continuousOn
  refine ⟨ψ, ?_⟩
  refine
    { normalized := by simpa [K, Metric.mem_sphere] using hψK.1
      supported := hψK.2
      minimizes := ?_ }
  intro φ hφ hφs
  exact hψmin ⟨by simp [hφ], hφs⟩

lemma sampledSupport_nonempty {M : ℕ} (samples : Samples κ ι Ω M)
    (hκ : Nonempty κ) (hM : 0 < M) (ω : Ω) :
    (sampledSupport samples ω).Nonempty := by
  let k : κ := hκ.some
  let m : Fin M := ⟨0, hM⟩
  exact ⟨samples k m ω, (mem_sampledSupport_iff samples ω _).mpr ⟨k, m, rfl⟩⟩

/-- A canonical mathematical specification of the exact classical
diagonalization step. -/
noncomputable def exactSKQDOutput {M : ℕ}
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (samples : Samples κ ι Ω M) (hκ : Nonempty κ) (hM : 0 < M) (ω : Ω) :
    EuclideanSpace ℂ ι :=
  Classical.choose (exists_minimizerOn H (sampledSupport samples ω)
    (sampledSupport_nonempty samples hκ hM ω))

theorem exactSKQDOutput_spec {M : ℕ}
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (samples : Samples κ ι Ω M) (hκ : Nonempty κ) (hM : 0 < M) (ω : Ω) :
    MinimizerOn H (sampledSupport samples ω)
      (exactSKQDOutput H samples hκ hM ω) :=
  Classical.choose_spec (exists_minimizerOn H (sampledSupport samples ω)
    (sampledSupport_nonempty samples hκ hM ω))

/-- An actual SKQD output has a bad energy only on a sampling-failure run. -/
theorem badEnergy_subset_samplingFailure {M : ℕ}
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ : EuclideanSpace ℂ ι) (s : Finset ι)
    (E₀ ΔE₁ α β : ℝ)
    (samples : Samples κ ι Ω M)
    (output : Ω → EuclideanSpace ℂ ι)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hs : Sparse φ₀ s α β)
    (hout : ∀ ω, MinimizerOn H (sampledSupport samples ω) (output ω)) :
    {ω | Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) <
      (inner ℂ (output ω) (H (output ω))).re - E₀} ⊆
      samplingFailure samples s := by
  intro ω hbad
  by_contra hfail
  have hsubset := (not_mem_failure_iff samples s ω).mp hfail
  have htrunc_norm : ‖truncated φ₀ s‖ = 1 :=
    truncated_normalized (sparse_mass_pos hα0 hs)
  have hmin := (hout ω).minimizes (truncated φ₀ s) htrunc_norm
    (truncated_supportedOn hsubset)
  have henergy := theorem1_energy H φ₀ s E₀ ΔE₁ α β hg hα0 hα1 hs
  change Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) <
    (inner ℂ (output ω) (H (output ω))).re - E₀ at hbad
  linarith

/-- **SKQD Theorem 1, probabilistic form.**

Under the KQD approximation hypotheses and the IID Born-sampling contract,
the probability that exact diagonalization on the sampled support returns an
energy outside the paper's bound is at most `η`.

Unlike `theorem1`, this statement mentions the actual random samples, their
sampled subspace, and the state returned on every run.  The overlap parameter
is definitionally tied to the designated reference Krylov state `k₀`.
-/
theorem theorem1_probabilistic {M : ℕ}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ : EuclideanSpace ℂ ι)
    (coeff : κ → ℂ) (krylov : κ → EuclideanSpace ℂ ι) (k₀ : κ)
    (s : Finset ι) (E₀ ΔE₁ ε α β η : ℝ)
    (samples : Samples κ ι Ω M)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hψn : ‖∑ k, coeff k • krylov k‖ = 1)
    (hkry : ∀ k, ‖krylov k‖ = 1)
    (hcoeff : ∀ k,
      ‖coeff k‖ * ‖inner ℂ φ₀ (krylov k₀)‖ ≤ 1)
    (hε : 0 ≤ ε) (hεgap : ε ≤ ΔE₁)
    (herr :
      (inner ℂ (∑ k, coeff k • krylov k)
        (H (∑ k, coeff k • krylov k))).re - E₀ ≤ ε)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hβL : 0 < β - 2 * Real.sqrt (epsTilde ε ΔE₁))
    (hs0 : Sparse φ₀ s α β)
    (hL : 0 < s.card) (hη : 0 < η)
    (hγ : 0 < ‖inner ℂ φ₀ (krylov k₀)‖)
    (hd : 0 < Fintype.card κ)
    (hMpos : 0 < M)
    (hM :
      ((Fintype.card κ : ℝ) ^ 2 * Real.log ((s.card : ℝ) / η)) /
        (‖inner ℂ φ₀ (krylov k₀)‖ ^ 2 *
          (β - 2 * Real.sqrt (epsTilde ε ΔE₁))) ≤ (M : ℝ))
    (hmeas : ∀ k m, Measurable (samples k m))
    (hindep : ∀ k, ProbabilityTheory.iIndepFun (fun m => samples k m) μ)
    (hmarginal : ∀ k m j,
      μ.real {ω | samples k m ω = j} = hitProb (krylov k) j) :
    μ.real {ω | Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) <
      (inner ℂ (exactSKQDOutput H samples
        (Fintype.card_pos_iff.mp hd) hMpos ω)
        (H (exactSKQDOutput H samples
          (Fintype.card_pos_iff.mp hd) hMpos ω))).re - E₀} ≤ η := by
  obtain ⟨coeff', hnorm, hsum_norm, henergy, hphase, hpos⟩ :=
    align_combination H φ₀ krylov coeff
  have hψn' : ‖∑ k, coeff' k • krylov k‖ = 1 := hsum_norm.trans hψn
  have herr' : (inner ℂ (∑ k, coeff' k • krylov k)
      (H (∑ k, coeff' k • krylov k))).re - E₀ ≤ ε := by
    rw [henergy]
    exact herr
  have hcoeff' : ∀ k, ‖coeff' k‖ * ‖inner ℂ φ₀ (krylov k₀)‖ ≤ 1 := by
    intro k
    rw [hnorm]
    exact hcoeff k
  let γ₀ : ℂ := inner ℂ φ₀ (krylov k₀)
  let ψ := ∑ k, coeff' k • krylov k
  let et := epsTilde ε ΔE₁
  let βL := β - 2 * Real.sqrt et
  let p := hitLowerBound (Fintype.card κ) γ₀ β et
  have het : 0 ≤ et := epsTilde_nonneg hε hεgap hg.gap_pos
  have hdist : ‖ψ - φ₀‖ ^ 2 ≤ et := by
    simpa [ψ, et, epsTilde] using
      lemma1_state_error H φ₀ ψ E₀ ΔE₁ ε hg hψn' hphase hpos hε hεgap herr'
  have hsψ : Sparse ψ s (α - 2 * Real.sqrt et) βL :=
    lemma2_sparsity_transfer (ψ := ψ) (φ := φ₀) (s := s)
      (α := α) (β := β) (ε := et) hg.normalized het hs0 hdist
  have hβLpos : 0 < βL := by simpa [βL, et] using hβL
  have hhit : ∀ j ∈ s, ∃ k, p ≤ hitProb (krylov k) j := by
    intro j hj
    simpa [p, hitLowerBound, γ₀, βL] using
      lemma3_krylov_hit coeff' krylov γ₀ βL j hd
        (by simpa [γ₀] using hcoeff') hβLpos.le (hsψ.pointwise j hj)
  have hp_le_one : p ≤ 1 := by
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hL
    obtain ⟨k, hk⟩ := hhit j hj
    exact hk.trans (hitProb_le_one (hkry k) j)
  have hγsq : 0 < ‖γ₀‖ ^ 2 := by
    have : 0 < ‖γ₀‖ := by simpa [γ₀] using hγ
    positivity
  have hunion :
      μ.real (samplingFailure samples s) ≤ (s.card : ℝ) * (1 - p) ^ M :=
    samplingFailure_measure_le μ samples krylov s p
      (iidBornMiss_of_independent μ samples krylov hmeas hindep hmarginal) hkry hhit
  have hfailure : μ.real (samplingFailure samples s) ≤ η := by
    refine paper_sampling_failure_le_eta
      s.card M (Fintype.card κ) (‖γ₀‖ ^ 2) βL η
      (μ.real (samplingFailure samples s)) hL hd hη hγsq hβLpos ?_ ?_ ?_
    · simpa [p, hitLowerBound, βL] using hp_le_one
    · simpa [p, hitLowerBound, βL] using hunion
    · simpa [γ₀, βL, et] using hM
  exact (measureReal_mono
    (badEnergy_subset_samplingFailure H φ₀ s E₀ ΔE₁ α β samples
      (exactSKQDOutput H samples (Fintype.card_pos_iff.mp hd) hMpos)
      hg hα0 hα1 hs0
      (exactSKQDOutput_spec H samples (Fintype.card_pos_iff.mp hd) hMpos))
    (by finiteness)).trans hfailure

end SKQD
