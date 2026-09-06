import LeanExperiments.SKQD.Sampling

/-!
The probabilistic theorem specialized to the exact physical Krylov family.
`ExactKrylovWitness` is the interface between Appendix A and Appendix B.
Its existence is now proved in `Parity.lean`, and `Paper.lean` discharges
this interface from spectral assumptions in the final theorem.
-/
namespace SKQD

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

/-- Simultaneous energy and coefficient properties proved in Appendix A.
No phase condition is required: it is proved by `align_combination`. -/
structure ExactKrylovWitness
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ ψ₀ : EuclideanSpace ℂ ι) (Δt E₀ ε : ℝ) (d : ℕ) where
  coeff : Fin d → ℂ
  normalized : ‖∑ k, coeff k • krylovFamily H ψ₀ Δt d k‖ = 1
  coefficient_bound : ∀ k, ‖coeff k‖ * ‖inner ℂ φ₀ ψ₀‖ ≤ 1
  energy_bound :
    (inner ℂ (∑ k, coeff k • krylovFamily H ψ₀ Δt d k)
      (H (∑ k, coeff k • krylovFamily H ψ₀ Δt d k))).re - E₀ ≤ ε

/-- Exact time evolution, actual initial-state overlap, Born sampling, and
the sampled-subspace variational output, conditional only on the stated
Krylov witness and the physical/sampling hypotheses. -/
theorem exact_krylov_probabilistic {d M : ℕ}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ₀ ψ₀ : EuclideanSpace ℂ ι) (s : Finset ι)
    (E₀ ΔE₁ W ε α β η : ℝ)
    (samples : Samples (Fin d) ι Ω M)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁) (hψ₀ : ‖ψ₀‖ = 1)
    (w : ExactKrylovWitness H φ₀ ψ₀ (Real.pi / W) E₀ ε d)
    (hε : 0 ≤ ε) (hεgap : ε ≤ ΔE₁)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hβL : 0 < β - 2 * Real.sqrt (epsTilde ε ΔE₁))
    (hs0 : Sparse φ₀ s α β) (hL : 0 < s.card) (hη : 0 < η)
    (hγ : 0 < ‖inner ℂ φ₀ ψ₀‖) (hd : 0 < d) (hMpos : 0 < M)
    (hM : ((d : ℝ) ^ 2 * Real.log ((s.card : ℝ) / η)) /
      (‖inner ℂ φ₀ ψ₀‖ ^ 2 * (β - 2 * Real.sqrt (epsTilde ε ΔE₁))) ≤ (M : ℝ))
    (hmeas : ∀ k m, Measurable (samples k m))
    (hindep : ∀ k, ProbabilityTheory.iIndepFun (fun m => samples k m) μ)
    (hmarginal : ∀ k m j, μ.real {ω | samples k m ω = j} =
      hitProb (krylovFamily H ψ₀ (Real.pi / W) d k) j) :
    μ.real {ω | Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) <
      (inner ℂ (exactSKQDOutput H samples ⟨⟨0, hd⟩⟩ hMpos ω)
        (H (exactSKQDOutput H samples ⟨⟨0, hd⟩⟩ hMpos ω))).re - E₀} ≤ η := by
  have hcard : 0 < Fintype.card (Fin d) := by simpa using hd
  apply theorem1_probabilistic μ H φ₀ w.coeff
    (krylovFamily H ψ₀ (Real.pi / W) d) ⟨0, hd⟩ s E₀ ΔE₁ ε α β η
    samples hg w.normalized
    (krylovFamily_normalized H ψ₀ _ d hg.symmetric hψ₀)
  · simpa using w.coefficient_bound
  · exact hε
  · exact hεgap
  · exact w.energy_bound
  · exact hα0
  · exact hα1
  · exact hβL
  · exact hs0
  · exact hL
  · exact hη
  · simpa using hγ
  · exact hcard
  · simpa using hM
  · exact hmeas
  · exact hindep
  · exact hmarginal

end SKQD
