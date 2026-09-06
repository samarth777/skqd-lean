import LeanExperiments.SKQD.Parity

/-! The paper's probability guarantee from spectral and sampling assumptions.
All positive dimensions and `gap = W` are included; no Krylov witness, energy
approximation, coefficient bound, or phase alignment is assumed. -/
namespace SKQD

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

theorem paper_theorem1 {d M : ℕ}
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (hsym : (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (s : Finset ι) (gap W ε α β η : ℝ)
    (hψ₀ : ‖ψ₀‖ = 1) (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖) (hd : 0 < d)
    (hgap : 0 < gap) (hgapW : gap ≤ W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W)
    (hεdef : ε = paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (effectiveOddDimension d))
    (hεgap : ε ≤ gap)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hβL : 0 < β - 2 * Real.sqrt (epsTilde ε gap))
    (hs0 : Sparse (b j₀) s α β) (hL : 0 < s.card) (hη : 0 < η)
    (samples : Samples (Fin d) ι Ω M) (hMpos : 0 < M)
    (hM : ((d : ℝ) ^ 2 * Real.log ((s.card : ℝ) / η)) /
      (‖inner ℂ (b j₀) ψ₀‖ ^ 2 * (β - 2 * Real.sqrt (epsTilde ε gap))) ≤ (M : ℝ))
    (hmeas : ∀ k n, Measurable (samples k n))
    (hindep : ∀ k, ProbabilityTheory.iIndepFun (fun n => samples k n) μ)
    (hmarginal : ∀ k n j, μ.real {ω | samples k n ω = j} =
      hitProb (krylovFamily H ψ₀ (Real.pi / W) d k) j) :
    μ.real {ω | Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) <
      (inner ℂ (exactSKQDOutput H samples ⟨⟨0, hd⟩⟩ hMpos ω)
        (H (exactSKQDOutput H samples ⟨⟨0, hd⟩⟩ hMpos ω))).re - e j₀} ≤ η := by
  have hg := groundStateGap_of_eigenbasis H b e heigen hsym j₀ gap hgap
    (fun j hj => (he j hj).1)
  obtain ⟨w⟩ := exists_exactKrylovWitness H b e heigen hsym ψ₀ j₀ d gap W
    hψ₀ hγ hd hgap hgapW he
  have hε : 0 ≤ ε := by
    have hnorm : ‖inner ℂ (b j₀) ψ₀‖ ≤ 1 := by
      simpa [hg.normalized, hψ₀] using norm_inner_le_norm (b j₀) ψ₀
    have hmass : 0 ≤ 1 - ‖inner ℂ (b j₀) ψ₀‖ ^ 2 := by
      nlinarith [norm_nonneg (inner ℂ (b j₀) ψ₀)]
    have hW : 0 < W := hgap.trans_le hgapW
    rw [hεdef, paperKrylovError]
    positivity
  have w' : ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀) ε d := by
    rw [hεdef]
    exact w
  exact exact_krylov_probabilistic μ H (b j₀) ψ₀ s (e j₀) gap W ε α β η samples
    hg hψ₀ w' hε hεgap hα0 hα1 hβL hs0 hL hη hγ hd hMpos hM hmeas hindep hmarginal

end SKQD
