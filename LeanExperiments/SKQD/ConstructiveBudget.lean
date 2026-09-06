import LeanExperiments.SKQD.PolynomialResources

/-! The probability guarantee with dimension and shots chosen explicitly.
No approximation witness, energy tolerance condition, retained-sparsity
condition, or sample-count inequality is supplied by the caller. -/
namespace SKQD
open MeasureTheory
open scoped InnerProductSpace

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

lemma resourceShots_pos (W gap g β L η : ℝ) : 0 < resourceShots W gap g β L η :=
  sufficientShots_pos _

theorem paper_theorem1_constructive
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (hsym : (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (s : Finset ι) (gap W g α β η : ℝ)
    (hψ₀ : ‖ψ₀‖ = 1) (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖)
    (hgdef : g = ‖inner ℂ (b j₀) ψ₀‖ ^ 2)
    (hgap : 0 < gap) (hgapW : gap ≤ W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hs0 : Sparse (b j₀) s α β) (hL : 0 < s.card) (hη : 0 < η)
    (samples : Samples (Fin (resourceDimension W gap g β)) ι Ω (resourceShots W gap g β s.card η))
    (hmeas : ∀ k n, Measurable (samples k n))
    (hindep : ∀ k, ProbabilityTheory.iIndepFun (fun n => samples k n) μ)
    (hmarginal : ∀ k n j, μ.real {ω | samples k n ω = j} =
      hitProb (krylovFamily H ψ₀ (Real.pi / W) (resourceDimension W gap g β) k) j) :
    1 - η ≤ μ.real {ω |
      (inner ℂ (exactSKQDOutput H samples ⟨⟨0, resourceDimension_pos W gap g β⟩⟩
        (resourceShots_pos W gap g β s.card η) ω)
        (H (exactSKQDOutput H samples ⟨⟨0, resourceDimension_pos W gap g β⟩⟩
          (resourceShots_pos W gap g β s.card η) ω))).re - e j₀ ≤
            Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α)} := by
  have hW : 0 < W := hgap.trans_le hgapW
  have hg : 0 < g := by rw [hgdef]; positivity
  have hg1 : g ≤ 1 := by
    have hn : ‖inner ℂ (b j₀) ψ₀‖ ≤ 1 := by
      simpa [b.orthonormal.norm_eq_one j₀, hψ₀] using norm_inner_le_norm (b j₀) ψ₀
    rw [hgdef]
    nlinarith
  have hβ1 : β ≤ 1 := by
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hL
    exact (hs0.pointwise j hj).trans (hitProb_le_one (b.orthonormal.norm_eq_one j₀) j)
  let ε := paperKrylovError W gap g (resourceDimension W gap g β)
  obtain ⟨hε0, hεgap, hret⟩ := resourceParameterDomains hW hgap hg hg1 hβ hβ1
  have hretpos : 0 < β - 2 * Real.sqrt (epsTilde ε gap) :=
    lt_of_lt_of_le (by positivity) hret
  apply success_probability_of_bad_probability μ H samples _ _ hmeas
  apply paper_theorem1 μ H b e heigen hsym ψ₀ j₀ s gap W ε α β η hψ₀ hγ
    (resourceDimension_pos W gap g β) hgap hgapW he
  · rw [resourceDimension_odd, ← hgdef]
  · exact hεgap
  · exact hα0
  · exact hα1
  · exact hretpos
  · exact hs0
  · exact hL
  · exact hη
  · rw [← hgdef]
    exact sufficientShots_meets_threshold _
  · exact hmeas
  · exact hindep
  · exact hmarginal

end SKQD
