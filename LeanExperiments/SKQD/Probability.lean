import LeanExperiments.SKQD.Paper

/-! Measurability of the chosen output and success-probability conversion. -/
namespace SKQD
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped InnerProductSpace

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_exactSKQDOutput {M : ℕ}
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (samples : Samples κ ι Ω M) (hκ : Nonempty κ) (hM : 0 < M)
    (hmeas : ∀ k n, Measurable (samples k n)) :
    Measurable (exactSKQDOutput H samples hκ hM) := by
  let f : (κ → Fin M → ι) → EuclideanSpace ℂ ι := fun v =>
    exactSKQDOutput H (fun k n (_ : Unit) => v k n) hκ hM ()
  have htuple : Measurable (fun ω k n => samples k n ω) :=
    measurable_pi_lambda _ (fun k => measurable_pi_lambda _ (hmeas k))
  have hf := (measurable_of_finite f).comp htuple
  exact hf

theorem success_probability_of_bad_probability {M : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (samples : Samples κ ι Ω M) (hκ : Nonempty κ) (hM : 0 < M)
    (hmeas : ∀ k n, Measurable (samples k n)) (E₀ bound η : ℝ)
    (hbad : μ.real {ω | bound < (inner ℂ (exactSKQDOutput H samples hκ hM ω)
      (H (exactSKQDOutput H samples hκ hM ω))).re - E₀} ≤ η) :
    1 - η ≤ μ.real {ω | (inner ℂ (exactSKQDOutput H samples hκ hM ω)
      (H (exactSKQDOutput H samples hκ hM ω))).re - E₀ ≤ bound} := by
  have hout := measurable_exactSKQDOutput H samples hκ hM hmeas
  have henergy : Continuous (fun ψ : EuclideanSpace ℂ ι => (inner ℂ ψ (H ψ)).re - E₀) := by
    fun_prop
  have hs : MeasurableSet {ω | bound < (inner ℂ (exactSKQDOutput H samples hκ hM ω)
      (H (exactSKQDOutput H samples hκ hM ω))).re - E₀} :=
    measurableSet_lt measurable_const (henergy.measurable.comp hout)
  have hh := measureReal_compl (μ := μ) hs
  simp only [Set.compl_ofPred, not_lt, probReal_univ] at hh
  linarith

theorem sampledSupport_card_le {M : ℕ} (samples : Samples κ ι Ω M) (ω : Ω) :
    (sampledSupport samples ω).card ≤ Fintype.card κ * M := by
  unfold sampledSupport
  calc
    _ ≤ ∑ k : κ, (Finset.univ.image (fun n : Fin M => samples k n ω)).card := Finset.card_biUnion_le
    _ ≤ ∑ _k : κ, M := by
      apply Finset.sum_le_sum
      intro k _
      simpa using (Finset.card_image_le (s := Finset.univ) (f := fun n : Fin M => samples k n ω))
    _ = _ := by simp

end SKQD
