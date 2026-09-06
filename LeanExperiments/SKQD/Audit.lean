import LeanExperiments.SKQD

/-! Trust-boundary and edge-case regression checks. Run with
`lake env lean LeanExperiments/SKQD/Audit.lean`. -/

/-- info: 'SKQD.align_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.align_combination
/-- info: 'SKQD.chebyshevFilter_off_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.chebyshevFilter_off_band
/-- info: 'SKQD.chebyshevFilter_bounded_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.chebyshevFilter_bounded_expansion
/-- info: 'SKQD.filterFourierCoeff_sum_sq_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.filterFourierCoeff_sum_sq_le_one
/-- info: 'SKQD.exp_apply_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.exp_apply_eigenvector
/-- info: 'SKQD.exact_krylov_probabilistic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.exact_krylov_probabilistic
/-- info: 'SKQD.sufficientOddDimension_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.sufficientOddDimension_error
/-- info: 'SKQD.retained_sparsity_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.retained_sparsity_ge_half

/-- info: 'SKQD.spectral_chebyshev_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.spectral_chebyshev_energy
/-- info: 'SKQD.exists_centered_krylov_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.exists_centered_krylov_witness
/-- info: 'SKQD.exists_exactKrylovWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.exists_exactKrylovWitness
/-- info: 'SKQD.paper_theorem1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.paper_theorem1
/-- info: 'SKQD.measurable_exactSKQDOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.measurable_exactSKQDOutput
/-- info: 'SKQD.success_probability_of_bad_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.success_probability_of_bad_probability

/-- info: 'SKQD.paper_theorem1_constructive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.paper_theorem1_constructive
/-- info: 'SKQD.resourceCounts_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.resourceCounts_isBigO
/-- info: 'SKQD.evolutionTime_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SKQD.evolutionTime_isBigO

example : ∃ c : ℂ, ‖c‖ = 1 ∧ c * 0 = (‖(0 : ℂ)‖ : ℂ) :=
  SKQD.exists_aligning_phase 0

example (a : ℝ) (ha : 0 ≤ a) (haπ : a < Real.pi) :
    SKQD.chebyshevFilter 0 a 0 = 1 := SKQD.chebyshevFilter_zero 0 ha haπ

example (threshold : ℝ) : 0 < SKQD.sufficientShots threshold ∧
    threshold ≤ (SKQD.sufficientShots threshold : ℝ) :=
  ⟨SKQD.sufficientShots_pos threshold, SKQD.sufficientShots_meets_threshold threshold⟩

example : SKQD.effectiveOddDimension 1 = 1 := by decide
example : SKQD.effectiveOddDimension 2 = 1 := by decide
example : SKQD.effectiveOddDimension 5 = 5 := by decide
example : SKQD.effectiveOddDimension 6 = 5 := by decide
