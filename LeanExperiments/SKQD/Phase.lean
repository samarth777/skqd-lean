import LeanExperiments.SKQD.Basic

/-! Global phase alignment, including the zero-overlap case. -/
namespace SKQD
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_aligning_phase (z : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  refine ⟨(‖z‖ : ℂ) / z, ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hz)
  · exact div_mul_cancel₀ _ hz

theorem energy_phase_invariant (H : E →L[ℂ] E) (ψ : E) (c : ℂ)
    (hc : ‖c‖ = 1) :
    inner ℂ (c • ψ) (H (c • ψ)) = inner ℂ ψ (H ψ) := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
  have hmul : starRingEnd ℂ c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [hmul, one_mul]

/-- Every normalized linear combination can be phase-aligned without changing
its energy or any coefficient norm. -/
theorem align_combination {κ : Type*} [Fintype κ]
    (H : E →L[ℂ] E) (φ : E) (v : κ → E) (coeff : κ → ℂ) :
    ∃ coeff' : κ → ℂ,
      (∀ k, ‖coeff' k‖ = ‖coeff k‖) ∧
      ‖∑ k, coeff' k • v k‖ = ‖∑ k, coeff k • v k‖ ∧
      inner ℂ (∑ k, coeff' k • v k) (H (∑ k, coeff' k • v k)) =
        inner ℂ (∑ k, coeff k • v k) (H (∑ k, coeff k • v k)) ∧
      (inner ℂ φ (∑ k, coeff' k • v k)).im = 0 ∧
      0 ≤ (inner ℂ φ (∑ k, coeff' k • v k)).re := by
  obtain ⟨c, hc, hz⟩ := exists_aligning_phase (inner ℂ φ (∑ k, coeff k • v k))
  have hsum : (∑ k, (c * coeff k) • v k) = c • ∑ k, coeff k • v k := by
    simp [Finset.smul_sum, smul_smul]
  refine ⟨fun k => c * coeff k, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simp [hc]
  · rw [hsum, norm_smul, hc, one_mul]
  · rw [hsum]; exact energy_phase_invariant H _ c hc
  · rw [hsum, inner_smul_right, hz]; simp
  · rw [hsum, inner_smul_right, hz]; exact norm_nonneg _

end SKQD
