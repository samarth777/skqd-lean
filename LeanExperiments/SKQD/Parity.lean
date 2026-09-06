import LeanExperiments.SKQD.Endpoint

/-! The paper's reduction of even dimension to the preceding odd dimension. -/
namespace SKQD
open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ExactKrylovWitness.pad {d : ℕ}
    {H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    {φ₀ ψ₀ : EuclideanSpace ℂ ι} {t E₀ ε : ℝ}
    (w : ExactKrylovWitness H φ₀ ψ₀ t E₀ ε d) :
    ExactKrylovWitness H φ₀ ψ₀ t E₀ ε (d + 1) := by
  let c : Fin (d + 1) → ℂ := Fin.lastCases 0 w.coeff
  have hsum : (∑ j, c j • krylovFamily H ψ₀ t (d + 1) j) =
      ∑ j, w.coeff j • krylovFamily H ψ₀ t d j := by
    rw [Fin.sum_univ_castSucc]
    simp only [c, Fin.lastCases_castSucc, Fin.lastCases_last, zero_smul, add_zero]
    rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hsum]; exact w.normalized
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [c]
    · simpa [c] using w.coefficient_bound k
  · rw [hsum]; exact w.energy_bound

def effectiveOddDimension (d : ℕ) : ℕ := 2 * ((d - 1) / 2) + 1

theorem effectiveOddDimension_cases {d : ℕ} (hd : 0 < d) :
    d = effectiveOddDimension d ∨ d = effectiveOddDimension d + 1 := by
  unfold effectiveOddDimension
  omega

theorem exists_exactKrylovWitness
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (hsym : (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (d : ℕ) (gap W : ℝ)
    (hψ₀ : ‖ψ₀‖ = 1) (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖)
    (hd : 0 < d) (hgap : 0 < gap) (hgapW : gap ≤ W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    Nonempty (ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (effectiveOddDimension d)) d) := by
  obtain ⟨w⟩ := exists_exactKrylovWitness_all_odd H b e heigen hsym ψ₀ j₀ ((d - 1) / 2)
    gap W hψ₀ hγ hgap hgapW he
  change ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
    (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (effectiveOddDimension d))
      (effectiveOddDimension d) at w
  rcases effectiveOddDimension_cases hd with h | h
  · exact ⟨cast (congrArg (fun n => ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (effectiveOddDimension d)) n) h.symm) w⟩
  · exact ⟨cast (congrArg (fun n => ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (effectiveOddDimension d)) n) h.symm) w.pad⟩

end SKQD
