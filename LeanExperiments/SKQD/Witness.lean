import LeanExperiments.SKQD.FilterBridge
import LeanExperiments.SKQD.ExactGuarantee

/-! Constructing the exact Krylov witness rather than assuming it. -/
namespace SKQD

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unshift_centered_sum (H : E →L[ℂ] E) (ψ₀ : E) (m : ℕ) (t : ℝ) (c : ℤ → ℂ) :
    (∑ j : Fin (2 * m + 1), c ((m : ℤ) - (j : ℕ)) • krylovFamily H ψ₀ t (2 * m + 1) j) =
      timeEvolution H ((m : ℝ) * t)
        (∑ k ∈ Finset.Icc (-(m : ℤ)) m, c k • timeEvolution H (-(k : ℝ) * t) ψ₀) := by
  rw [map_sum]
  simp_rw [map_smul]
  apply Finset.sum_bij (fun (j : Fin (2 * m + 1)) _ => (m : ℤ) - (j : ℕ))
  · intro j _
    simp only [Finset.mem_Icc]
    have := j.isLt
    constructor <;> omega
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    refine ⟨⟨((m : ℤ) - k).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only
    omega
  · intro j _
    congr 1
    rw [← mul_apply_eq_comp, ← timeEvolution_add]
    unfold krylovFamily
    congr 2
    push_cast
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under the paper's non-endpoint spectral assumptions and odd dimension,
the exact Krylov witness is a theorem, not an additional hypothesis. -/
theorem exists_exactKrylovWitness_odd
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (hsym : (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (m : ℕ) (gap W : ℝ)
    (hψ₀ : ‖ψ₀‖ = 1) (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖)
    (hgap : 0 < gap) (hgapW : gap < W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    Nonempty (ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (2 * m + 1)) (2 * m + 1)) := by
  obtain ⟨c, hc, hn, hec⟩ := exists_centered_krylov_witness H b e heigen (b.repr ψ₀) j₀ m gap W
    (by simpa using hψ₀) (by simpa [b.repr_apply_apply] using hγ) hgap hgapW he
  simp only [b.repr.symm_apply_apply, b.repr_apply_apply] at hn hec hc
  refine ⟨⟨fun j => c ((m : ℤ) - (j : ℕ)), ?_, ?_, ?_⟩⟩
  · rw [unshift_centered_sum, timeEvolution_norm H _ _ hsym]
    exact hn
  · intro j
    apply hc
    simp only [Finset.mem_Icc]
    have := j.isLt
    constructor <;> omega
  · rw [unshift_centered_sum, timeEvolution_energy_inner H _ _ _ hsym]
    exact hec

end SKQD
