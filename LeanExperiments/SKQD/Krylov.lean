import LeanExperiments.SKQD.Basic
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Exact finite-dimensional Krylov time evolution. -/

namespace SKQD

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The exact propagator `exp(-i t H)`. -/
noncomputable def timeEvolution (H : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • H)

/-- The `d` exact time-evolved states used by KQD. -/
noncomputable def krylovFamily (H : E →L[ℂ] E) (ψ₀ : E) (Δt : ℝ) (d : ℕ) :
    Fin d → E :=
  fun k => timeEvolution H ((k : ℕ) * Δt) ψ₀

@[simp] lemma krylovFamily_zero {H : E →L[ℂ] E} {ψ₀ : E} {Δt : ℝ} {d : ℕ}
    (hd : 0 < d) :
    krylovFamily H ψ₀ Δt d ⟨0, hd⟩ = ψ₀ := by
  simp [krylovFamily, timeEvolution]

theorem timeEvolution_norm (H : E →L[ℂ] E) (t : ℝ) (ψ : E)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric) :
    ‖timeEvolution H t ψ‖ = ‖ψ‖ := by
  let a : selfAdjoint (E →L[ℂ] E) :=
    ⟨(-(t : ℂ)) • H, by
      change star ((-(t : ℂ)) • H) = (-(t : ℂ)) • H
      rw [star_smul, ContinuousLinearMap.star_eq_adjoint, hsym.clm_adjoint_eq]
      simp⟩
  let u : unitary (E →L[ℂ] E) := selfAdjoint.expUnitary a
  have hu := Unitary.norm_map u ψ
  have harg : Complex.I • ((-(t : ℂ)) • H) =
      (-(t : ℂ) * Complex.I) • H := by
    rw [smul_smul]
    congr 1
    ring
  simp only [u, a, selfAdjoint.expUnitary, Subtype.coe_mk] at hu
  rw [harg] at hu
  simpa [timeEvolution, mul_comm] using hu

theorem krylovFamily_normalized (H : E →L[ℂ] E) (ψ₀ : E) (Δt : ℝ) (d : ℕ)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric) (hψ₀ : ‖ψ₀‖ = 1) :
    ∀ k, ‖krylovFamily H ψ₀ Δt d k‖ = 1 := by
  intro k
  rw [krylovFamily, timeEvolution_norm H _ ψ₀ hsym, hψ₀]

theorem timeEvolution_add (H : E →L[ℂ] E) (s t : ℝ) :
    timeEvolution H (s + t) = timeEvolution H s * timeEvolution H t := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  unfold timeEvolution
  have harg : (-((s + t : ℝ) : ℂ) * Complex.I) • H =
      (-(s : ℂ) * Complex.I) • H + (-(t : ℂ) * Complex.I) • H := by
    rw [← add_smul]
    congr 1
    push_cast
    ring
  rw [harg]
  exact NormedSpace.exp_add_of_commute (((Commute.refl H).smul_left _).smul_right _)

theorem timeEvolution_commute (H : E →L[ℂ] E) (t : ℝ) :
    Commute H (timeEvolution H t) :=
  ((Commute.refl H).smul_right _).exp_right

theorem timeEvolution_inner (H : E →L[ℂ] E) (t : ℝ) (x y : E)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric) :
    inner ℂ (timeEvolution H t x) (timeEvolution H t y) = inner ℂ x y :=
  (LinearMap.norm_map_iff_inner_map_map (timeEvolution H t)).mp
    (fun ψ => timeEvolution_norm H t ψ hsym) x y

/-- Simultaneously shifting all time indices preserves every projected
Hamiltonian entry, not only the norms of individual Krylov states. -/
theorem timeEvolution_energy_inner (H : E →L[ℂ] E) (t : ℝ) (x y : E)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric) :
    inner ℂ (timeEvolution H t x) (H (timeEvolution H t y)) = inner ℂ x (H y) := by
  have hc : H (timeEvolution H t y) = timeEvolution H t (H y) :=
    DFunLike.congr_fun (timeEvolution_commute H t).eq y
  rw [hc, timeEvolution_inner H t x (H y) hsym]

/-- Equation (32): the centered family is the ordinary family with a
common unitary time shift. -/
theorem centered_krylov_eq_shift (H : E →L[ℂ] E) (ψ₀ : E) (Δt : ℝ)
    (m k : ℕ) :
    timeEvolution H (((k : ℝ) - m) * Δt) ψ₀ =
      timeEvolution H (-((m : ℝ) * Δt)) (timeEvolution H ((k : ℝ) * Δt) ψ₀) := by
  have ht : ((k : ℝ) - m) * Δt = -((m : ℝ) * Δt) + (k : ℝ) * Δt := by ring
  rw [ht, timeEvolution_add]
  rfl

/-- Operator exponentiation acts on an eigenvector by scalar exponentiation. -/
theorem exp_apply_eigenvector (H : E →L[ℂ] E) (ψ : E) (ζ : ℂ)
    (heigen : H ψ = ζ • ψ) : NormedSpace.exp H ψ = NormedSpace.exp ζ • ψ := by
  have hpow : ∀ n : ℕ, (H ^ n) ψ = ζ ^ n • ψ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ, mul_apply_eq_comp, heigen, map_smul, ih, smul_smul]
      rw [mul_comm]
  have hsum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) H).mapL
    (ContinuousLinearMap.apply ℂ E ψ)
  have hscalar := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ζ).smul_const ψ
  have hterms : (fun n : ℕ => (ContinuousLinearMap.apply ℂ E ψ)
      ((n.factorial : ℂ)⁻¹ • H ^ n)) =
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • ζ ^ n) • ψ) := by
    funext n
    simp [hpow, smul_smul]
  rw [hterms] at hsum
  exact hsum.unique hscalar

end SKQD
