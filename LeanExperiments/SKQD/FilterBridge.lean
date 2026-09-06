import LeanExperiments.SKQD.SpectralFilter
import LeanExperiments.SKQD.Krylov

/-! Identifying the spectral filter with a physical, centered Krylov sum. -/
namespace SKQD

set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem timeEvolution_eigenvector (H : E →L[ℂ] E) (ψ : E) (e t : ℝ)
    (he : H ψ = (e : ℂ) • ψ) :
    timeEvolution H t ψ = Complex.exp ((-(t : ℂ) * Complex.I) * e) • ψ := by
  unfold timeEvolution
  rw [exp_apply_eigenvector _ ψ ((-(t : ℂ) * Complex.I) * e)]
  · rw [← Complex.exp_eq_exp_ℂ]
  · change (-(t : ℂ) * Complex.I) • H ψ = _
    rw [he, smul_smul]

theorem timeEvolution_eigenbasis (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E)
    (e : ι → ℝ) (he : ∀ j, H (b j) = (e j : ℂ) • b j)
    (u : EuclideanSpace ℂ ι) (t : ℝ) :
    timeEvolution H t (b.repr.symm u) =
      b.repr.symm (filteredCoordinates u (fun j => Complex.exp ((-(t : ℂ) * Complex.I) * e j))) := by
  rw [← b.sum_repr_symm, ← b.sum_repr_symm, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, timeEvolution_eigenvector H (b j) (e j) t (he j), smul_smul]
  simp only [filteredCoordinates_apply]
  rw [mul_comm]

noncomputable def centeredFilterCoeff (c : ℤ → ℂ) (E₀ t : ℝ) (k : ℤ) : ℂ :=
  c k * phaseMode k (-E₀ * t)

lemma centeredFilterCoeff_norm (c : ℤ → ℂ) (E₀ t : ℝ) (k : ℤ) :
    ‖centeredFilterCoeff c E₀ t k‖ = ‖c k‖ := by
  unfold centeredFilterCoeff phaseMode
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Eq. (36), including the ground-energy phase shift and the sign of the
physical propagator. The same coefficients used here are bounded in norm. -/
theorem centered_filter_identity (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E)
    (e : ι → ℝ) (he : ∀ j, H (b j) = (e j : ℂ) • b j)
    (u : EuclideanSpace ℂ ι) (m : ℕ) (a E₀ t : ℝ) (c : ℤ → ℂ)
    (hc : ∀ θ, ∑ k ∈ Finset.Icc (-(m : ℤ)) m, c k * phaseMode k θ =
      (chebyshevFilter m a θ : ℂ)) :
    (∑ k ∈ Finset.Icc (-(m : ℤ)) m, centeredFilterCoeff c E₀ t k •
      timeEvolution H (-(k : ℝ) * t) (b.repr.symm u)) =
      b.repr.symm (filteredCoordinates u (fun j => (chebyshevFilter m a ((e j - E₀) * t) : ℂ))) := by
  simp_rw [timeEvolution_eigenbasis H b e he]
  simp_rw [← map_smul b.repr.symm]
  rw [← map_sum]
  congr 1
  ext j
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, filteredCoordinates_apply]
  have hterm : ∀ k : ℤ, centeredFilterCoeff c E₀ t k *
      (Complex.exp ((-(((-(k : ℝ) * t) : ℝ) : ℂ) * Complex.I) * e j) * u j) =
      (c k * phaseMode k ((e j - E₀) * t)) * u j := by
    intro k
    unfold centeredFilterCoeff phaseMode
    rw [mul_assoc (c k), ← mul_assoc (Complex.exp _), ← Complex.exp_add]
    rw [← mul_assoc]
    congr 2
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, hc]

/-- Simultaneous normalization, coefficient control, and energy control
for a centered physical Krylov sum, derived from the paper's spectral data. -/
theorem exists_centered_krylov_witness
    (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (u : EuclideanSpace ℂ ι) (j₀ : ι) (m : ℕ) (gap W : ℝ)
    (hu : ‖u‖ = 1) (hγ : 0 < ‖u j₀‖) (hgap : 0 < gap) (hgapW : gap < W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    ∃ c : ℤ → ℂ,
      (∀ k ∈ Finset.Icc (-(m : ℤ)) m, ‖c k‖ * ‖u j₀‖ ≤ 1) ∧
      let ψ := ∑ k ∈ Finset.Icc (-(m : ℤ)) m, c k •
        timeEvolution H (-(k : ℝ) * (Real.pi / W)) (b.repr.symm u)
      ‖ψ‖ = 1 ∧ (inner ℂ ψ (H ψ)).re - e j₀ ≤
        paperKrylovError W gap (‖u j₀‖ ^ 2) (2 * m + 1) := by
  have hW : 0 < W := hgap.trans hgapW
  have ha : 0 ≤ Real.pi * gap / W := by positivity
  have haπ : Real.pi * gap / W < Real.pi := by
    apply (div_lt_iff₀ hW).mpr
    nlinarith [Real.pi_pos]
  obtain ⟨c, hc_bound, hc⟩ := chebyshevFilter_bounded_expansion m ha haπ
  let v := filteredCoordinates u (spectralChebyshev m gap W e j₀)
  have hq₀ := (spectralChebyshev_bounds m gap W e j₀ hgap hgapW he).1
  have hlower : ‖u j₀‖ ≤ ‖v‖ := filteredCoordinates_ground_lower u _ j₀ hq₀
  have hv : 0 < ‖v‖ := hγ.trans_le hlower
  let d : ℤ → ℂ := fun k => (‖v‖ : ℂ)⁻¹ * centeredFilterCoeff c (e j₀) (Real.pi / W) k
  have hid : (∑ k ∈ Finset.Icc (-(m : ℤ)) m,
      d k • timeEvolution H (-(k : ℝ) * (Real.pi / W)) (b.repr.symm u)) =
      b.repr.symm (normalizedCoordinates v) := by
    simp only [d, mul_smul, ← Finset.smul_sum]
    rw [centered_filter_identity H b e heigen u m _ _ _ c hc]
    rw [← map_smul]
    rfl
  refine ⟨d, ?_, ?_⟩
  · intro k hk
    have hn : ‖d k‖ = ‖c k‖ / ‖v‖ := by
      simp [d, centeredFilterCoeff_norm, norm_inv, div_eq_mul_inv, mul_comm]
    rw [hn, div_mul_eq_mul_div]
    apply (div_le_one hv).mpr
    calc
      ‖c k‖ * ‖u j₀‖ ≤ 1 * ‖u j₀‖ := mul_le_mul_of_nonneg_right (hc_bound k hk) (norm_nonneg _)
      _ ≤ ‖v‖ := by simpa using hlower
  · dsimp only
    rw [hid]
    exact spectral_chebyshev_energy H b e heigen u j₀ m gap W hu hγ hgap hgapW he

end SKQD
