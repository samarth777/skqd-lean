import LeanExperiments.SKQD.Fourier
import LeanExperiments.SKQD.Sparsity
import LeanExperiments.SKQD.Resources

/-! Spectral filtering in the orthonormal eigenbasis used in Appendix A.
The eigenbasis and eigenvalue bounds are input data, as in the paper;
the filtered-state normalization and Rayleigh quotient are not assumptions. -/
namespace SKQD

set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem eigenbasis_energy (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E)
    (e : ι → ℝ) (he : ∀ j, H (b j) = (e j : ℂ) • b j)
    (u : EuclideanSpace ℂ ι) :
    (inner ℂ (b.repr.symm u) (H (b.repr.symm u))).re = ∑ j, e j * ‖u j‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun j => (e j : ℂ) * u j)
  have hH : H (b.repr.symm u) = b.repr.symm v := by
    rw [← b.sum_repr_symm u, ← b.sum_repr_symm v, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, he, smul_smul]
    change (u j * (e j : ℂ)) • b j = ((e j : ℂ) * u j) • b j
    rw [mul_comm]
  rw [hH, b.repr.symm.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (((e j : ℂ) * u j) * star (u j)).re = _
  have hh : ((e j : ℂ) * u j) * star (u j) =
      (e j : ℂ) * ((‖u j‖ ^ 2 : ℝ) : ℂ) := by
    change (e j : ℂ) * u j * (starRingEnd ℂ) (u j) = _
    rw [mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [hh]
  norm_cast

noncomputable def filteredCoordinates (u : EuclideanSpace ℂ ι) (q : ι → ℂ) :
    EuclideanSpace ℂ ι := WithLp.toLp 2 (fun j => q j * u j)

@[simp] lemma filteredCoordinates_apply (u : EuclideanSpace ℂ ι) (q : ι → ℂ) (j : ι) :
    filteredCoordinates u q j = q j * u j := rfl

lemma filteredCoordinates_ground_lower (u : EuclideanSpace ℂ ι) (q : ι → ℂ)
    (j₀ : ι) (hq₀ : q j₀ = 1) : ‖u j₀‖ ≤ ‖filteredCoordinates u q‖ := by
  have hh := hitProb_le_norm_sq (filteredCoordinates u q) j₀
  simp only [hitProb, filteredCoordinates_apply, hq₀, one_mul] at hh
  nlinarith [norm_nonneg (u j₀), norm_nonneg (filteredCoordinates u q)]

/-- The numerator of Eq. (38), with gaps rather than unshifted eigenvalues. -/
theorem filtered_numerator_bound (u : EuclideanSpace ℂ ι) (q : ι → ℂ)
    (e : ι → ℝ) (j₀ : ι) (W B : ℝ) (hu : ‖u‖ = 1)
    (hW : 0 ≤ W) (hB : 0 ≤ B)
    (he : ∀ j, 0 ≤ e j - e j₀ ∧ e j - e j₀ ≤ W)
    (hq : ∀ j, j ≠ j₀ → ‖q j‖ ≤ B) :
    ∑ j, (e j - e j₀) * ‖filteredCoordinates u q j‖ ^ 2 ≤
      W * B ^ 2 * (1 - ‖u j₀‖ ^ 2) := by
  have hterm : ∀ j ∈ Finset.univ.erase j₀,
      (e j - e j₀) * ‖filteredCoordinates u q j‖ ^ 2 ≤ W * B ^ 2 * ‖u j‖ ^ 2 := by
    intro j hj
    have hjne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    have hqj : ‖q j‖ ^ 2 ≤ B ^ 2 := by nlinarith [hq j hjne, norm_nonneg (q j)]
    simp only [filteredCoordinates_apply, norm_mul, mul_pow]
    calc
      _ ≤ W * (‖q j‖ ^ 2 * ‖u j‖ ^ 2) := mul_le_mul_of_nonneg_right (he j).2 (by positivity)
      _ ≤ W * (B ^ 2 * ‖u j‖ ^ 2) := by gcongr
      _ = _ := by ring
  have hmass : ∑ j ∈ Finset.univ.erase j₀, ‖u j‖ ^ 2 = 1 - ‖u j₀‖ ^ 2 := by
    have hh := Finset.sum_erase_add (s := Finset.univ) (fun j => ‖u j‖ ^ 2)
      (Finset.mem_univ j₀)
    rw [← EuclideanSpace.norm_sq_eq, hu] at hh
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, hmass] at hsum
  have hzero : (e j₀ - e j₀) * ‖filteredCoordinates u q j₀‖ ^ 2 = 0 := by ring
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (fun j => (e j - e j₀) * ‖filteredCoordinates u q j‖ ^ 2) (Finset.mem_univ j₀), hzero, add_zero]
  exact hsum

/-- Eq. (38): normalization costs at most the inverse ground overlap squared. -/
theorem filtered_rayleigh_bound (u : EuclideanSpace ℂ ι) (q : ι → ℂ)
    (e : ι → ℝ) (j₀ : ι) (W B : ℝ) (hu : ‖u‖ = 1)
    (hγ : 0 < ‖u j₀‖) (hq₀ : q j₀ = 1) (hW : 0 ≤ W) (hB : 0 ≤ B)
    (he : ∀ j, 0 ≤ e j - e j₀ ∧ e j - e j₀ ≤ W)
    (hq : ∀ j, j ≠ j₀ → ‖q j‖ ≤ B) :
    (∑ j, (e j - e j₀) * ‖filteredCoordinates u q j‖ ^ 2) /
      ‖filteredCoordinates u q‖ ^ 2 ≤ W * B ^ 2 * (1 - ‖u j₀‖ ^ 2) / ‖u j₀‖ ^ 2 := by
  have hnorm := filteredCoordinates_ground_lower u q j₀ hq₀
  have hnum := filtered_numerator_bound u q e j₀ W B hu hW hB he hq
  have hmass : ‖u j₀‖ ^ 2 ≤ 1 := by simpa [hitProb] using hitProb_le_one hu j₀
  have hnpos : 0 < ‖filteredCoordinates u q‖ := hγ.trans_le hnorm
  have hden : 0 < ‖filteredCoordinates u q‖ ^ 2 := by positivity
  calc
    _ ≤ (W * B ^ 2 * (1 - ‖u j₀‖ ^ 2)) / ‖filteredCoordinates u q‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [norm_nonneg (filteredCoordinates u q)])

noncomputable def normalizedCoordinates (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  ((‖v‖ : ℂ)⁻¹) • v

theorem normalizedCoordinates_norm (v : EuclideanSpace ℂ ι) (hv : 0 < ‖v‖) :
    ‖normalizedCoordinates v‖ = 1 := by
  simp [normalizedCoordinates, norm_smul, norm_inv, hv.ne']

theorem normalized_eigenbasis_energy (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E)
    (e : ι → ℝ) (he : ∀ j, H (b j) = (e j : ℂ) • b j)
    (v : EuclideanSpace ℂ ι) (hv : 0 < ‖v‖) (E₀ : ℝ) :
    (inner ℂ (b.repr.symm (normalizedCoordinates v))
      (H (b.repr.symm (normalizedCoordinates v)))).re - E₀ =
      (∑ j, (e j - E₀) * ‖v j‖ ^ 2) / ‖v‖ ^ 2 := by
  rw [eigenbasis_energy H b e he]
  have hc : ∀ j, ‖normalizedCoordinates v j‖ ^ 2 = ‖v j‖ ^ 2 / ‖v‖ ^ 2 := by
    intro j
    change ‖(‖v‖ : ℂ)⁻¹ * v j‖ ^ 2 = _
    simp [norm_inv, mul_pow, div_eq_mul_inv, mul_comm]
  simp_rw [hc, ← mul_div_assoc]
  rw [← Finset.sum_div]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← EuclideanSpace.norm_sq_eq]
  field_simp

/-- The normalized spectral filter satisfies Eq. (38), with no assumed
normalization or assumed energy conclusion. -/
theorem normalized_filtered_energy_bound
    (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (u : EuclideanSpace ℂ ι) (q : ι → ℂ) (j₀ : ι) (W B : ℝ)
    (hu : ‖u‖ = 1) (hγ : 0 < ‖u j₀‖) (hq₀ : q j₀ = 1)
    (hW : 0 ≤ W) (hB : 0 ≤ B)
    (he : ∀ j, 0 ≤ e j - e j₀ ∧ e j - e j₀ ≤ W)
    (hq : ∀ j, j ≠ j₀ → ‖q j‖ ≤ B) :
    ‖b.repr.symm (normalizedCoordinates (filteredCoordinates u q))‖ = 1 ∧
    (inner ℂ (b.repr.symm (normalizedCoordinates (filteredCoordinates u q)))
      (H (b.repr.symm (normalizedCoordinates (filteredCoordinates u q))))).re - e j₀ ≤
        W * B ^ 2 * (1 - ‖u j₀‖ ^ 2) / ‖u j₀‖ ^ 2 := by
  have hv : 0 < ‖filteredCoordinates u q‖ :=
    hγ.trans_le (filteredCoordinates_ground_lower u q j₀ hq₀)
  constructor
  · rw [b.repr.symm.norm_map]
    exact normalizedCoordinates_norm _ hv
  · rw [normalized_eigenbasis_energy H b e heigen _ hv]
    exact filtered_rayleigh_bound u q e j₀ W B hu hγ hq₀ hW hB he hq

noncomputable def spectralChebyshev (m : ℕ) (gap W : ℝ) (e : ι → ℝ) (j₀ : ι) (j : ι) : ℂ :=
  chebyshevFilter m (Real.pi * gap / W) ((e j - e j₀) * (Real.pi / W))

theorem spectralChebyshev_bounds (m : ℕ) (gap W : ℝ) (e : ι → ℝ) (j₀ : ι)
    (hgap : 0 < gap) (hgapW : gap < W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    spectralChebyshev m gap W e j₀ j₀ = 1 ∧
    ∀ j, j ≠ j₀ → ‖spectralChebyshev m gap W e j₀ j‖ ≤
      2 / (1 + Real.pi * gap / W) ^ m := by
  have hW : 0 < W := hgap.trans hgapW
  have ha : 0 ≤ Real.pi * gap / W := by positivity
  have haπ : Real.pi * gap / W < Real.pi := by
    apply (div_lt_iff₀ hW).mpr
    nlinarith [Real.pi_pos]
  constructor
  · simp [spectralChebyshev, chebyshevFilter_zero m ha haπ]
  · intro j hj
    obtain ⟨hl, hu⟩ := he j hj
    have ht : 0 ≤ (e j - e j₀) * (Real.pi / W) := mul_nonneg (by linarith) (by positivity)
    have hupper : (e j - e j₀) * (Real.pi / W) ≤ Real.pi := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hW).mpr
      nlinarith [Real.pi_pos]
    have hlower : Real.pi * gap / W ≤ (e j - e j₀) * (Real.pi / W) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hW).mpr
      nlinarith [Real.pi_pos]
    simpa only [spectralChebyshev, Complex.norm_real, Real.norm_eq_abs] using
      chebyshevFilter_off_band m ha haπ (by simpa [abs_of_nonneg ht] using hupper)
        (by simpa [abs_of_nonneg ht] using hlower)

/-- The concrete spectral Chebyshev state satisfies the paper's odd-`d`
energy bound. Membership in the physical Krylov family is a separate step. -/
theorem spectral_chebyshev_energy
    (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (u : EuclideanSpace ℂ ι) (j₀ : ι) (m : ℕ) (gap W : ℝ)
    (hu : ‖u‖ = 1) (hγ : 0 < ‖u j₀‖) (hgap : 0 < gap) (hgapW : gap < W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    let ψ := b.repr.symm (normalizedCoordinates
      (filteredCoordinates u (spectralChebyshev m gap W e j₀)))
    ‖ψ‖ = 1 ∧ (inner ℂ ψ (H ψ)).re - e j₀ ≤
      paperKrylovError W gap (‖u j₀‖ ^ 2) (2 * m + 1) := by
  have hW : 0 < W := hgap.trans hgapW
  have ha : 0 < 1 + Real.pi * gap / W := by positivity
  obtain ⟨hq₀, hq⟩ := spectralChebyshev_bounds m gap W e j₀ hgap hgapW he
  have heg : ∀ j, 0 ≤ e j - e j₀ ∧ e j - e j₀ ≤ W := by
    intro j
    by_cases hj : j = j₀
    · subst j; simp [hW.le]
    · exact ⟨hgap.le.trans (he j hj).1, (he j hj).2⟩
  obtain ⟨hn, henergy⟩ := normalized_filtered_energy_bound H b e heigen u
    (spectralChebyshev m gap W e j₀) j₀ W (2 / (1 + Real.pi * gap / W) ^ m)
    hu hγ hq₀ hW.le (by positivity) heg hq
  refine ⟨hn, henergy.trans ?_⟩
  have hmass : 0 ≤ 1 - ‖u j₀‖ ^ 2 := by
    have := hitProb_le_one hu j₀
    simpa only [hitProb, sub_nonneg] using this
  have hid : W * (2 / (1 + Real.pi * gap / W) ^ m) ^ 2 * (1 - ‖u j₀‖ ^ 2) / ‖u j₀‖ ^ 2 =
      (4 * W * (1 - ‖u j₀‖ ^ 2) / ‖u j₀‖ ^ 2) / (1 + Real.pi * gap / W) ^ (2 * m) := by
    rw [Nat.mul_comm 2 m, pow_mul]
    ring
  rw [hid]
  simp only [paperKrylovError, Nat.add_sub_cancel]
  gcongr
  norm_num

/-- The spectral assumptions imply the abstract ground-state gap used by
Appendix B; the final theorem need not assume this consequence separately. -/
theorem groundStateGap_of_eigenbasis
    (H : E →L[ℂ] E) (b : OrthonormalBasis ι ℂ E) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric) (j₀ : ι) (gap : ℝ) (hgap : 0 < gap)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀) : GroundStateGap H (b j₀) (e j₀) gap := by
  refine ⟨b.orthonormal.norm_eq_one j₀, heigen j₀, hsym, hgap, ?_⟩
  intro ψ horth hψ
  have hc₀ : b.repr ψ j₀ = 0 := by simpa only [b.repr_apply_apply] using horth
  have hmass : ∑ j, ‖b.repr ψ j‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, b.repr.norm_map, hψ]
    norm_num
  have henergy := eigenbasis_energy H b e heigen (b.repr ψ)
  rw [b.repr.symm_apply_apply] at henergy
  rw [henergy]
  calc
    e j₀ + gap = (e j₀ + gap) * ∑ j, ‖b.repr ψ j‖ ^ 2 := by rw [hmass, mul_one]
    _ = ∑ j, (e j₀ + gap) * ‖b.repr ψ j‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = j₀
      · subst j; simp [hc₀]
      · apply mul_le_mul_of_nonneg_right (by linarith [he j hj]) (sq_nonneg _)

end SKQD
