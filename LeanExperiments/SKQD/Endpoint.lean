import LeanExperiments.SKQD.Witness

/-! The two-level endpoint `gap = W`. -/
namespace SKQD
open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem two_level_projection
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (W : ℝ) (hW : 0 < W)
    (he : ∀ j, j ≠ j₀ → e j - e j₀ = W) :
    (1 / 2 : ℂ) • ψ₀ +
      (Complex.exp ((e j₀ : ℂ) * (Real.pi / W : ℝ) * Complex.I) / 2) •
        timeEvolution H (Real.pi / W) ψ₀ =
      inner ℂ (b j₀) ψ₀ • b j₀ := by
  let t : ℝ := Real.pi / W
  have hphase : ∀ j, Complex.exp ((e j₀ : ℂ) * (t : ℂ) * Complex.I) *
      Complex.exp ((-(t : ℂ) * Complex.I) * e j) = if j = j₀ then 1 else -1 := by
    intro j
    rw [← Complex.exp_add]
    by_cases hj : j = j₀
    · subst j
      rw [if_pos rfl]
      convert Complex.exp_zero using 1
      congr 1
      ring
    · rw [if_neg hj]
      convert Complex.exp_neg_pi_mul_I using 1
      congr 1
      have hh : e j = W + e j₀ := by linarith [he j hj]
      rw [hh]
      dsimp [t]
      push_cast
      have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
      field_simp [hWc]
      ring
  apply b.repr.injective
  have ht := timeEvolution_eigenbasis H b e heigen (b.repr ψ₀) t
  rw [b.repr.symm_apply_apply] at ht
  change b.repr ((1 / 2 : ℂ) • ψ₀ + (Complex.exp ((e j₀ : ℂ) * (t : ℂ) * Complex.I) / 2) •
      timeEvolution H t ψ₀) = _
  rw [map_add, map_smul, map_smul, ht, b.repr.apply_symm_apply, map_smul, b.repr_self]
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, filteredCoordinates_apply]
  have hh := hphase j
  by_cases hj : j = j₀
  · subst j
    simp only [ite_true] at hh
    simp only [PiLp.single_apply, ite_true, mul_one, b.repr_apply_apply]
    linear_combination (inner ℂ (b j₀) ψ₀) / 2 * hh
  · simp only [if_neg hj] at hh
    simp only [PiLp.single_apply, if_neg hj, mul_zero]
    linear_combination (b.repr ψ₀ j) / 2 * hh

/-- Two time samples suffice to isolate the ground eigenspace at the
two-level endpoint. Zero padding allows any dimension at least two. -/
theorem exists_exactKrylovWitness_two_levels
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (W ε : ℝ) (d : ℕ)
    (hW : 0 < W) (hε : 0 ≤ ε) (hd : 2 ≤ d)
    (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖)
    (he : ∀ j, j ≠ j₀ → e j - e j₀ = W) :
    Nonempty (ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀) ε d) := by
  let γ := inner ℂ (b j₀) ψ₀
  let z := Complex.exp ((e j₀ : ℂ) * (Real.pi / W : ℝ) * Complex.I)
  let k₀ : Fin d := ⟨0, by omega⟩
  let k₁ : Fin d := ⟨1, by omega⟩
  have hne : k₀ ≠ k₁ := by intro h; have := congrArg Fin.val h; simp [k₀, k₁] at this
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  let raw : Fin d → ℂ := fun j => (if j = k₀ then 1 / 2 else 0) + (if j = k₁ then z / 2 else 0)
  have hraw : ∀ j, ‖raw j‖ ≤ 1 := by
    intro j
    by_cases hj0 : j = k₀
    · subst j; norm_num [raw, hne]
    · by_cases hj1 : j = k₁
      · subst j; norm_num [raw, hj0, hz]
      · simp [raw, hj0, hj1]
  have hsumraw : (∑ j, raw j • krylovFamily H ψ₀ (Real.pi / W) d j) = γ • b j₀ := by
    have hk0 : krylovFamily H ψ₀ (Real.pi / W) d k₀ = ψ₀ := by simp [krylovFamily, k₀, timeEvolution]
    have hk1 : krylovFamily H ψ₀ (Real.pi / W) d k₁ = timeEvolution H (Real.pi / W) ψ₀ := by
      simp [krylovFamily, k₁]
    simp only [raw, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hk0, hk1]
    exact two_level_projection H b e heigen ψ₀ j₀ W hW he
  let c : Fin d → ℂ := fun j => (‖γ‖ : ℂ)⁻¹ * raw j
  have hunit : ‖(‖γ‖ : ℂ)⁻¹ * γ‖ = 1 := by
    have hg : ‖γ‖ ≠ 0 := ne_of_gt hγ
    simp [norm_inv, hg]
  have hsum : (∑ j, c j • krylovFamily H ψ₀ (Real.pi / W) d j) =
      ((‖γ‖ : ℂ)⁻¹ * γ) • b j₀ := by
    simp only [c, mul_smul, ← Finset.smul_sum]
    rw [hsumraw, smul_smul]
  refine ⟨⟨c, ?_, ?_, ?_⟩⟩
  · rw [hsum, norm_smul, hunit, one_mul]
    exact b.orthonormal.norm_eq_one j₀
  · intro j
    change ‖c j‖ * ‖γ‖ ≤ 1
    have hh : ‖c j‖ * ‖γ‖ = ‖raw j‖ := by
      have hg : ‖γ‖ ≠ 0 := ne_of_gt hγ
      simp [c, norm_inv, mul_comm, hg]
    rw [hh]
    exact hraw j
  · rw [hsum, energy_phase_invariant H (b j₀) _ hunit, heigen,
      inner_smul_right, b.inner_eq_one]
    simpa using hε

theorem exists_exactKrylovWitness_one
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (gap W : ℝ)
    (hψ₀ : ‖ψ₀‖ = 1) (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖) (hW : 0 ≤ W)
    (he : ∀ j, 0 ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    Nonempty (ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) 1) 1) := by
  have hnorm : ‖inner ℂ (b j₀) ψ₀‖ ≤ 1 := by
    simpa [b.orthonormal.norm_eq_one j₀, hψ₀] using norm_inner_le_norm (b j₀) ψ₀
  have hmass : 0 ≤ 1 - ‖inner ℂ (b j₀) ψ₀‖ ^ 2 := by
    nlinarith [norm_nonneg (inner ℂ (b j₀) ψ₀)]
  have hv : filteredCoordinates (b.repr ψ₀) (fun _ => (1 : ℂ)) = b.repr ψ₀ := by
    ext j; simp
  have hn : normalizedCoordinates (b.repr ψ₀) = b.repr ψ₀ := by
    simp [normalizedCoordinates, hψ₀]
  have hh := normalized_filtered_energy_bound H b e heigen (b.repr ψ₀)
    (fun _ => (1 : ℂ)) j₀ W 1 (by simpa using hψ₀)
    (by simpa only [b.repr_apply_apply] using hγ) rfl hW zero_le_one he (by intros; simp)
  rw [hv, hn, b.repr.symm_apply_apply] at hh
  simp only [b.repr_apply_apply, one_pow, mul_one] at hh
  have hzero : krylovFamily H ψ₀ (Real.pi / W) 1 0 = ψ₀ := by
    simp [krylovFamily, timeEvolution]
  refine ⟨⟨fun _ => 1, ?_, ?_, ?_⟩⟩
  · simpa [hzero] using hψ₀
  · intro j; simpa using hnorm
  · simp only [Fin.sum_univ_one, one_smul, hzero]
    refine hh.2.trans ?_
    simp only [paperKrylovError, Nat.sub_self, pow_zero, div_one]
    gcongr
    linarith

theorem exists_exactKrylovWitness_all_odd
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (e : ι → ℝ)
    (heigen : ∀ j, H (b j) = (e j : ℂ) • b j)
    (hsym : (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).IsSymmetric)
    (ψ₀ : EuclideanSpace ℂ ι) (j₀ : ι) (m : ℕ) (gap W : ℝ)
    (hψ₀ : ‖ψ₀‖ = 1) (hγ : 0 < ‖inner ℂ (b j₀) ψ₀‖)
    (hgap : 0 < gap) (hgapW : gap ≤ W)
    (he : ∀ j, j ≠ j₀ → gap ≤ e j - e j₀ ∧ e j - e j₀ ≤ W) :
    Nonempty (ExactKrylovWitness H (b j₀) ψ₀ (Real.pi / W) (e j₀)
      (paperKrylovError W gap (‖inner ℂ (b j₀) ψ₀‖ ^ 2) (2 * m + 1)) (2 * m + 1)) := by
  rcases lt_or_eq_of_le hgapW with hlt | heq
  · exact exists_exactKrylovWitness_odd H b e heigen hsym ψ₀ j₀ m gap W hψ₀ hγ hgap hlt he
  have hW : 0 < W := hgap.trans_le hgapW
  by_cases hm : m = 0
  · subst m
    apply exists_exactKrylovWitness_one H b e heigen ψ₀ j₀ gap W hψ₀ hγ hW.le
    intro j
    by_cases hj : j = j₀
    · subst j; simp [hW.le]
    · exact ⟨hgap.le.trans (he j hj).1, (he j hj).2⟩
  · apply exists_exactKrylovWitness_two_levels H b e heigen ψ₀ j₀ W _ _ hW
    · have hnorm : ‖inner ℂ (b j₀) ψ₀‖ ≤ 1 := by
        simpa [b.orthonormal.norm_eq_one j₀, hψ₀] using norm_inner_le_norm (b j₀) ψ₀
      have hmass : 0 ≤ 1 - ‖inner ℂ (b j₀) ψ₀‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (b j₀) ψ₀)]
      unfold paperKrylovError
      positivity
    · omega
    · exact hγ
    · intro j hj
      have := he j hj
      linarith

end SKQD
