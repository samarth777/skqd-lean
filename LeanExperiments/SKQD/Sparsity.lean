import Mathlib
import LeanExperiments.SKQD.Basic

/-!
Computational-basis sparsity (Definition 1) and Lemmas 2, 3, 5 of
arXiv:2501.09702v1, Appendix B.
-/

set_option linter.unusedSectionVars false

namespace SKQD

open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Born-rule probability of computational-basis outcome `j`. -/
noncomputable def hitProb (ψ : EuclideanSpace ℂ ι) (j : ι) : ℝ := ‖ψ j‖ ^ 2

lemma hitProb_nonneg (ψ : EuclideanSpace ℂ ι) (j : ι) : 0 ≤ hitProb ψ j := by
  unfold hitProb; positivity

lemma sum_hitProb (ψ : EuclideanSpace ℂ ι) :
    ∑ j, hitProb ψ j = ‖ψ‖ ^ 2 :=
  (EuclideanSpace.norm_sq_eq ψ).symm

lemma hitProb_le_norm_sq (ψ : EuclideanSpace ℂ ι) (j : ι) :
    hitProb ψ j ≤ ‖ψ‖ ^ 2 := by
  have h : hitProb ψ j ≤ ∑ i, hitProb ψ i :=
    Finset.single_le_sum (fun i _ => hitProb_nonneg ψ i) (Finset.mem_univ j)
  simpa [sum_hitProb] using h

lemma hitProb_le_one {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (j : ι) :
    hitProb ψ j ≤ 1 := by
  have := hitProb_le_norm_sq ψ j
  simpa [hψ] using this

/-- Definition 1: `(α, β)`-sparsity on a set of computational-basis states. -/
structure Sparse (ψ : EuclideanSpace ℂ ι) (s : Finset ι) (α β : ℝ) : Prop where
  mass : α ≤ ∑ i ∈ s, hitProb ψ i
  pointwise : ∀ i ∈ s, β ≤ hitProb ψ i

noncomputable def supportMass (ψ : EuclideanSpace ℂ ι) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, hitProb ψ i

lemma supportMass_nonneg (ψ : EuclideanSpace ℂ ι) (s : Finset ι) :
    0 ≤ supportMass ψ s :=
  Finset.sum_nonneg fun _ _ => hitProb_nonneg _ _

lemma sparse_mass_pos {ψ : EuclideanSpace ℂ ι} {s : Finset ι} {α β : ℝ}
    (hα : 0 < α) (h : Sparse ψ s α β) : 0 < supportMass ψ s :=
  lt_of_lt_of_le hα h.mass

lemma coord_diff_le_dist (ψ φ : EuclideanSpace ℂ ι) (j : ι) :
    ‖(ψ - φ) j‖ ≤ ‖ψ - φ‖ := by
  have hsq : ‖(ψ - φ) j‖ ^ 2 ≤ ‖ψ - φ‖ ^ 2 := by
    simpa [hitProb] using hitProb_le_norm_sq (ψ - φ) j
  exact le_of_sq_le_sq (by linarith [hsq]) (norm_nonneg _)

lemma amp_sq_sub_bound (a d : ℂ) :
    ‖a‖ ^ 2 - 2 * ‖a‖ * ‖d‖ ≤ ‖a + d‖ ^ 2 := by
  have hexp : ‖a + d‖ ^ 2 = ‖a‖ ^ 2 + 2 * (inner ℂ a d).re + ‖d‖ ^ 2 := by
    convert norm_add_sq (𝕜 := ℂ) a d
    rfl
  have hre : - (‖a‖ * ‖d‖) ≤ (inner ℂ a d).re := by
    have := (abs_le.mp ((Complex.abs_re_le_norm (inner ℂ a d)).trans
      (norm_inner_le_norm a d))).1
    linarith
  nlinarith [hexp, hre, sq_nonneg ‖d‖]

lemma sum_subset_hitProb (ψ : EuclideanSpace ℂ ι) (s : Finset ι) :
    ∑ i ∈ s, hitProb ψ i ≤ ‖ψ‖ ^ 2 := by
  have h : ∑ i ∈ s, hitProb ψ i ≤ ∑ i, hitProb ψ i :=
    Finset.sum_le_univ_sum_of_nonneg (fun i => hitProb_nonneg ψ i)
  simpa [sum_hitProb] using h

lemma sum_amp_cs {s : Finset ι} (φ ψ : EuclideanSpace ℂ ι) (ε : ℝ)
    (hφ : ‖φ‖ = 1) (hε : 0 ≤ ε) (hdist : ‖ψ - φ‖ ^ 2 ≤ ε) :
    ∑ i ∈ s, ‖φ i‖ * ‖(ψ - φ) i‖ ≤ Real.sqrt ε := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖φ i‖) (fun i => ‖(ψ - φ) i‖)
  have hφs : ∑ i ∈ s, ‖φ i‖ ^ 2 ≤ 1 := by
    simpa [hitProb, hφ] using sum_subset_hitProb φ s
  have hds : ∑ i ∈ s, ‖(ψ - φ) i‖ ^ 2 ≤ ε := by
    have hsub := sum_subset_hitProb (ψ - φ) s
    simpa [hitProb] using hsub.trans hdist
  have hnn : 0 ≤ ∑ i ∈ s, ‖φ i‖ * ‖(ψ - φ) i‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hφnn : 0 ≤ ∑ i ∈ s, ‖φ i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdnn : 0 ≤ ∑ i ∈ s, ‖(ψ - φ) i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod : (∑ i ∈ s, ‖φ i‖ ^ 2) * ∑ i ∈ s, ‖(ψ - φ) i‖ ^ 2 ≤ ε := by
    have := mul_le_mul hφs hds hdnn (by linarith [hφs])
    simpa using this
  have hsq : (∑ i ∈ s, ‖φ i‖ * ‖(ψ - φ) i‖) ^ 2 ≤ ε :=
    le_trans hCS hprod
  exact (sq_le_sq₀ hnn (Real.sqrt_nonneg ε)).1 (by simpa [Real.sq_sqrt hε] using hsq)

lemma norm_coord_le_one {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (j : ι) :
    ‖ψ j‖ ≤ 1 :=
  (sq_le_one_iff₀ (norm_nonneg _)).1 (by simpa [hitProb] using hitProb_le_one hψ j)

lemma coord_add_diff (ψ φ : EuclideanSpace ℂ ι) (j : ι) :
    φ j + (ψ - φ) j = ψ j := by
  simp

/-- **Lemma 2.** Sparsity is stable under a small 2-norm perturbation. -/
theorem lemma2_sparsity_transfer
    {ψ φ : EuclideanSpace ℂ ι} {s : Finset ι} {α β ε : ℝ}
    (hφ : ‖φ‖ = 1) (hε : 0 ≤ ε)
    (hs : Sparse φ s α β)
    (hdist : ‖ψ - φ‖ ^ 2 ≤ ε) :
    Sparse ψ s (α - 2 * Real.sqrt ε) (β - 2 * Real.sqrt ε) where
  mass := by
    have hpt : ∀ i ∈ s,
        hitProb φ i - 2 * ‖φ i‖ * ‖(ψ - φ) i‖ ≤ hitProb ψ i := by
      intro i _
      have := amp_sq_sub_bound (φ i) ((ψ - φ) i)
      simpa [hitProb, coord_add_diff ψ φ i] using this
    have hsum := Finset.sum_le_sum hpt
    have hsum' :
        ∑ i ∈ s, hitProb φ i - 2 * ∑ i ∈ s, ‖φ i‖ * ‖(ψ - φ) i‖ ≤
          ∑ i ∈ s, hitProb ψ i := by
      have hdecomp :
          ∑ i ∈ s, (hitProb φ i - 2 * ‖φ i‖ * ‖(ψ - φ) i‖) =
            ∑ i ∈ s, hitProb φ i - ∑ i ∈ s, 2 * ‖φ i‖ * ‖(ψ - φ) i‖ :=
        Finset.sum_sub_distrib (fun i => hitProb φ i)
          (fun i => 2 * ‖φ i‖ * ‖(ψ - φ) i‖)
      have htwo :
          ∑ i ∈ s, 2 * ‖φ i‖ * ‖(ψ - φ) i‖ =
            2 * ∑ i ∈ s, ‖φ i‖ * ‖(ψ - φ) i‖ := by
        simp [mul_assoc, Finset.mul_sum]
      rwa [hdecomp, htwo] at hsum
    have hCS := sum_amp_cs (s := s) φ ψ ε hφ hε hdist
    nlinarith [hsum', hs.mass, hCS]
  pointwise := by
    intro j hj
    have hpt := amp_sq_sub_bound (φ j) ((ψ - φ) j)
    have hφj := norm_coord_le_one hφ j
    have hd : ‖(ψ - φ) j‖ ≤ Real.sqrt ε :=
      (coord_diff_le_dist ψ φ j).trans <|
        (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg ε)).1
          (by simpa [Real.sq_sqrt hε] using hdist)
    have hψj : hitProb φ j - 2 * ‖φ j‖ * ‖(ψ - φ) j‖ ≤ hitProb ψ j := by
      simpa [hitProb, coord_add_diff ψ φ j] using hpt
    have hmul : ‖φ j‖ * ‖(ψ - φ) j‖ ≤ Real.sqrt ε :=
      (mul_le_of_le_one_left (norm_nonneg _) hφj).trans hd
    nlinarith [hψj, hs.pointwise j hj, hmul]

lemma coord_smul (c : ℂ) (ψ : EuclideanSpace ℂ ι) (j : ι) :
    (c • ψ) j = c * ψ j := by
  simp [smul_eq_mul]

lemma coord_sum {κ : Type*} [Fintype κ] (f : κ → EuclideanSpace ℂ ι) (j : ι) :
    (∑ k, f k) j = ∑ k, f k j := by
  simp [WithLp.ofLp_sum]

lemma coord_linear_combination {κ : Type*} [Fintype κ]
    (coeff : κ → ℂ) (krylov : κ → EuclideanSpace ℂ ι) (j : ι) :
    (∑ k, coeff k • krylov k) j = ∑ k, coeff k * krylov k j := by
  rw [coord_sum]
  simp

/-- **Lemma 3.** Each important bitstring has a nontrivial Born probability
on at least one Krylov vector. -/
theorem lemma3_krylov_hit {κ : Type*} [Fintype κ]
    (coeff : κ → ℂ) (krylov : κ → EuclideanSpace ℂ ι)
    (γ : ℂ) (β : ℝ) (j : ι)
    (hd : 0 < Fintype.card κ)
    (hcoeff : ∀ k, ‖coeff k‖ * ‖γ‖ ≤ 1)
    (hβnn : 0 ≤ β)
    (hβ : β ≤ hitProb (∑ k, coeff k • krylov k) j) :
    ∃ k, ‖γ‖ ^ 2 * β / (Fintype.card κ : ℝ) ^ 2 ≤ hitProb (krylov k) j := by
  set φ := ∑ k, coeff k • krylov k
  have hcoord : φ j = ∑ k, coeff k * krylov k j := coord_linear_combination coeff krylov j
  have htri : ‖φ j‖ ≤ ∑ k, ‖coeff k‖ * ‖krylov k j‖ := by
    simpa [hcoord, norm_mul] using
      (norm_sum_le (s := Finset.univ) (f := fun k => coeff k * krylov k j))
  have hscale : ∑ k, ‖coeff k‖ * ‖γ‖ * ‖krylov k j‖ ≤ ∑ k, ‖krylov k j‖ := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hk := hcoeff k
    have hnn : 0 ≤ ‖krylov k j‖ := norm_nonneg _
    nlinarith [norm_nonneg (coeff k), norm_nonneg γ, hnn, hk]
  have hfactor :
      ‖γ‖ * ∑ k, ‖coeff k‖ * ‖krylov k j‖
        = ∑ k, ‖coeff k‖ * ‖γ‖ * ‖krylov k j‖ := by
    simp [Finset.mul_sum, mul_assoc, mul_comm]
  have hsum_c : ‖γ‖ * ‖φ j‖ ≤ ∑ k, ‖krylov k j‖ := by
    have := mul_le_mul_of_nonneg_left htri (norm_nonneg γ)
    linarith [this, hfactor, hscale]
  have hsqrt : Real.sqrt β ≤ ‖φ j‖ := by
    have hsq : Real.sqrt β ^ 2 ≤ ‖φ j‖ ^ 2 := by
      simpa [Real.sq_sqrt hβnn, hitProb, φ] using hβ
    exact (sq_le_sq₀ (Real.sqrt_nonneg β) (norm_nonneg _)).1 hsq
  have hsum : ‖γ‖ * Real.sqrt β ≤ ∑ k, ‖krylov k j‖ :=
    le_trans (mul_le_mul_of_nonneg_left hsqrt (norm_nonneg γ)) hsum_c
  have hne : Finset.univ.Nonempty :=
    Finset.univ_nonempty_iff.2 (Fintype.card_pos_iff.mp hd)
  obtain ⟨kmax, hkmax_mem, hkmax⟩ :=
    Finset.exists_max_image (s := Finset.univ) (fun k : κ => ‖krylov k j‖) hne
  have hsum_le :
      ∑ k, ‖krylov k j‖ ≤ (Fintype.card κ : ℝ) * ‖krylov kmax j‖ := by
    have hle : ∀ k ∈ Finset.univ, ‖krylov k j‖ ≤ ‖krylov kmax j‖ :=
      fun k hk => hkmax k hk
    simpa [nsmul_eq_mul, Finset.card_univ] using
      Finset.sum_le_card_nsmul Finset.univ (fun k => ‖krylov k j‖)
        (‖krylov kmax j‖) hle
  have hcard : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.mpr hd
  have hmax : ‖γ‖ * Real.sqrt β / (Fintype.card κ : ℝ) ≤ ‖krylov kmax j‖ :=
    (div_le_iff₀ hcard).2 (hsum.trans (by simpa [mul_comm] using hsum_le))
  refine ⟨kmax, ?_⟩
  have hsq := pow_le_pow_left₀ (by positivity) hmax 2
  have hlhs :
      (‖γ‖ * Real.sqrt β / (Fintype.card κ : ℝ)) ^ 2 =
        ‖γ‖ ^ 2 * β / (Fintype.card κ : ℝ) ^ 2 := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hβnn]
  simpa [hitProb, hlhs] using hsq

/-- Restriction of a state to a computational-basis subset. -/
noncomputable def restrict (ψ : EuclideanSpace ℂ ι) (s : Finset ι) :
    EuclideanSpace ℂ ι :=
  ∑ i ∈ s, EuclideanSpace.single i (ψ i)

lemma restrict_apply (ψ : EuclideanSpace ℂ ι) (s : Finset ι) (j : ι) :
    restrict ψ s j = if j ∈ s then ψ j else 0 := by
  unfold restrict
  have hsum :
      (∑ i ∈ s, EuclideanSpace.single i (ψ i)).ofLp =
        ∑ i ∈ s, (EuclideanSpace.single i (ψ i)).ofLp :=
    map_sum (WithLp.addEquiv (2 : ENNReal) (ι → ℂ)) _ _
  change (∑ i ∈ s, EuclideanSpace.single i (ψ i)).ofLp j = _
  rw [hsum]
  have hpt :
      (∑ i ∈ s, (EuclideanSpace.single i (ψ i)).ofLp) j =
        ∑ i ∈ s, (EuclideanSpace.single i (ψ i)).ofLp j :=
    map_sum (Pi.evalAddMonoidHom (fun _ : ι => ℂ) j)
      (fun i => (EuclideanSpace.single i (ψ i)).ofLp) s
  rw [hpt]
  have hsingle : ∀ i,
      (EuclideanSpace.single i (ψ i)).ofLp j = if i = j then ψ i else 0 := by
    intro i
    rw [PiLp.single_apply]
    simp [eq_comm]
  simp_rw [hsingle]
  exact Finset.sum_ite_eq' s j (fun i => ψ i)

lemma restrict_norm_sq (ψ : EuclideanSpace ℂ ι) (s : Finset ι) :
    ‖restrict ψ s‖ ^ 2 = supportMass ψ s := by
  rw [EuclideanSpace.norm_sq_eq]
  have hite : ∀ j, ‖restrict ψ s j‖ ^ 2 =
      if j ∈ s then hitProb ψ j else 0 := by
    intro j
    rw [restrict_apply]
    split_ifs <;> simp [hitProb]
  simp_rw [hite]
  simp [supportMass, Finset.sum_ite_mem]

lemma restrict_inner (ψ : EuclideanSpace ℂ ι) (s : Finset ι) :
    inner ℂ (restrict ψ s) ψ = (supportMass ψ s : ℂ) := by
  rw [PiLp.inner_apply]
  have hite : ∀ j, inner ℂ (restrict ψ s j) (ψ j) =
      if j ∈ s then (hitProb ψ j : ℂ) else 0 := by
    intro j
    rw [restrict_apply]
    split_ifs with hj
    · simp [hitProb]
    · simp
  simp_rw [hite]
  simp [supportMass, Finset.sum_ite_mem, Complex.ofReal_sum]

/-- Normalized truncation of a state onto a computational-basis subset. -/
noncomputable def truncated (ψ : EuclideanSpace ℂ ι) (s : Finset ι) :
    EuclideanSpace ℂ ι :=
  (Real.sqrt (supportMass ψ s) : ℂ)⁻¹ • restrict ψ s

lemma truncated_normalized {ψ : EuclideanSpace ℂ ι} {s : Finset ι}
    (hpos : 0 < supportMass ψ s) :
    ‖truncated ψ s‖ = 1 := by
  have hsqrtpos : 0 < Real.sqrt (supportMass ψ s) := Real.sqrt_pos.mpr hpos
  have hnorm : ‖restrict ψ s‖ = Real.sqrt (supportMass ψ s) := by
    have hsq := restrict_norm_sq ψ s
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  rw [truncated, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrtpos, hnorm]
  exact inv_mul_cancel₀ hsqrtpos.ne'

lemma truncated_overlap {ψ : EuclideanSpace ℂ ι} {s : Finset ι}
    (hpos : 0 < supportMass ψ s) :
    inner ℂ (truncated ψ s) ψ = (Real.sqrt (supportMass ψ s) : ℂ) := by
  have hsqrtpos : 0 < Real.sqrt (supportMass ψ s) := Real.sqrt_pos.mpr hpos
  rw [truncated, inner_smul_left, map_inv₀, Complex.conj_ofReal, restrict_inner]
  have hne : (Real.sqrt (supportMass ψ s) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hsqrtpos.ne'
  rw [inv_mul_eq_iff_eq_mul₀ hne]
  norm_cast
  rw [← pow_two, Real.sq_sqrt hpos.le]

lemma truncated_overlap_re {ψ : EuclideanSpace ℂ ι} {s : Finset ι}
    (hpos : 0 < supportMass ψ s) :
    (inner ℂ (truncated ψ s) ψ).re = Real.sqrt (supportMass ψ s) := by
  rw [truncated_overlap hpos]
  simp

/-- **Lemma 5.** The normalized truncation of a sparse ground state has energy
within the paper's `√8 ‖H‖ √(1-√α)` bound. -/
theorem lemma5_truncated_energy
    (H : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ ι) (s : Finset ι) (α β : ℝ)
    (hφ : ‖φ‖ = 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hs : Sparse φ s α β) :
    abs ((inner ℂ (truncated φ s) (H (truncated φ s))).re -
      (inner ℂ φ (H φ)).re) ≤
      Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) := by
  have hmass : 0 < supportMass φ s := sparse_mass_pos hα0 hs
  have htrunc : ‖truncated φ s‖ = 1 := truncated_normalized hmass
  refine truncated_energy_bound H (truncated φ s) φ α htrunc hφ hα1 ?_
  have re_eq : RCLike.re (inner ℂ (truncated φ s) φ) = Real.sqrt (supportMass φ s) :=
    truncated_overlap_re hmass
  have : Real.sqrt α ≤ Real.sqrt (supportMass φ s) := Real.sqrt_le_sqrt hs.mass
  rwa [re_eq]

end SKQD
