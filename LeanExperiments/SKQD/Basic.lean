import Mathlib

/-!
Hilbert-space ingredients of the SKQD proof (arXiv:2501.09702v1, Appendix B).
-/

namespace SKQD

open Complex
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Ground-state eigenvector with a spectral gap `ΔE₁`. -/
structure GroundStateGap (H : E →L[ℂ] E) (φ₀ : E) (E₀ ΔE₁ : ℝ) : Prop where
  normalized : ‖φ₀‖ = 1
  eigen : H φ₀ = (E₀ : ℂ) • φ₀
  symmetric : (H : E →ₗ[ℂ] E).IsSymmetric
  gap_pos : 0 < ΔE₁
  gap : ∀ ψ, inner ℂ φ₀ ψ = 0 → ‖ψ‖ = 1 →
    E₀ + ΔE₁ ≤ (inner ℂ ψ (H ψ)).re

/-- Expectation values of a bounded operator are Lipschitz on normalized
vectors (Equation (62)). Self-adjointness is not required. -/
theorem energy_expectation_lipschitz
    (H : E →L[ℂ] E) (ψ φ : E)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    abs ((inner ℂ ψ (H ψ)).re - (inner ℂ φ (H φ)).re) ≤
      2 * ‖H‖ * ‖ψ - φ‖ := by
  have hid :
      inner ℂ ψ (H ψ) - inner ℂ φ (H φ) =
        inner ℂ ψ (H (ψ - φ)) + inner ℂ (ψ - φ) (H φ) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    abel
  have hfirst :
      ‖inner ℂ ψ (H (ψ - φ))‖ ≤ ‖ψ‖ * (‖H‖ * ‖ψ - φ‖) :=
    (norm_inner_le_norm _ _).trans <|
      mul_le_mul_of_nonneg_left (H.le_opNorm (ψ - φ)) (norm_nonneg ψ)
  have hsecond :
      ‖inner ℂ (ψ - φ) (H φ)‖ ≤ ‖ψ - φ‖ * (‖H‖ * ‖φ‖) :=
    (norm_inner_le_norm _ _).trans <|
      mul_le_mul_of_nonneg_left (H.le_opNorm φ) (norm_nonneg (ψ - φ))
  calc
    abs ((inner ℂ ψ (H ψ)).re - (inner ℂ φ (H φ)).re)
        = abs ((inner ℂ ψ (H ψ) - inner ℂ φ (H φ)).re) := rfl
    _ ≤ ‖inner ℂ ψ (H ψ) - inner ℂ φ (H φ)‖ := abs_re_le_norm _
    _ = ‖inner ℂ ψ (H (ψ - φ)) + inner ℂ (ψ - φ) (H φ)‖ := by rw [hid]
    _ ≤ ‖inner ℂ ψ (H (ψ - φ))‖ + ‖inner ℂ (ψ - φ) (H φ)‖ := norm_add_le _ _
    _ ≤ ‖ψ‖ * (‖H‖ * ‖ψ - φ‖) + ‖ψ - φ‖ * (‖H‖ * ‖φ‖) :=
      add_le_add hfirst hsecond
    _ = 2 * ‖H‖ * ‖ψ - φ‖ := by
      rw [hψ, hφ]
      ring

/-- Equation (60) as a geometric estimate: real overlap at least `√α`
implies the paper's energy error bound. -/
theorem truncated_energy_bound
    (H : E →L[ℂ] E) (ψ φ : E) (α : ℝ)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hα₁ : α ≤ 1)
    (hoverlap : Real.sqrt α ≤ RCLike.re (inner ℂ ψ φ)) :
    abs ((inner ℂ ψ (H ψ)).re - (inner ℂ φ (H φ)).re) ≤
      Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) := by
  have hsqrtα_le : Real.sqrt α ≤ 1 := (Real.sqrt_le_one).2 hα₁
  have hrad : 0 ≤ 2 * (1 - Real.sqrt α) := by positivity
  have hexpand := norm_sub_mul_self (𝕜 := ℂ) ψ φ
  have hdist_sq :
      ‖ψ - φ‖ * ‖ψ - φ‖ ≤ 2 * (1 - Real.sqrt α) := by
    rw [hψ, hφ] at hexpand
    nlinarith
  have hdist :
      ‖ψ - φ‖ ≤ Real.sqrt (2 * (1 - Real.sqrt α)) := by
    have hsqrt_sq := Real.sq_sqrt hrad
    nlinarith [norm_nonneg (ψ - φ), Real.sqrt_nonneg (2 * (1 - Real.sqrt α))]
  calc
    abs ((inner ℂ ψ (H ψ)).re - (inner ℂ φ (H φ)).re)
        ≤ 2 * ‖H‖ * ‖ψ - φ‖ :=
      energy_expectation_lipschitz H ψ φ hψ hφ
    _ ≤ 2 * ‖H‖ * Real.sqrt (2 * (1 - Real.sqrt α)) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = Real.sqrt 8 * ‖H‖ * Real.sqrt (1 - Real.sqrt α) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
      have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
        rw [show (8 : ℝ) = 4 * 2 by norm_num,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
        norm_num
      rw [hsqrt8]
      ring

lemma eq_coe_re_of_im_zero {z : ℂ} (him : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [him])

lemma re_inner_comm (x y : E) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  rw [← inner_conj_symm x y, conj_re]

theorem dist_sq_of_normalized {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ‖ψ - φ‖ ^ 2 = 2 - 2 * (inner ℂ ψ φ).re := by
  have h := norm_sub_mul_self (𝕜 := ℂ) ψ φ
  rw [hψ, hφ] at h
  have : RCLike.re (inner ℂ ψ φ) = (inner ℂ ψ φ).re := rfl
  nlinarith [h, this]

lemma inner_H_eq_inner_eigen
    (H : E →L[ℂ] E) (φ₀ δ : E) (E₀ : ℝ)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric)
    (heig : H φ₀ = (E₀ : ℂ) • φ₀)
    (hφδ : inner ℂ φ₀ δ = 0) :
    inner ℂ φ₀ (H δ) = 0 := by
  have h := hsym φ₀ δ
  -- `h : ⟪H φ₀, δ⟫ = ⟪φ₀, H δ⟫` after unfolding the coercion
  change inner ℂ (H φ₀) δ = inner ℂ φ₀ (H δ) at h
  rw [← h, heig, inner_smul_left, hφδ]
  simp

lemma eigen_term
    (φ₀ : E) (E₀ : ℝ) (χ : ℂ) (hφ : ‖φ₀‖ = 1) :
    inner ℂ (χ • φ₀) ((χ * (E₀ : ℂ)) • φ₀) = (‖χ‖ ^ 2 : ℂ) * (E₀ : ℂ) := by
  have hφ2 : inner ℂ φ₀ φ₀ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hφ]
    simp
  rw [inner_smul_left, inner_smul_right, hφ2, mul_one, ← mul_assoc, mul_comm (conj χ),
    mul_conj, Complex.normSq_eq_norm_sq]
  simp [pow_two]

lemma re_coe_mul_re (a b : ℝ) : ((a : ℂ) * (b : ℂ)).re = a * b := by simp

lemma re_coe_mul (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
  simp [mul_re]

theorem re_energy_decomposition
    (H : E →L[ℂ] E) (φ₀ : E) (E₀ : ℝ) (χ : ℂ) (δ : E)
    (hφ : ‖φ₀‖ = 1)
    (hsym : (H : E →ₗ[ℂ] E).IsSymmetric)
    (heig : H φ₀ = (E₀ : ℂ) • φ₀)
    (hφδ : inner ℂ φ₀ δ = 0) :
    (inner ℂ (χ • φ₀ + δ) (H (χ • φ₀ + δ))).re =
      ‖χ‖ ^ 2 * E₀ + (inner ℂ δ (H δ)).re := by
  have hH : H (χ • φ₀ + δ) = (χ * (E₀ : ℂ)) • φ₀ + H δ := by
    rw [map_add, map_smul, heig]
    module
  have hL : inner ℂ (χ • φ₀) (H δ) = 0 := by
    rw [inner_smul_left, inner_H_eq_inner_eigen H φ₀ δ E₀ hsym heig hφδ, mul_zero]
  have hR : inner ℂ δ ((χ * (E₀ : ℂ)) • φ₀) = 0 := by
    rw [inner_smul_right, inner_eq_zero_symm.mp hφδ, mul_zero]
  rw [hH, inner_add_left]
  have hsum :
      inner ℂ (χ • φ₀) ((χ * (E₀ : ℂ)) • φ₀ + H δ) +
          inner ℂ δ ((χ * (E₀ : ℂ)) • φ₀ + H δ) =
        inner ℂ (χ • φ₀) ((χ * (E₀ : ℂ)) • φ₀) + inner ℂ δ (H δ) := by
    rw [inner_add_right, inner_add_right, hL, hR, add_zero, zero_add]
  rw [hsum, eigen_term φ₀ E₀ χ hφ, add_re]
  have : ((‖χ‖ : ℂ) ^ 2 * (E₀ : ℂ)).re = ‖χ‖ ^ 2 * E₀ := by
    simp [pow_two, mul_re]
  exact congrArg (· + (inner ℂ δ (H δ)).re) this

theorem remainder_orthogonal
    (φ₀ ψ : E) (hφ : ‖φ₀‖ = 1) :
    inner ℂ φ₀ (ψ - inner ℂ φ₀ ψ • φ₀) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hφ]
  simp

theorem remainder_pythagoras
    (φ₀ ψ : E) (hφ : ‖φ₀‖ = 1) :
    ‖ψ‖ ^ 2 = ‖inner ℂ φ₀ ψ‖ ^ 2 + ‖ψ - inner ℂ φ₀ ψ • φ₀‖ ^ 2 := by
  set χ := inner ℂ φ₀ ψ
  set δ := ψ - χ • φ₀
  have horth := remainder_orthogonal φ₀ ψ hφ
  have hdecomp : ψ = χ • φ₀ + δ := by simp [δ]
  have hinner : inner ℂ (χ • φ₀) δ = 0 := by
    rw [inner_smul_left, horth, mul_zero]
  have hmul := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (χ • φ₀) δ hinner
  have hχφ : ‖χ • φ₀‖ = ‖χ‖ := by simp [norm_smul, hφ]
  have := congrArg (fun t => t ^ 2) (Eq.refl ‖ψ‖)
  -- convert the product identity into squares
  have hsq : ‖ψ‖ * ‖ψ‖ = ‖χ‖ * ‖χ‖ + ‖δ‖ * ‖δ‖ := by
    simpa [hdecomp, hχφ, hφ] using hmul
  simpa [pow_two, χ, δ] using hsq

lemma orthogonal_energy_gap
    (H : E →L[ℂ] E) (φ₀ : E) (E₀ ΔE₁ : ℝ) (δ : E)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hφδ : inner ℂ φ₀ δ = 0) :
    ‖δ‖ ^ 2 * (E₀ + ΔE₁) ≤ (inner ℂ δ (H δ)).re := by
  by_cases hδ0 : δ = 0
  · simp [hδ0]
  generalize hR : ‖δ‖ = r
  have hδpos : 0 < r := hR ▸ norm_pos_iff.mpr hδ0
  set u : E := (r : ℂ)⁻¹ • δ
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, ← hR]
    exact inv_mul_cancel₀ (norm_pos_iff.mpr hδ0).ne'
  have hu_orth : inner ℂ φ₀ u = 0 := by
    rw [inner_smul_right, hφδ, mul_zero]
  have hgapu := hg.gap u hu_orth hu_norm
  have hδu : (r : ℂ) • u = δ := by
    simp [u, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hδpos.ne')]
  have henergy : inner ℂ δ (H δ) = ((r ^ 2 : ℝ) : ℂ) * inner ℂ u (H u) := by
    rw [← hδu, map_smul, inner_smul_left, inner_smul_right, conj_ofReal, ← mul_assoc,
      ← pow_two, ← ofReal_pow]
  have hre : (inner ℂ δ (H δ)).re = r ^ 2 * (inner ℂ u (H u)).re := by
    rw [henergy]
    exact re_coe_mul (r ^ 2) _
  have : r ^ 2 * (E₀ + ΔE₁) ≤ (inner ℂ δ (H δ)).re := by
    nlinarith [hre, hgapu, sq_nonneg r]
  simpa [hR] using this

/-- **Lemma 1.** A normalized state whose energy error is at most `ε`, and
whose overlap with the ground state is real and nonnegative, is close to
the ground state in 2-norm. -/
theorem lemma1_state_error
    (H : E →L[ℂ] E) (φ₀ ψ : E) (E₀ ΔE₁ ε : ℝ)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hψ : ‖ψ‖ = 1)
    (hphase : (inner ℂ φ₀ ψ).im = 0)
    (hpos : 0 ≤ (inner ℂ φ₀ ψ).re)
    (_hε : 0 ≤ ε) (hεgap : ε ≤ ΔE₁)
    (herr : (inner ℂ ψ (H ψ)).re - E₀ ≤ ε) :
    ‖ψ - φ₀‖ ^ 2 ≤ 2 * (1 - Real.sqrt (1 - ε / ΔE₁)) := by
  set χ : ℂ := inner ℂ φ₀ ψ
  set δ : E := ψ - χ • φ₀
  have hφδ : inner ℂ φ₀ δ = 0 := remainder_orthogonal φ₀ ψ hg.normalized
  have hpy : ‖ψ‖ ^ 2 = ‖χ‖ ^ 2 + ‖δ‖ ^ 2 := remainder_pythagoras φ₀ ψ hg.normalized
  have hδsq : ‖δ‖ ^ 2 = 1 - ‖χ‖ ^ 2 := by nlinarith [hpy, hψ, sq_nonneg ‖χ‖]
  have hdecomp : ψ = χ • φ₀ + δ := by simp [δ]
  have hE := re_energy_decomposition H φ₀ E₀ χ δ hg.normalized hg.symmetric hg.eigen hφδ
  have herr' : (inner ℂ δ (H δ)).re - ‖δ‖ ^ 2 * E₀ ≤ ε := by
    have : (inner ℂ ψ (H ψ)).re = ‖χ‖ ^ 2 * E₀ + (inner ℂ δ (H δ)).re := by
      simpa [hdecomp] using hE
    have hsum : ‖χ‖ ^ 2 + ‖δ‖ ^ 2 = 1 := by nlinarith [hδsq]
    calc
      (inner ℂ δ (H δ)).re - ‖δ‖ ^ 2 * E₀
          = (inner ℂ δ (H δ)).re - (1 - ‖χ‖ ^ 2) * E₀ := by rw [hδsq]
      _ = ‖χ‖ ^ 2 * E₀ + (inner ℂ δ (H δ)).re - E₀ := by ring
      _ = (inner ℂ ψ (H ψ)).re - E₀ := by rw [this]
      _ ≤ ε := herr
  have hgapδ := orthogonal_energy_gap H φ₀ E₀ ΔE₁ δ hg hφδ
  have hδle : ‖δ‖ ^ 2 ≤ ε / ΔE₁ := by
    have : ‖δ‖ ^ 2 * ΔE₁ ≤ ε := by nlinarith [herr', hgapδ]
    exact (le_div_iff₀ hg.gap_pos).2 this
  have hχsq : 1 - ε / ΔE₁ ≤ ‖χ‖ ^ 2 := by nlinarith [hδsq, hδle]
  have hχre : ‖χ‖ = χ.re := by
    calc
      ‖χ‖ = ‖(χ.re : ℂ)‖ := congrArg norm (eq_coe_re_of_im_zero hphase)
      _ = |χ.re| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = χ.re := abs_of_nonneg hpos
  have hsqrt : Real.sqrt (1 - ε / ΔE₁) ≤ χ.re := by
    have hnn : 0 ≤ 1 - ε / ΔE₁ :=
      sub_nonneg.2 (div_le_one_of_le₀ hεgap hg.gap_pos.le)
    have := (Real.sqrt_le_sqrt_iff (sq_nonneg ‖χ‖)).2 hχsq
    rwa [Real.sqrt_sq (by simp [hχre, hpos]), hχre] at this
  have hdist : ‖ψ - φ₀‖ ^ 2 = 2 - 2 * χ.re := by
    have := dist_sq_of_normalized hψ hg.normalized
    rwa [re_inner_comm] at this
  nlinarith [hdist, hsqrt]

lemma ground_rayleigh
    (H : E →L[ℂ] E) (φ₀ : E) (E₀ ΔE₁ : ℝ)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁) :
    (inner ℂ φ₀ (H φ₀)).re = E₀ := by
  rw [hg.eigen, inner_smul_right, inner_self_eq_norm_sq_to_K, hg.normalized]
  simp

/-- Variational principle: every unit vector has energy at least `E₀`. -/
theorem energy_ge_ground
    (H : E →L[ℂ] E) (φ₀ ψ : E) (E₀ ΔE₁ : ℝ)
    (hg : GroundStateGap H φ₀ E₀ ΔE₁)
    (hψ : ‖ψ‖ = 1) :
    E₀ ≤ (inner ℂ ψ (H ψ)).re := by
  set χ : ℂ := inner ℂ φ₀ ψ
  set δ : E := ψ - χ • φ₀
  have hφδ : inner ℂ φ₀ δ = 0 := remainder_orthogonal φ₀ ψ hg.normalized
  have hpy : ‖ψ‖ ^ 2 = ‖χ‖ ^ 2 + ‖δ‖ ^ 2 := remainder_pythagoras φ₀ ψ hg.normalized
  have hdecomp : ψ = χ • φ₀ + δ := by simp [δ]
  have hE := re_energy_decomposition H φ₀ E₀ χ δ hg.normalized hg.symmetric hg.eigen hφδ
  have hgapδ := orthogonal_energy_gap H φ₀ E₀ ΔE₁ δ hg hφδ
  have : (inner ℂ ψ (H ψ)).re = ‖χ‖ ^ 2 * E₀ + (inner ℂ δ (H δ)).re := by
    simpa [hdecomp] using hE
  have hpy' : ‖χ‖ ^ 2 + ‖δ‖ ^ 2 = 1 := by nlinarith [hpy, hψ]
  have hsplit : ‖χ‖ ^ 2 * E₀ + ‖δ‖ ^ 2 * E₀ = E₀ := by
    calc
      ‖χ‖ ^ 2 * E₀ + ‖δ‖ ^ 2 * E₀ = (‖χ‖ ^ 2 + ‖δ‖ ^ 2) * E₀ := by ring
      _ = E₀ := by rw [hpy', one_mul]
  have hδE : ‖δ‖ ^ 2 * E₀ ≤ (inner ℂ δ (H δ)).re := by
    have : 0 ≤ ‖δ‖ ^ 2 * ΔE₁ := mul_nonneg (sq_nonneg _) hg.gap_pos.le
    nlinarith [hgapδ]
  calc
    E₀ = ‖χ‖ ^ 2 * E₀ + ‖δ‖ ^ 2 * E₀ := hsplit.symm
    _ ≤ ‖χ‖ ^ 2 * E₀ + (inner ℂ δ (H δ)).re := by gcongr
    _ = (inner ℂ ψ (H ψ)).re := this.symm

/-- Equation (59): the union-bound expression is at most its exponential relaxation. -/
theorem failure_bound_le_exp (L : ℕ) (M : ℕ) (p : ℝ) (hp : p ≤ 1) :
    (L : ℝ) * (1 - p) ^ M ≤ (L : ℝ) * Real.exp (-(M : ℝ) * p) := by
  have hbase : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have hpow : (1 - p) ^ M ≤ (Real.exp (-p)) ^ M := by
    gcongr
  calc
    (L : ℝ) * (1 - p) ^ M ≤ (L : ℝ) * (Real.exp (-p)) ^ M :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg L)
    _ = (L : ℝ) * Real.exp (-(M : ℝ) * p) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

theorem exp_failure_le_eta
    (L M : ℕ) (p η : ℝ)
    (hL : 0 < L) (hη : 0 < η)
    (hcount : Real.log ((L : ℝ) / η) ≤ (M : ℝ) * p) :
    (L : ℝ) * Real.exp (-(M : ℝ) * p) ≤ η := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hratio : 0 < (L : ℝ) / η := div_pos hLr hη
  have hexp :
      Real.exp (-(M : ℝ) * p) ≤ Real.exp (-Real.log ((L : ℝ) / η)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    (L : ℝ) * Real.exp (-(M : ℝ) * p)
        ≤ (L : ℝ) * Real.exp (-Real.log ((L : ℝ) / η)) :=
      mul_le_mul_of_nonneg_left hexp hLr.le
    _ = η := by
      rw [Real.exp_neg, Real.exp_log hratio]
      field_simp

/-- **Lemma 4** (analytic form). Enough independent samples make the
union-bound failure probability at most `η`. -/
theorem lemma4_sampling_failure_le_eta
    (L M : ℕ) (p η failureProbability : ℝ)
    (hL : 0 < L) (hη : 0 < η) (hp : p ≤ 1)
    (hunion : failureProbability ≤ (L : ℝ) * (1 - p) ^ M)
    (hcount : Real.log ((L : ℝ) / η) ≤ (M : ℝ) * p) :
    failureProbability ≤ η :=
  hunion.trans <|
    (failure_bound_le_exp L M p hp).trans <|
      exp_failure_le_eta L M p η hL hη hcount

theorem paper_sample_threshold
    (L M d : ℕ) (γsq β η : ℝ)
    (hd : 0 < d) (hγ : 0 < γsq) (hβ : 0 < β)
    (hM :
      ((d : ℝ) ^ 2 * Real.log ((L : ℝ) / η)) / (γsq * β) ≤ (M : ℝ)) :
    Real.log ((L : ℝ) / η) ≤
      (M : ℝ) * (γsq * β / (d : ℝ) ^ 2) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 ≤ γsq * β / (d : ℝ) ^ 2 := by positivity
  calc
    Real.log ((L : ℝ) / η) =
        (((d : ℝ) ^ 2 * Real.log ((L : ℝ) / η)) / (γsq * β)) *
          (γsq * β / (d : ℝ) ^ 2) := by
      field_simp
    _ ≤ (M : ℝ) * (γsq * β / (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hM hp

theorem paper_sampling_failure_le_eta
    (L M d : ℕ) (γsq β η failureProbability : ℝ)
    (hL : 0 < L) (hd : 0 < d) (hη : 0 < η)
    (hγ : 0 < γsq) (hβ : 0 < β)
    (hp_le_one : γsq * β / (d : ℝ) ^ 2 ≤ 1)
    (hunion :
      failureProbability ≤
        (L : ℝ) * (1 - γsq * β / (d : ℝ) ^ 2) ^ M)
    (hM :
      ((d : ℝ) ^ 2 * Real.log ((L : ℝ) / η)) / (γsq * β) ≤ (M : ℝ)) :
    failureProbability ≤ η := by
  apply lemma4_sampling_failure_le_eta
      L M (γsq * β / (d : ℝ) ^ 2) η failureProbability
      hL hη hp_le_one hunion
  exact paper_sample_threshold L M d γsq β η hd hγ hβ hM

end SKQD
