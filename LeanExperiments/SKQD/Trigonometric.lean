import LeanExperiments.SKQD.Filter

/-! Finite frequency support of polynomial filters. -/
namespace SKQD

variable {X : Type*}

def trigSpan (mode : ℤ → X → ℂ) (n : ℕ) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ (mode '' Set.Icc (-(n : ℤ)) n)

lemma mode_mem_trigSpan (mode : ℤ → X → ℂ) {n : ℕ} {k : ℤ}
    (hk : -(n : ℤ) ≤ k ∧ k ≤ n) : mode k ∈ trigSpan mode n :=
  Submodule.subset_span ⟨k, hk, rfl⟩

lemma trigSpan_mono (mode : ℤ → X → ℂ) {m n : ℕ} (hmn : m ≤ n) :
    trigSpan mode m ≤ trigSpan mode n := by
  apply Submodule.span_mono
  rintro _ ⟨k, hk, rfl⟩
  have hmn' : (m : ℤ) ≤ n := by exact_mod_cast hmn
  obtain ⟨hk1, hk2⟩ := hk
  exact ⟨k, ⟨by omega, by omega⟩, rfl⟩

lemma trigSpan_mul (mode : ℤ → X → ℂ)
    (hadd : ∀ i j, mode (i + j) = mode i * mode j)
    {m n : ℕ} {f g : X → ℂ} (hf : f ∈ trigSpan mode m) (hg : g ∈ trigSpan mode n) :
    f * g ∈ trigSpan mode (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, hi, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨j, hj, rfl⟩ := hg
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨hj1, hj2⟩ := hj
      rw [← hadd]
      apply mode_mem_trigSpan
      push_cast
      constructor <;> omega
    | zero => simpa only [mul_zero] using (trigSpan mode (m + n)).zero_mem
    | add g h _ _ ihg ihh =>
      simpa only [mul_add] using (trigSpan mode (m + n)).add_mem ihg ihh
    | smul c g _ ih =>
      simpa only [mul_smul_comm] using (trigSpan mode (m + n)).smul_mem c ih
  | zero => simpa only [zero_mul] using (trigSpan mode (m + n)).zero_mem
  | add f h _ _ ihf ihh =>
    simpa only [add_mul] using (trigSpan mode (m + n)).add_mem ihf ihh
  | smul c f _ ih =>
    simpa only [smul_mul_assoc] using (trigSpan mode (m + n)).smul_mem c ih

lemma trigSpan_one (mode : ℤ → X → ℂ) (hzero : mode 0 = 1) (n : ℕ) :
    (1 : X → ℂ) ∈ trigSpan mode n := by
  rw [← hzero]
  apply mode_mem_trigSpan
  constructor <;> omega

/-- Evaluating a degree-`m` Chebyshev polynomial on an affine cosine
expression introduces no frequencies outside `[-m,m]`. -/
theorem chebyshev_mem_trigSpan (mode : ℤ → X → ℂ)
    (hzero : mode 0 = 1) (hadd : ∀ i j, mode (i + j) = mode i * mode j)
    (z : X → ℂ) (hz : z ∈ trigSpan mode 1) (m : ℕ) :
    (fun x => (Polynomial.Chebyshev.T ℂ (m : ℤ)).eval (z x)) ∈ trigSpan mode m := by
  induction m using Nat.twoStepInduction with
  | zero =>
    convert trigSpan_one mode hzero 0 using 1
    ext x
    simp
  | one => simpa using hz
  | more m hm hm1 =>
    have hmul := trigSpan_mul mode hadd hz hm1
    have hm' := trigSpan_mono mode (show m ≤ m + 2 by omega) hm
    have heq : (fun x => (Polynomial.Chebyshev.T ℂ ((m + 2 : ℕ) : ℤ)).eval (z x)) =
        (2 : ℂ) • (z * fun x => (Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ)).eval (z x)) -
          (fun x => (Polynomial.Chebyshev.T ℂ (m : ℤ)).eval (z x)) := by
      ext x
      simp [Nat.cast_add, Polynomial.Chebyshev.T_add_two, mul_assoc]
    rw [heq]
    exact (trigSpan mode (m + 2)).sub_mem
      ((trigSpan mode (m + 2)).smul_mem 2 (by convert hmul using 1; congr 1; omega)) hm'

theorem trigSpan_exists_coefficients (mode : ℤ → X → ℂ) {m : ℕ} {f : X → ℂ}
    (hf : f ∈ trigSpan mode m) :
    ∃ c : ℤ → ℂ, ∑ k ∈ Finset.Icc (-(m : ℤ)) m, c k • mode k = f := by
  apply (Submodule.mem_span_image_finset_iff_exists_fun' ℂ).mp
  simpa only [trigSpan, Finset.coe_Icc] using hf

noncomputable def phaseMode (k : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)

lemma phaseMode_zero : phaseMode 0 = 1 := by
  ext θ
  simp [phaseMode]

lemma phaseMode_add (i j : ℤ) : phaseMode (i + j) = phaseMode i * phaseMode j := by
  ext θ
  simp only [phaseMode, Int.cast_add, add_mul, Complex.exp_add, Pi.mul_apply]

lemma filterArgument_mem_trigSpan (a : ℝ) :
    (fun θ => (filterArgument a θ : ℂ)) ∈ trigSpan phaseMode 1 := by
  have h1 := mode_mem_trigSpan phaseMode (n := 1) (k := 1) (by norm_num)
  have hn := mode_mem_trigSpan phaseMode (n := 1) (k := -1) (by norm_num)
  have h0 := trigSpan_one phaseMode phaseMode_zero 1
  have heq : (fun θ => (filterArgument a θ : ℂ)) =
      ((1 - 2 * Real.cos a / (1 + Real.cos a) : ℝ) : ℂ) • (1 : ℝ → ℂ) +
      ((1 / (1 + Real.cos a) : ℝ) : ℂ) • (phaseMode 1 + phaseMode (-1)) := by
    ext θ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      phaseMode, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
    rw [← Complex.two_cos, ← Complex.ofReal_cos]
    unfold filterArgument
    push_cast
    ring
  rw [heq]
  exact (trigSpan phaseMode 1).add_mem
    ((trigSpan phaseMode 1).smul_mem _ h0)
    ((trigSpan phaseMode 1).smul_mem _ ((trigSpan phaseMode 1).add_mem h1 hn))

/-- The filter in Equation (34) has an exact finite exponential expansion.
The coefficients in this theorem have not yet been identified with the
integral-defined `filterFourierCoeff`. -/
theorem chebyshevFilter_exists_expansion (m : ℕ) (a : ℝ) :
    ∃ c : ℤ → ℂ, ∀ θ : ℝ,
      ∑ k ∈ Finset.Icc (-(m : ℤ)) m, c k * phaseMode k θ = (chebyshevFilter m a θ : ℂ) := by
  have hmem := chebyshev_mem_trigSpan phaseMode phaseMode_zero phaseMode_add
    (fun θ => (filterArgument a θ : ℂ)) (filterArgument_mem_trigSpan a) m
  have hfilter : (fun θ => (chebyshevFilter m a θ : ℂ)) ∈ trigSpan phaseMode m := by
    have hh := (trigSpan phaseMode m).smul_mem
      ((((Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (filterArgument a 0) : ℝ) : ℂ)⁻¹) hmem
    convert hh using 1
    ext θ
    simp only [Pi.smul_apply, smul_eq_mul, chebyshevFilter, Complex.ofReal_div]
    have hcast := Polynomial.Chebyshev.algebraMap_eval_T (R := ℝ) (R' := ℂ)
      (filterArgument a θ) (m : ℤ)
    change (((Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (filterArgument a θ) : ℝ) : ℂ) =
      (Polynomial.Chebyshev.T ℂ (m : ℤ)).eval (filterArgument a θ : ℂ) at hcast
    rw [← hcast]
    simp [div_eq_mul_inv, mul_comm]
  obtain ⟨c, hc⟩ := trigSpan_exists_coefficients phaseMode hfilter
  refine ⟨c, fun θ => ?_⟩
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc θ

end SKQD
