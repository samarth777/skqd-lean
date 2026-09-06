import LeanExperiments.SKQD.Filter
import LeanExperiments.SKQD.Trigonometric

/-! Fourier coefficients of the Appendix A filter. -/
namespace SKQD

open MeasureTheory AddCircle

/-- Fourier coefficients on one full phase period. -/
noncomputable def filterFourierCoeff (m : ℕ) (a : ℝ) (k : ℤ) : ℂ :=
  fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos])
    (fun θ => (chebyshevFilter m a θ : ℂ)) k

/-- A bounded function has Fourier coefficients bounded by its uniform bound.
This argument uses the integral definition directly, without assuming Parseval. -/
lemma fourierCoeffOn_norm_le_one {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (k : ℤ) :
    ‖fourierCoeffOn hab f k‖ ≤ 1 := by
  let : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have hbounded : ∀ x ∈ Set.uIoc a b,
      ‖fourier (-k) (x : AddCircle (b - a)) • f x‖ ≤ (1 : ℝ) := by
    intro x _
    have hn : ‖fourier (-k) (x : AddCircle (b - a))‖ = 1 := Circle.norm_coe _
    rw [norm_smul, hn, one_mul]
    exact hf x
  have hb : ‖∫ x in a..b, fourier (-k) (x : AddCircle (b - a)) • f x‖ ≤ |b - a| := by
    simpa only [one_mul] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbounded
  calc
    _ ≤ ‖(1 : ℝ) / (b - a)‖ * |b - a| := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = 1 := by
      rw [Real.norm_eq_abs, abs_div, abs_one, div_mul_cancel₀]
      exact abs_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hab))

/-- In particular each Fourier coefficient of the paper's filter has norm ≤ 1. -/
theorem filterFourierCoeff_norm_le_one (m : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haπ : a < Real.pi) (k : ℤ) :
    ‖filterFourierCoeff m a k‖ ≤ 1 := by
  apply fourierCoeffOn_norm_le_one
  intro θ
  simpa using chebyshevFilter_abs_le_one m ha haπ θ

/-- Parseval's bound on any finite set of coefficients; in particular this
applies to the frequency interval `[-m,m]` in Equation (35). -/
lemma fourierCoeffOn_sum_sq_le_one {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hc : Continuous f) (hf : ∀ x, ‖f x‖ ≤ 1) (s : Finset ℤ) :
    ∑ k ∈ s, ‖fourierCoeffOn hab f k‖ ^ 2 ≤ 1 := by
  have hlp : MemLp f 2 (volume.restrict (Set.Ioc a b)) :=
    MemLp.of_bound hc.aestronglyMeasurable 1 (Filter.Eventually.of_forall hf)
  have hs := hasSum_sq_fourierCoeffOn hab hlp
  have hI : ‖∫ x in a..b, ‖f x‖ ^ 2‖ ≤ b - a := by
    have hh : ∀ x ∈ Set.uIoc a b, ‖‖f x‖ ^ 2‖ ≤ (1 : ℝ) := by
      intro x _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (f x), hf x]
    simpa only [one_mul, abs_of_pos (sub_pos.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hh
  have htotal : (b - a)⁻¹ • (∫ x in a..b, ‖f x‖ ^ 2) ≤ (1 : ℝ) := by
    rw [smul_eq_mul, ← div_eq_inv_mul]
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    simpa only [one_mul] using (le_abs_self _).trans hI
  exact (hs.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)).trans
    (hs.tsum_eq.trans_le htotal)

theorem filterFourierCoeff_sum_sq_le_one (m : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haπ : a < Real.pi) (s : Finset ℤ) :
    ∑ k ∈ s, ‖filterFourierCoeff m a k‖ ^ 2 ≤ 1 := by
  apply fourierCoeffOn_sum_sq_le_one
  · unfold chebyshevFilter filterArgument
    fun_prop
  · intro θ
    simpa using chebyshevFilter_abs_le_one m ha haπ θ

lemma phaseMode_eq_fourier (k : ℤ) (θ : ℝ) :
    phaseMode k θ = fourier k (θ : AddCircle (2 * Real.pi)) := by
  rw [fourier_coe_apply]
  unfold phaseMode
  congr 1
  push_cast
  field_simp

/-- Extracting a coefficient of a finite character sum. -/
lemma fourierCoeff_finite_sum {T : ℝ} [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ)
    {k : ℤ} (hk : k ∈ s) :
    fourierCoeff (fun x : AddCircle T => ∑ j ∈ s, c j * fourier j x) k = c k := by
  have heq : (fun x : AddCircle T => ∑ j ∈ s, c j * fourier j x) =
      ∑ j ∈ s, c j • (fourier j : AddCircle T → ℂ) := by
    ext x
    simp
  rw [heq, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_smul, fourierCoeff_fourier,
      smul_eq_mul]
    simp [Pi.single_apply, hk]
  · intro j _
    exact ((fourier j).continuous.const_smul (c j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma fourierCoeff_norm_le_one {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (k : ℤ) : ‖fourierCoeff f k‖ ≤ 1 := by
  unfold fourierCoeff
  have hbound : ∀ᵐ x ∂haarAddCircle, ‖fourier (-k) x • f x‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    have hn : ‖fourier (-k) x‖ = 1 := Circle.norm_coe _
    rw [norm_smul, hn, one_mul]
    exact hf x
  simpa using norm_integral_le_of_norm_le_const hbound

/-- Equation (35), with coefficient bounds for the *same* finite expansion.
The finite expansion and uniform bound are both derived from the concrete
Chebyshev filter rather than supplied as assumptions. -/
theorem chebyshevFilter_bounded_expansion (m : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haπ : a < Real.pi) :
    ∃ c : ℤ → ℂ,
      (∀ k ∈ Finset.Icc (-(m : ℤ)) m, ‖c k‖ ≤ 1) ∧
      (∀ θ : ℝ, ∑ k ∈ Finset.Icc (-(m : ℤ)) m, c k * phaseMode k θ =
        (chebyshevFilter m a θ : ℂ)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  obtain ⟨c, hc⟩ := chebyshevFilter_exists_expansion m a
  let s := Finset.Icc (-(m : ℤ)) m
  let f : AddCircle (2 * Real.pi) → ℂ := fun x => ∑ j ∈ s, c j * fourier j x
  have hf : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H θ =>
      have heq : f (θ : AddCircle (2 * Real.pi)) = (chebyshevFilter m a θ : ℂ) := by
        simpa only [f, s, ← phaseMode_eq_fourier] using hc θ
      rw [heq]
      simpa using chebyshevFilter_abs_le_one m ha haπ θ
  refine ⟨c, ?_, hc⟩
  intro k hk
  have heq := fourierCoeff_finite_sum (T := 2 * Real.pi) s c hk
  rw [← heq]
  exact fourierCoeff_norm_le_one f hf k

end SKQD
