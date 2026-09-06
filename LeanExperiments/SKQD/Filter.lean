import Mathlib

/-! The real Chebyshev trigonometric filter of Appendix A, Equation (34). -/
namespace SKQD

open Polynomial.Chebyshev

noncomputable def filterArgument (a θ : ℝ) : ℝ :=
  1 + 2 * (Real.cos θ - Real.cos a) / (1 + Real.cos a)

noncomputable def chebyshevFilter (m : ℕ) (a θ : ℝ) : ℝ :=
  (T ℝ (m : ℤ)).eval (filterArgument a θ) /
    (T ℝ (m : ℤ)).eval (filterArgument a 0)

lemma filter_denominator_pos {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi) :
    0 < 1 + Real.cos a := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi ha (le_refl Real.pi) haπ
  simp only [Real.cos_pi] at this
  linarith

lemma filterArgument_zero_ge_one {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi) :
    1 ≤ filterArgument a 0 := by
  have hd := filter_denominator_pos ha haπ
  simp only [filterArgument, Real.cos_zero]
  have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (sub_nonneg.mpr (Real.cos_le_one a))) hd.le
  linarith

theorem chebyshevFilter_zero (m : ℕ) {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi) :
    chebyshevFilter m a 0 = 1 := by
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (one_le_eval_T_real _ (filterArgument_zero_ge_one ha haπ))))

lemma filterArgument_bounds {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi) (θ : ℝ) :
    -1 ≤ filterArgument a θ ∧ filterArgument a θ ≤ filterArgument a 0 := by
  have hd := filter_denominator_pos ha haπ
  constructor
  · unfold filterArgument
    have h := Real.neg_one_le_cos θ
    have : -2 ≤ 2 * (Real.cos θ - Real.cos a) / (1 + Real.cos a) :=
      (le_div_iff₀ hd).mpr (by nlinarith)
    linarith
  · unfold filterArgument
    simp only [Real.cos_zero]
    apply add_le_add_right
    apply (div_le_div_iff_of_pos_right hd).mpr
    nlinarith [Real.cos_le_one θ]

lemma chebyshev_mono_above_one (m : ℕ) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (T ℝ (m : ℤ)).eval x ≤ (T ℝ (m : ℤ)).eval y := by
  have hy := hx.trans hxy
  rw [← Real.cosh_arcosh hx, T_real_cosh, ← Real.cosh_arcosh hy, T_real_cosh]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hx)),
    abs_of_nonneg (mul_nonneg (by positivity) (Real.arcosh_nonneg hy))]
  exact mul_le_mul_of_nonneg_left
    ((Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hxy) (by positivity)

/-- The bound on the entire real line needed for Fourier coefficient estimates. -/
theorem chebyshevFilter_abs_le_one (m : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (haπ : a < Real.pi) (θ : ℝ) :
    |chebyshevFilter m a θ| ≤ 1 := by
  have hden := one_le_eval_T_real (m : ℤ) (filterArgument_zero_ge_one ha haπ)
  have hdpos : 0 < (T ℝ (m : ℤ)).eval (filterArgument a 0) := by linarith
  obtain ⟨hlow, hupp⟩ := filterArgument_bounds ha haπ θ
  rw [chebyshevFilter, abs_div, abs_of_pos hdpos, div_le_one hdpos]
  by_cases hx : filterArgument a θ ≤ 1
  · exact (abs_eval_T_real_le_one _ (abs_le.mpr ⟨hlow, hx⟩)).trans hden
  · have hone : 1 ≤ filterArgument a θ := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonneg (zero_le_one.trans (one_le_eval_T_real _ hone))]
    exact chebyshev_mono_above_one m hone hupp

lemma filterArgument_off_band {a θ : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi)
    (hθ : |θ| ≤ Real.pi) (hband : a ≤ |θ|) : |filterArgument a θ| ≤ 1 := by
  refine abs_le.mpr ⟨(filterArgument_bounds ha haπ θ).1, ?_⟩
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha hθ hband
  rw [Real.cos_abs] at hc
  unfold filterArgument
  have : 2 * (Real.cos θ - Real.cos a) / (1 + Real.cos a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (filter_denominator_pos ha haπ).le
  linarith

lemma filterArgument_zero_tan {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi) :
    filterArgument a 0 = 1 + 2 * Real.tan (a / 2) ^ 2 := by
  have hd := filter_denominator_pos ha haπ
  have hc : 0 < Real.cos (a / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcos := Real.cos_two_mul (a / 2)
  have hsq := Real.sin_sq_add_cos_sq (a / 2)
  have hat : 2 * (a / 2) = a := by ring
  rw [hat] at hcos
  simp only [filterArgument, Real.cos_zero, Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith

/-- The growth base of the denominator is at least `1 + a`. -/
lemma filter_growth_base {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi) :
    1 + a ≤ Real.exp (Real.arcosh (filterArgument a 0)) := by
  have hx := filterArgument_zero_ge_one ha haπ
  have ht := Real.le_tan (show 0 ≤ a / 2 by linarith) (show a / 2 < Real.pi / 2 by linarith)
  have htn : 0 ≤ Real.tan (a / 2) := le_trans (by linarith) ht
  rw [Real.exp_arcosh hx]
  have hs : 2 * Real.tan (a / 2) ≤ Real.sqrt (filterArgument a 0 ^ 2 - 1) := by
    apply (Real.le_sqrt (by positivity) (by nlinarith)).mpr
    rw [filterArgument_zero_tan ha haπ]
    nlinarith [sq_nonneg (Real.tan (a / 2) ^ 2)]
  linarith

theorem chebyshevFilter_off_band (m : ℕ) {a θ : ℝ}
    (ha : 0 ≤ a) (haπ : a < Real.pi) (hθ : |θ| ≤ Real.pi) (hband : a ≤ |θ|) :
    |chebyshevFilter m a θ| ≤ 2 / (1 + a) ^ m := by
  have hx := filterArgument_zero_ge_one ha haπ
  have hden := one_le_eval_T_real (m : ℤ) hx
  have hdpos : 0 < (T ℝ (m : ℤ)).eval (filterArgument a 0) := by linarith
  have hnum := abs_eval_T_real_le_one (m : ℤ) (filterArgument_off_band ha haπ hθ hband)
  have hbase := filter_growth_base ha haπ
  have hpow : (1 + a) ^ m ≤ 2 * (T ℝ (m : ℤ)).eval (filterArgument a 0) := by
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + a) hbase m
    rw [← Real.exp_nat_mul] at hp
    rw [← Real.cosh_arcosh hx, T_real_cosh, Real.cosh_eq]
    norm_cast at *
    linarith [Real.exp_pos (-((m : ℝ) * Real.arcosh (filterArgument a 0)))]
  rw [chebyshevFilter, abs_div, abs_of_pos hdpos]
  calc
    _ ≤ 1 / (T ℝ (m : ℤ)).eval (filterArgument a 0) := div_le_div_of_nonneg_right hnum hdpos.le
    _ ≤ 2 / (1 + a) ^ m := by
      apply (div_le_div_iff₀ hdpos (pow_pos (by linarith) m)).mpr
      simpa using hpow

end SKQD
