import LeanExperiments.SKQD.Theorem1

/-! Explicit scalar parameter choices. These do not assert the existence
of a Krylov witness or the runtime of an eigensolver. -/
namespace SKQD

/-- Equation (31), written using a natural power in the denominator.
For the paper's odd-dimensional construction use `d = 2*m+1`. -/
noncomputable def paperKrylovError (W gap overlapSq : ℝ) (d : ℕ) : ℝ :=
  (8 * W * (1 - overlapSq) / overlapSq) /
    (1 + Real.pi * gap / W) ^ (d - 1)

lemma geometric_error_le {C q ε : ℝ} {n : ℕ}
    (hC : 0 < C) (hq : 1 < q) (hε : 0 < ε)
    (hn : Real.log (C / ε) / Real.log q ≤ (n : ℝ)) :
    C / q ^ n ≤ ε := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hl : Real.log (C / ε) ≤ Real.log (q ^ n) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hlq).mp hn
  have hdiv : C / ε ≤ q ^ n :=
    (Real.log_le_log_iff (div_pos hC hε) (pow_pos (by linarith) n)).mp hl
  apply (div_le_iff₀ (pow_pos (by linarith) n)).mpr
  simpa [mul_comm] using (div_le_iff₀ hε).mp hdiv

/-- An explicit odd Krylov dimension attaining a target scalar error. -/
noncomputable def sufficientOddDimension (C q ε : ℝ) : ℕ :=
  2 * ⌈Real.log (C / ε) / (2 * Real.log q)⌉₊ + 1

theorem sufficientOddDimension_error {C q ε : ℝ}
    (hC : 0 < C) (hq : 1 < q) (hε : 0 < ε) :
    C / q ^ (sufficientOddDimension C q ε - 1) ≤ ε := by
  apply geometric_error_le hC hq hε
  have hceil := Nat.le_ceil (Real.log (C / ε) / (2 * Real.log q))
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hscale : Real.log (C / ε) / Real.log q =
      2 * (Real.log (C / ε) / (2 * Real.log q)) := by ring
  rw [hscale]
  simp only [sufficientOddDimension, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- The state error is at most twice the relative energy error. -/
theorem epsTilde_le_twice_ratio {ε gap : ℝ}
    (hε : 0 ≤ ε) (hεgap : ε ≤ gap) (hgap : 0 < gap) :
    epsTilde ε gap ≤ 2 * ε / gap := by
  have hr : 0 ≤ 1 - ε / gap := sub_nonneg.mpr ((div_le_one hgap).mpr hεgap)
  have hu : 1 - ε / gap ≤ 1 := by linarith [div_nonneg hε hgap.le]
  have hs : 1 - ε / gap ≤ Real.sqrt (1 - ε / gap) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  unfold epsTilde
  rw [mul_div_assoc]
  linarith

/-- Choosing `ε ≤ gap*β²/32` retains at least half the ground-state
pointwise sparsity. This makes the sample threshold denominator positive. -/
theorem retained_sparsity_ge_half {ε gap β : ℝ}
    (hε : 0 ≤ ε) (hεgap : ε ≤ gap) (hgap : 0 < gap)
    (hβ : 0 ≤ β) (htarget : ε ≤ gap * β ^ 2 / 32) :
    β / 2 ≤ β - 2 * Real.sqrt (epsTilde ε gap) := by
  have he := epsTilde_le_twice_ratio hε hεgap hgap
  have het := epsTilde_nonneg hε hεgap hgap
  have hratio : 2 * ε / gap ≤ β ^ 2 / 16 := by
    apply (div_le_iff₀ hgap).mpr
    nlinarith
  have hs : Real.sqrt (epsTilde ε gap) ≤ β / 4 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  linarith

/-- Positive integer shot count meeting any real lower bound. -/
noncomputable def sufficientShots (threshold : ℝ) : ℕ := max 1 ⌈threshold⌉₊

theorem sufficientShots_pos (threshold : ℝ) : 0 < sufficientShots threshold :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem sufficientShots_meets_threshold (threshold : ℝ) :
    threshold ≤ (sufficientShots threshold : ℝ) :=
  (Nat.le_ceil threshold).trans (by exact_mod_cast le_max_right 1 ⌈threshold⌉₊)

/-- A looser, manifestly polynomial alternative to the logarithmic dimension
choice. Bernoulli's inequality suffices to prove its error bound. -/
noncomputable def polynomialOddDimension (C a ε : ℝ) : ℕ :=
  2 * ⌈C / (2 * ε * a)⌉₊ + 1

theorem polynomialOddDimension_error {C a ε : ℝ}
    (_hC : 0 ≤ C) (ha : 0 < a) (hε : 0 < ε) :
    C / (1 + a) ^ (polynomialOddDimension C a ε - 1) ≤ ε := by
  have hceil := Nat.le_ceil (C / (2 * ε * a))
  have hscaled := (div_le_iff₀ (show 0 < 2 * ε * a by positivity)).mp hceil
  have hbern := one_add_mul_le_pow (show -2 ≤ a by linarith)
    (polynomialOddDimension C a ε - 1)
  have hmul := mul_le_mul_of_nonneg_left hbern hε.le
  apply (div_le_iff₀ (pow_pos (by linarith) _)).mpr
  simp only [polynomialOddDimension, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat] at hmul ⊢
  nlinarith

theorem polynomialOddDimension_size {C a ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hε : 0 < ε) :
    (polynomialOddDimension C a ε : ℝ) < C / (ε * a) + 3 := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ C / (2 * ε * a) by positivity)
  have heq : C / (ε * a) = 2 * (C / (2 * ε * a)) := by ring
  simp only [polynomialOddDimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [heq]
  linarith

theorem sufficientShots_size {threshold : ℝ} (h : 0 ≤ threshold) :
    (sufficientShots threshold : ℝ) ≤ threshold + 1 := by
  unfold sufficientShots
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (Nat.ceil_lt_add_one h).le

end SKQD
