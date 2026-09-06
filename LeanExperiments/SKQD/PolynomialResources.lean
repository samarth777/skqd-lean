import LeanExperiments.SKQD.Probability

/-! Explicit polynomial resource bounds under the paper's polynomially
controlled spectral, overlap, sparsity, and confidence parameters. -/
namespace SKQD

noncomputable def resourceTarget (gap β : ℝ) : ℝ := gap * β ^ 2 / 32

noncomputable def resourceDimension (W gap g β : ℝ) : ℕ :=
  polynomialOddDimension (8 * W * (1 - g) / g) (Real.pi * gap / W) (resourceTarget gap β)

lemma resourceDimension_pos (W gap g β : ℝ) : 0 < resourceDimension W gap g β := by
  unfold resourceDimension polynomialOddDimension
  omega

lemma resourceDimension_odd (W gap g β : ℝ) :
    effectiveOddDimension (resourceDimension W gap g β) = resourceDimension W gap g β := by
  unfold effectiveOddDimension resourceDimension polynomialOddDimension
  omega

theorem resourceDimension_accuracy {W gap g β : ℝ}
    (hW : 0 < W) (hgap : 0 < gap) (hg : 0 < g) (hg1 : g ≤ 1) (hβ : 0 < β) :
    paperKrylovError W gap g (resourceDimension W gap g β) ≤ resourceTarget gap β := by
  exact polynomialOddDimension_error (by positivity) (by positivity) (by unfold resourceTarget; positivity)

theorem resourceTarget_le_gap {gap β : ℝ} (hgap : 0 < gap) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    resourceTarget gap β ≤ gap := by
  unfold resourceTarget
  have : β ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hgap.le]

/-- A common polynomial envelope for the physical input parameters gives
an explicit polynomial bound on the chosen Krylov dimension. -/
theorem resourceDimension_size {W gap g β R : ℝ}
    (hW : 0 < W) (hgap : 0 < gap) (hg : 0 < g) (hg1 : g ≤ 1) (hβ : 0 < β)
    (hR : 1 ≤ R) (hWR : W ≤ R) (hgR : g⁻¹ ≤ R)
    (hgapR : gap⁻¹ ≤ R) (hβR : β⁻¹ ≤ R) :
    (resourceDimension W gap g β : ℝ) ≤ 260 * R ^ 7 := by
  have hC : 0 ≤ 8 * W * (1 - g) / g := by positivity
  have ha : 0 < Real.pi * gap / W := by positivity
  have hτ : 0 < resourceTarget gap β := by unfold resourceTarget; positivity
  have hd := polynomialOddDimension_size hC ha hτ
  have hid : (8 * W * (1 - g) / g) / (resourceTarget gap β * (Real.pi * gap / W)) =
      (256 / Real.pi) * W ^ 2 * (1 - g) * g⁻¹ * (gap⁻¹) ^ 2 * (β⁻¹) ^ 2 := by
    unfold resourceTarget
    field_simp
    ring
  have hπ : 1 ≤ Real.pi := (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
  have hc : 256 / Real.pi ≤ (256 : ℝ) := (div_le_iff₀ Real.pi_pos).mpr (by nlinarith)
  have hprod : (256 / Real.pi) * W ^ 2 * (1 - g) * g⁻¹ * (gap⁻¹) ^ 2 * (β⁻¹) ^ 2 ≤
      256 * R ^ 2 * 1 * R * R ^ 2 * R ^ 2 := by
    gcongr
    linarith
  have hpow : 1 ≤ R ^ 7 := one_le_pow₀ hR
  have hidR : 256 * R ^ 2 * 1 * R * R ^ 2 * R ^ 2 = 256 * R ^ 7 := by ring
  rw [hid] at hd
  rw [hidR] at hprod
  change (resourceDimension W gap g β : ℝ) < _ at hd
  linarith

noncomputable def resourceThreshold (d : ℕ) (L η g β ε gap : ℝ) : ℝ :=
  (d : ℝ) ^ 2 * Real.log (L / η) / (g * (β - 2 * Real.sqrt (epsTilde ε gap)))

noncomputable def resourceShots (W gap g β L η : ℝ) : ℕ :=
  sufficientShots (resourceThreshold (resourceDimension W gap g β) L η g β
    (paperKrylovError W gap g (resourceDimension W gap g β)) gap)

theorem resourceParameterDomains {W gap g β : ℝ}
    (hW : 0 < W) (hgap : 0 < gap) (hg : 0 < g) (hg1 : g ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    let ε := paperKrylovError W gap g (resourceDimension W gap g β)
    0 ≤ ε ∧ ε ≤ gap ∧ β / 2 ≤ β - 2 * Real.sqrt (epsTilde ε gap) := by
  dsimp only
  have hε : 0 ≤ paperKrylovError W gap g (resourceDimension W gap g β) := by
    unfold paperKrylovError
    positivity
  have htarget := resourceDimension_accuracy hW hgap hg hg1 hβ
  have hεgap := htarget.trans (resourceTarget_le_gap hgap hβ hβ1)
  exact ⟨hε, hεgap, retained_sparsity_ge_half hε hεgap hgap hβ.le htarget⟩

theorem resourceThreshold_size {d : ℕ} {L η g β ε gap R : ℝ}
    (hL : 1 ≤ L) (hη : 0 < η) (hη1 : η ≤ 1) (hg : 0 < g) (hβ : 0 < β)
    (hretained : β / 2 ≤ β - 2 * Real.sqrt (epsTilde ε gap))
    (hR : 1 ≤ R) (hdR : (d : ℝ) ≤ 260 * R ^ 7)
    (hlog : Real.log (L / η) ≤ R ^ 2) (hgR : g⁻¹ ≤ R) (hβR : β⁻¹ ≤ R) :
    0 ≤ resourceThreshold d L η g β ε gap ∧ resourceThreshold d L η g β ε gap ≤ 135200 * R ^ 18 := by
  have hlog0 : 0 ≤ Real.log (L / η) := Real.log_nonneg ((one_le_div hη).mpr (hη1.trans hL))
  have hretpos : 0 < β - 2 * Real.sqrt (epsTilde ε gap) := lt_of_lt_of_le (by positivity) hretained
  constructor
  · unfold resourceThreshold; positivity
  · unfold resourceThreshold
    calc
      _ ≤ (d : ℝ) ^ 2 * Real.log (L / η) / (g * (β / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hretained hg.le)
      _ = 2 * (d : ℝ) ^ 2 * Real.log (L / η) * g⁻¹ * β⁻¹ := by ring
      _ ≤ 2 * (260 * R ^ 7) ^ 2 * R ^ 2 * R * R := by gcongr
      _ = 135200 * R ^ 18 := by ring

theorem resourceShots_size {W gap g β L η R : ℝ}
    (hW : 0 < W) (hgap : 0 < gap) (hg : 0 < g) (hg1 : g ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 1 ≤ L) (hη : 0 < η) (hη1 : η ≤ 1)
    (hR : 1 ≤ R) (hWR : W ≤ R) (hgR : g⁻¹ ≤ R) (hgapR : gap⁻¹ ≤ R)
    (hβR : β⁻¹ ≤ R) (hlogR : Real.log (L / η) ≤ R) :
    (resourceShots W gap g β L η : ℝ) ≤ 140000 * R ^ 18 := by
  have hd := resourceDimension_size hW hgap hg hg1 hβ hR hWR hgR hgapR hβR
  have hret := (resourceParameterDomains hW hgap hg hg1 hβ hβ1).2.2
  have hlog : Real.log (L / η) ≤ R ^ 2 := hlogR.trans (by nlinarith [sq_nonneg (R - 1)])
  obtain ⟨ht0, ht⟩ := resourceThreshold_size hL hη hη1 hg hβ hret hR hd hlog hgR hβR
  have hM := sufficientShots_size ht0
  change (resourceShots W gap g β L η : ℝ) ≤ _ at hM
  have hpow : 1 ≤ R ^ 18 := one_le_pow₀ hR
  linarith

/-- A common envelope for the quantities assumed polynomially controlled.
No conclusion about the required resources is a field of this structure. -/
structure ResourceEnvelope (W gap g β L η R : ℝ) : Prop where
  bandwidth_pos : 0 < W
  gap_pos : 0 < gap
  overlap_pos : 0 < g
  overlap_le_one : g ≤ 1
  sparsity_pos : 0 < β
  sparsity_le_one : β ≤ 1
  support_nonempty : 1 ≤ L
  confidence_pos : 0 < η
  confidence_le_one : η ≤ 1
  envelope_ge_one : 1 ≤ R
  bandwidth_le : W ≤ R
  inverse_overlap_le : g⁻¹ ≤ R
  inverse_gap_le : gap⁻¹ ≤ R
  inverse_sparsity_le : β⁻¹ ≤ R
  support_le : L ≤ R
  confidence_cost_le : Real.log (L / η) ≤ R

theorem ResourceEnvelope.dimension_bound {W gap g β L η R : ℝ}
    (h : ResourceEnvelope W gap g β L η R) :
    (resourceDimension W gap g β : ℝ) ≤ 260 * R ^ 7 :=
  resourceDimension_size h.bandwidth_pos h.gap_pos h.overlap_pos h.overlap_le_one
    h.sparsity_pos h.envelope_ge_one h.bandwidth_le h.inverse_overlap_le h.inverse_gap_le h.inverse_sparsity_le

theorem ResourceEnvelope.shots_bound {W gap g β L η R : ℝ}
    (h : ResourceEnvelope W gap g β L η R) :
    (resourceShots W gap g β L η : ℝ) ≤ 140000 * R ^ 18 :=
  resourceShots_size h.bandwidth_pos h.gap_pos h.overlap_pos h.overlap_le_one
    h.sparsity_pos h.sparsity_le_one h.support_nonempty h.confidence_pos h.confidence_le_one
    h.envelope_ge_one h.bandwidth_le h.inverse_overlap_le h.inverse_gap_le h.inverse_sparsity_le
    h.confidence_cost_le

theorem polynomial_envelope_isBigO (f : ℕ → ℝ) (A K : ℝ) (p r : ℕ)
    (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ n, f n ≤ A * (K * ((n : ℝ) + 1) ^ p) ^ r) :
    Asymptotics.IsBigO Filter.atTop f (fun n => ((n : ℝ) + 1) ^ (r * p)) := by
  apply Asymptotics.IsBigO.of_bound (A * K ^ r)
  apply Filter.Eventually.of_forall
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n), Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ A * (K * ((n : ℝ) + 1) ^ p) ^ r := hf n
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm p r]; ring

/-- A formal asymptotic corollary for families indexed by system size.
Krylov dimension, shots per Krylov state, and total shots are polynomial. -/
theorem resourceCounts_isBigO (W gap g β L η : ℕ → ℝ) (K : ℝ) (p : ℕ)
    (h : ∀ n, ResourceEnvelope (W n) (gap n) (g n) (β n) (L n) (η n)
      (K * ((n : ℝ) + 1) ^ p)) :
    Asymptotics.IsBigO Filter.atTop (fun n => (resourceDimension (W n) (gap n) (g n) (β n) : ℝ))
      (fun n => ((n : ℝ) + 1) ^ (7 * p)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n => (resourceShots (W n) (gap n) (g n) (β n) (L n) (η n) : ℝ))
      (fun n => ((n : ℝ) + 1) ^ (18 * p)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n =>
      (resourceDimension (W n) (gap n) (g n) (β n) : ℝ) *
      (resourceShots (W n) (gap n) (g n) (β n) (L n) (η n) : ℝ))
      (fun n => ((n : ℝ) + 1) ^ (25 * p)) := by
  have hd := polynomial_envelope_isBigO
    (fun n => (resourceDimension (W n) (gap n) (g n) (β n) : ℝ)) 260 K p 7
    (by intro n; positivity) (fun n => (h n).dimension_bound)
  have hM := polynomial_envelope_isBigO
    (fun n => (resourceShots (W n) (gap n) (g n) (β n) (L n) (η n) : ℝ)) 140000 K p 18
    (by intro n; positivity) (fun n => (h n).shots_bound)
  refine ⟨hd, hM, ?_⟩
  have hh := hd.mul hM
  have heq : 7 * p + 18 * p = 25 * p := by omega
  simpa only [← pow_add, heq] using hh

noncomputable def resourceMaxTime (W gap g β : ℝ) : ℝ :=
  (resourceDimension W gap g β : ℝ) * Real.pi / W

theorem ResourceEnvelope.maxTime_bound {W gap g β L η R : ℝ}
    (h : ResourceEnvelope W gap g β L η R) (hgapW : gap ≤ W) :
    resourceMaxTime W gap g β ≤ 1040 * R ^ 8 := by
  have hR0 : 0 ≤ R := zero_le_one.trans h.envelope_ge_one
  have hW0 := h.bandwidth_pos
  have hi : W⁻¹ ≤ R := by
    have hh := one_div_le_one_div_of_le h.gap_pos hgapW
    have hh' : W⁻¹ ≤ gap⁻¹ := by simpa only [one_div] using hh
    exact hh'.trans h.inverse_gap_le
  have hπ : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hd := h.dimension_bound
  unfold resourceMaxTime
  calc
    _ = (resourceDimension W gap g β : ℝ) * Real.pi * W⁻¹ := by ring
    _ ≤ (260 * R ^ 7) * 4 * R := by gcongr
    _ = _ := by ring

theorem evolutionTime_isBigO (W gap g β L η : ℕ → ℝ) (K : ℝ) (p : ℕ)
    (h : ∀ n, ResourceEnvelope (W n) (gap n) (g n) (β n) (L n) (η n)
      (K * ((n : ℝ) + 1) ^ p)) (hgapW : ∀ n, gap n ≤ W n) :
    Asymptotics.IsBigO Filter.atTop (fun n => resourceMaxTime (W n) (gap n) (g n) (β n))
      (fun n => ((n : ℝ) + 1) ^ (8 * p)) := by
  apply polynomial_envelope_isBigO _ 1040 K p 8
  · intro n
    have hW := (h n).bandwidth_pos
    unfold resourceMaxTime
    positivity
  · intro n
    exact (h n).maxTime_bound (hgapW n)

end SKQD
