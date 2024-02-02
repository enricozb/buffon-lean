import Mathlib.Probability.Density
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals

open MeasureTheory (MeasureSpace IsProbabilityMeasure pdf.IsUniform Measure)
open ProbabilityTheory

lemma set_integral_toReal_ofReal [MeasureSpace α] {s : Set α} {f : α → ℝ}
    (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x ≥ 0) :
    ∫ (x : α) in s, ENNReal.toReal (ENNReal.ofReal (f x)) =
    ∫ (x : α) in s, f x := by

  have comp_eq : (fun x => ENNReal.toReal (ENNReal.ofReal (f x))) = (ENNReal.toReal ∘ ENNReal.ofReal ∘ f) := by rfl
  simp_rw [comp_eq]

  have eq_on : Set.EqOn (ENNReal.toReal ∘ ENNReal.ofReal ∘ f) f s := by
    intro x hx
    simp only [Function.comp_apply, ENNReal.toReal_ofReal_eq_iff]
    exact hf x hx

  rw [MeasureTheory.set_integral_congr hs eq_on]

lemma sin_mul_le (l d θ : ℝ) (hl₁ : l ≥ 0) (hl₂ : l ≤ d) : θ.sin * l ≤ d := by
  rw [mul_comm, ← mul_one d]
  apply mul_le_mul_of_le_of_le hl₂ θ.sin_le_one hl₁ zero_le_one

lemma neg_sin_mul_le (l d θ : ℝ) (hl₁ : l ≥ 0) (hl₂ : l ≤ d) : -(θ.sin * l) ≤ d := by
  rw [mul_comm, ← mul_one d, mul_comm, ← neg_mul, mul_comm, ←Real.sin_neg]
  apply mul_le_mul_of_le_of_le hl₂ (-θ).sin_le_one hl₁ zero_le_one

notation "π" => Real.pi

variable
  /- Probability theory variables. -/
  {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

  /- Buffon's needle variables. -/

  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : d > 0)
  (hl : l > 0)

  /-
    `B = (X, Θ)` is the joint random variable for the x-position and angle of
    the needle. If a line is at `x = 0`, by symmetry, `B` can be a uniform
    random variable over `[-d/2, d/2] × [0, π]`, where `θ` is the angle of the
    needle relative to the y-axis.
  -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)

  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)

/--
  Projection of a needle onto the x-axis. The needle's center is at
  x-coordinate `x`, of length `l` and angle `θ`. Note, `θ` is measured
  relative to the y-axis, that is, a vertical needle has `θ = 0`.
-/
def needle_x_proj (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/--
  A random variable representing whether the needle crosses a line.

  The line is at `x = 0`, and the needle crosses the line if it's projection
  onto the x-axis contains `0`. This random variable is `1` if the needle
  crosses the line, and `0` otherwise.

  Note: `N : Ω → ℝ` is the random variable; the definition of `N' : ℝ × ℝ` is
  provided for convenience.
-/
noncomputable def N' (p : ℝ × ℝ) : ℝ := Set.indicator (needle_x_proj l p.1 p.2) 1 0
noncomputable def N : Ω → ℝ := N' l ∘ B

lemma short_needle_inter_eq (h : l ≤ d) (θ : ℝ) :
    Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) =
    Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) := by

  apply Set.inter_eq_self_of_subset_right
  apply Set.Icc_subset
  all_goals rw [Set.mem_Icc]

  · apply And.intro <;> apply div_le_div_of_le (le_of_lt two_pos) <;> rw [neg_mul]
    · exact neg_le_neg (sin_mul_le l d θ hl.le h)
    · exact neg_sin_mul_le l d θ hl.le h

  · apply And.intro <;> apply div_le_div_of_le (le_of_lt two_pos)
    · exact neg_le.mpr (neg_sin_mul_le l d θ hl.le h)
    · exact sin_mul_le l d θ hl.le h

abbrev B_range := Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π

lemma B_range_volume : ℙ (B_range d) = ENNReal.ofReal (d * π) := by
  simp_rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc]
  ring_nf
  exact (ENNReal.ofReal_mul hd.le).symm

lemma B_range_nonzero : ℙ (B_range d) ≠ 0 := by
  rw [B_range_volume d hd, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact mul_pos hd Real.pi_pos

lemma B_range_nontop : ℙ (B_range d) ≠ ⊤ := by
  rw [B_range_volume d hd]
  exact ENNReal.ofReal_ne_top

lemma B_range_measurable : MeasurableSet (B_range d) :=
  MeasurableSet.prod measurableSet_Icc measurableSet_Icc

instance instBHasPDF : MeasureTheory.HasPDF B ℙ :=
  MeasureTheory.pdf.IsUniform.hasPDF
    (B_range_measurable d) (B_range_nonzero d hd) (B_range_nontop d hd) hB

lemma N'_measurable : Measurable (N' l) := by
  unfold N'

  apply Measurable.indicator measurable_const
  apply IsClosed.measurableSet
  apply IsClosed.inter

  case' h.h₁ =>
    simp only [tsub_le_iff_right, zero_add]
    apply isClosed_le continuous_fst _
  case' h.h₂ =>
    simp only [← neg_le_iff_add_nonneg']
    apply isClosed_le _ _

  · conv => arg 1; intro p; rw [← mul_one p.1, ← mul_neg]
    exact Continuous.mul continuous_fst continuous_const

  all_goals
  · simp_rw [mul_div_assoc]
    apply Continuous.mul _ continuous_const
    have : (fun (x : ℝ × ℝ) => Real.sin x.2) = Real.sin ∘ Prod.snd := by rfl
    rw [this]
    apply Continuous.comp Real.continuous_sin continuous_snd

lemma N'_strongly_measurable : MeasureTheory.StronglyMeasurable (N' l) := by
  apply stronglyMeasurable_iff_measurable_separable.mpr
  apply And.intro
  · exact N'_measurable l
  · apply Exists.intro {0, 1}
    have range_finite : Set.Finite ({0, 1} : Set ℝ) := by
      simp only [Set.mem_singleton_iff, Set.finite_singleton, Set.Finite.insert]
    apply And.intro
    · exact Set.Finite.countable range_finite
    · rw [IsClosed.closure_eq (Set.Finite.isClosed range_finite)]
      unfold N' Set.range
      rw [Set.subset_def]
      intro x ⟨p, hxp⟩
      by_cases hp : 0 ∈ needle_x_proj l p.1 p.2
      · simp_rw [Set.indicator_of_mem hp, Pi.one_apply] at hxp
        apply Or.inr hxp.symm
      · simp_rw [Set.indicator_of_not_mem hp] at hxp
        apply Or.inl hxp.symm

lemma N'_integrable_prod :
    MeasureTheory.Integrable (N' l)
      (Measure.prod (Measure.restrict ℙ (Set.Icc (-d / 2) (d / 2))) (Measure.restrict ℙ (Set.Icc 0 π))) := by

  have N'_nonneg p : N' l p ≥ 0 := by
    apply Set.indicator_apply_nonneg
    simp only [Pi.one_apply, zero_le_one, implies_true]

  have N'_le_one p : N' l p ≤ 1 := by
    unfold N'
    by_cases hp : 0 ∈ needle_x_proj l p.1 p.2
    · simp_rw [Set.indicator_of_mem hp, Pi.one_apply, le_refl]
    · simp_rw [Set.indicator_of_not_mem hp, zero_le_one]

  apply And.intro (N'_strongly_measurable l).aestronglyMeasurable
  · apply (MeasureTheory.hasFiniteIntegral_iff_norm (N' l)).mpr
    apply lt_of_le_of_lt
    apply MeasureTheory.lintegral_mono (g := 1)
    · simp only [Real.norm_eq_abs, abs_of_nonneg (N'_nonneg _)]
      intro p
      simp only [ENNReal.ofReal_le_one, Pi.one_apply]
      exact N'_le_one p
    simp only [Pi.one_apply, MeasureTheory.lintegral_const, one_mul, MeasureTheory.Measure.prod_restrict]
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, MeasureTheory.Measure.prod_prod]
    simp_rw [Real.volume_Icc]
    ring_nf
    rw [← ENNReal.ofReal_mul hd.le]
    exact ENNReal.ofReal_lt_top

lemma buffon_integral :
    𝔼[N l B] = (d * π) ⁻¹ *
      ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1 := by
  simp_rw [N, Function.comp_apply]

  rw [
    ← MeasureTheory.integral_map (f := N' l) hBₘ.aemeasurable (N'_strongly_measurable l).aestronglyMeasurable,
    hB,
    MeasureTheory.integral_smul_measure,
    B_range_volume d hd,
    ENNReal.ofReal_inv_of_pos (mul_pos hd Real.pi_pos),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hd.le Real.pi_pos.le)),
    smul_eq_mul, mul_eq_mul_left_iff
  ]

  apply Or.inl

  have Real_measure_prod : (ℙ : Measure (ℝ × ℝ)) = Measure.prod ℙ ℙ := rfl

  have : MeasureTheory.IntegrableOn (N' l) (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) := by
    apply (MeasureTheory.integrableOn_def _ _ _).mpr
    rw [Real_measure_prod, ← MeasureTheory.Measure.prod_restrict]
    exact N'_integrable_prod d l hd

  rw [
    Real_measure_prod,
    MeasureTheory.set_integral_prod _ this,
    MeasureTheory.integral_integral_swap ?integrable,
  ]

  case integrable =>
    simp_rw [Function.uncurry_def, Prod.mk.eta]
    exact N'_integrable_prod d l hd

  unfold N' needle_x_proj
  simp only [Set.mem_Icc]

  have indicator_eq (x θ : ℝ) :
    Set.indicator (Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)) 1 0 =
    Set.indicator (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) (1 : ℝ → ℝ) x := by
    simp_rw [Set.indicator, Pi.one_apply, Set.mem_Icc, tsub_le_iff_right, zero_add, neg_mul]

    have :
        x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2 ↔
        -(Real.sin θ * l) / 2 ≤ x ∧ x ≤ Real.sin θ * l / 2 := by
        rw [neg_div, and_comm, ←tsub_le_iff_right, zero_sub]

    by_cases h : x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (this.not.mp h)]

  simp_rw [indicator_eq, MeasureTheory.set_integral_indicator measurableSet_Icc, Pi.one_apply]

/--
  Buffon's Needle, the short case (`l ≤ d`). The probability of the needle crossing a line equals `(2 * l) / (d * π)`.
-/
theorem buffon_short (h : l ≤ d) : ℙ[N l B] = (2 * l) * (d * π)⁻¹ := by
  simp_rw [
    buffon_integral d l hd B hBₘ hB,
    short_needle_inter_eq d l hl h _,
    MeasureTheory.set_integral_const,
    Real.volume_Icc,
    smul_eq_mul,
    mul_one,
  ]

  rw [mul_comm, mul_eq_mul_right_iff]
  apply Or.inl
  ring_nf

  have : ∀ θ ∈ Set.Icc 0 π, θ.sin * l ≥ 0 := by
    intro θ hθ
    exact mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le

  rw [set_integral_toReal_ofReal measurableSet_Icc this]

  conv in (_ * l) => rw [← smul_eq_mul]
  simp_rw [integral_smul_const, smul_eq_mul, mul_comm, mul_eq_mul_left_iff]
  apply Or.inl

  rw [
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_sin,
    Real.cos_zero,
    Real.cos_pi
  ]

  ring_nf

lemma min_sin_mul_continuous : Continuous (fun (θ : ℝ) => min d (θ.sin * l)) := by
  apply Continuous.min continuous_const
  apply Continuous.mul Real.continuous_sin continuous_const

lemma integral_min_eq_two_mul : ∫ θ in (0)..π, min d (θ.sin * l) = 2 * ∫ θ in (0)..π/2, min d (θ.sin * l) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2) (c := π)]
  conv => lhs; arg 2; arg 1; intro θ; rw [← neg_neg θ, Real.sin_neg]

  simp_rw [
    intervalIntegral.integral_comp_neg fun θ => min d (-θ.sin * l),
    ← Real.sin_add_pi,
    intervalIntegral.integral_comp_add_right (fun θ => min d (θ.sin * l)),
    add_left_neg,
    (by ring : -(π/2) + π = π/2),
    two_mul,
  ]

  all_goals
    exact Continuous.intervalIntegrable (min_sin_mul_continuous d l) _ _

lemma integral_zero_to_arcsin_min :
    ∫ θ in (0)..(d / l).arcsin, min d (θ.sin * l) = (1 - (1 - (d / l) ^ 2).sqrt) * l := by
  have : Set.EqOn (fun θ => min d (θ.sin * l)) (fun θ => θ.sin * l) (Set.uIcc 0 (d / l).arcsin) := by
    intro θ ⟨hθ₁, hθ₂⟩
    have arcsin_nonneg : (d / l).arcsin ≥ 0 := Real.arcsin_nonneg.mpr (div_nonneg hd.le hl.le)
    simp only [sup_eq_max, inf_eq_min, min_eq_left arcsin_nonneg, max_eq_right arcsin_nonneg] at hθ₁ hθ₂
    have hθ_mem : θ ∈ Set.Ioc (-(π / 2)) (π / 2) := by
      apply And.intro
      · calc
        -(π / 2) < 0 := neg_lt_zero.mpr (div_pos Real.pi_pos two_pos)
        _        ≤ θ := hθ₁
      · calc
        θ ≤ (d / l).arcsin := hθ₂
        _ ≤ π / 2 := (d / l).arcsin_mem_Icc.right

    have : θ.sin * l ≤ d := (le_div_iff hl).mp ((Real.le_arcsin_iff_sin_le' hθ_mem).mp hθ₂)
    simp_rw [min_eq_right this]

  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_mul_const, integral_sin,
    Real.cos_zero, Real.cos_arcsin]

lemma integral_arcsin_to_pi_div_two_min (h : l ≥ d) :
    ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l) = (π / 2 - (d / l).arcsin) * d := by

  have : Set.EqOn (fun θ => min d (θ.sin * l)) (fun _ => d) (Set.uIcc (d / l).arcsin (π / 2)) := by
    intro θ ⟨hθ₁, hθ₂⟩

    wlog hθ_ne_pi_div_two : θ ≠ π / 2
    · simp only [ne_eq, not_not] at hθ_ne_pi_div_two
      simp only [hθ_ne_pi_div_two, Real.sin_pi_div_two, one_mul, min_eq_left h]

    simp only [sup_eq_max, inf_eq_min, min_eq_left (d / l).arcsin_le_pi_div_two,
      max_eq_right (d / l).arcsin_le_pi_div_two] at hθ₁ hθ₂

    have hθ_mem : θ ∈ Set.Ico (-(π / 2)) (π / 2) := by
      apply And.intro
      · calc
        -(π / 2) ≤ 0 := neg_nonpos.mpr (div_nonneg Real.pi_pos.le zero_le_two)
        _        ≤ (d / l).arcsin := (Real.arcsin_pos.mpr (div_pos hd hl)).le
        _        ≤ θ := hθ₁
      · exact lt_of_le_of_ne hθ₂ hθ_ne_pi_div_two

    have : d ≤ θ.sin * l := (div_le_iff hl).mp ((Real.arcsin_le_iff_le_sin' hθ_mem).mp hθ₁)
    simp_rw [min_eq_left this]

  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const, smul_eq_mul]

/--
  Buffon's Needle, the short case (`l ≥ d`).
-/
theorem buffon_long (h : l ≥ d) :
    ℙ[N l B] = (2 * l) / (d * π) - 2 / (d * π) * ((l^2 - d^2).sqrt + d * (d / l).arcsin) + 1 := by

  simp only [
    buffon_integral d l hd B hBₘ hB, MeasureTheory.integral_const, smul_eq_mul, mul_one,
    MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, Set.Icc_inter_Icc, Real.volume_Icc,
    sup_eq_max, inf_eq_min, min_div_div_right zero_le_two d, max_div_div_right zero_le_two (-d), div_sub_div_same,
    neg_mul, max_neg_neg, sub_neg_eq_add, ← mul_two, mul_div_cancel (min d (Real.sin _ * l)) two_ne_zero
  ]

  have (θ : ℝ) (hθ : θ ∈ Set.Icc 0 π) : min d (θ.sin * l) ≥ 0 := by
    by_cases h : d ≤ θ.sin * l
    · rw [min_eq_left h]; exact hd.le
    · rw [min_eq_right (not_le.mp h).le]; exact mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le

  rw [set_integral_toReal_ofReal measurableSet_Icc this, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le, integral_min_eq_two_mul,
    ← intervalIntegral.integral_add_adjacent_intervals (b := (d / l).arcsin),
    integral_zero_to_arcsin_min d l hd hl,
    integral_arcsin_to_pi_div_two_min d l hd hl h]

  have this₁ : (1 - Real.sqrt (1 - (d / l) ^ 2)) * l = l - (l ^ 2 - d ^ 2).sqrt := by
    rw [mul_comm, mul_sub, mul_one, div_pow, one_sub_div, Real.sqrt_div, Real.sqrt_sq hl.le, ← mul_div_assoc, mul_comm,
      mul_div_cancel _ (ne_of_gt hl)]
    · rw [sub_nonneg]
      apply sq_le_sq.mpr
      rw [abs_of_pos hd, abs_of_pos hl]
      exact h
    · simp only [ne_eq, zero_lt_two, pow_eq_zero_iff]
      exact (ne_of_gt hl)

  have this₂ : 2 * d * (π / 2 - (d / l).arcsin) / (d * π) = 1 - (2 / π) * (d / l).arcsin := by
    rw [mul_sub, sub_div, mul_assoc, ← mul_comm_div, ← mul_assoc, ← mul_comm_div, div_self two_ne_zero, one_mul,
      div_self (ne_of_gt (mul_pos hd Real.pi_pos)), mul_div_assoc, ← mul_comm_div, mul_comm 2,
      mul_div_mul_left _ _ (ne_of_gt hd)]

  have this₃ : 2 * Real.sqrt (l ^ 2 - d ^ 2) / (d * π) = 2 / (d * π) * Real.sqrt (l ^ 2 - d ^ 2) := by ring_nf

  have this₄ : 2 / π * d / d = 2 / (d * π) * d := by ring_nf

  conv =>
    lhs
    rw [this₁, inv_mul_eq_div, mul_add, mul_sub, add_div, sub_div, mul_comm (π / 2 - (d / l).arcsin), ← mul_assoc,
      this₂, this₃, add_sub, add_sub_right_comm, sub_eq_add_neg, sub_eq_add_neg, ← neg_mul,
      ← mul_div_cancel (2 / π) (ne_of_gt hd), this₄, mul_assoc, ← neg_mul, add_assoc (2 * l / (d * π)) _ _,
      ← mul_add, neg_mul, ← sub_eq_add_neg]

  all_goals
    exact Continuous.intervalIntegrable (min_sin_mul_continuous d l) _ _
