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
def needle_proj_x (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/--
  A random variable representing whether the needle crosses a line.

  The line is at `x = 0`, and the needle crosses the line if it's projection
  onto the x-axis contains `0`. This random variable is `1` if the needle
  crosses the line, and `0` otherwise.

  Note: `N : Ω → ℝ` is the random variable; the definition of `N' : ℝ × ℝ` is
  provided for convenience.
-/
noncomputable def N' (p : ℝ × ℝ) : ℝ := Set.indicator (needle_proj_x l p.1 p.2) 1 0
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
      by_cases hp : 0 ∈ needle_proj_x l p.1 p.2
      · simp_rw [Set.indicator_of_mem hp, Pi.one_apply] at hxp
        apply Or.inr hxp.symm
      · simp_rw [Set.indicator_of_not_mem hp] at hxp
        apply Or.inl hxp.symm

lemma N'_integrable : MeasureTheory.Integrable (N' l) := by
  let B_range_indicator (p : ℝ × ℝ) : ℝ := Set.indicator ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) 1 p
  have N'_nonneg p : N' l p ≥ 0 := by sorry
  have N'_bound p : N' l p ≤ B_range_indicator p := by sorry
  have N'_bound' p :
      ENNReal.ofReal (N' l p) ≤ ENNReal.ofReal (B_range_indicator p) :=
    ENNReal.ofReal_le_ofReal (N'_bound p)

  apply And.intro (N'_strongly_measurable l).aestronglyMeasurable
  · apply (MeasureTheory.hasFiniteIntegral_iff_norm (N' l)).mpr
    simp_rw [Real.norm_of_nonneg (N'_nonneg _)]

    have : ∫⁻ (a : ℝ × ℝ), ENNReal.ofReal (N' l a) ≤ ∫⁻ (a : ℝ × ℝ), ENNReal.ofReal (B_range_indicator a) :=
      MeasureTheory.lintegral_mono N'_bound'

    have : ∫⁻ (a : ℝ × ℝ), ENNReal.ofReal (B_range_indicator a) = ENNReal.ofReal (d * π) := by
      unfold_let B_range_indicator
      simp_rw [← Function.comp_apply (f := ENNReal.ofReal), ← Set.indicator_comp_of_zero ENNReal.ofReal_zero]
      rw [MeasureTheory.lintegral_indicator (ENNReal.ofReal ∘ 1)]
      simp_rw [Function.comp_apply, Pi.one_apply, ENNReal.ofReal_one, MeasureTheory.set_lintegral_const, one_mul,
        B_range_volume d hd]

      exact measurableSet_prod.mpr (Or.inl ⟨measurableSet_Icc, measurableSet_Icc⟩)

    sorry

lemma N'_integrable_prod :
    MeasureTheory.Integrable (N' l)
      (Measure.prod (Measure.restrict ℙ (Set.Icc (-d / 2) (d / 2))) (Measure.restrict ℙ (Set.Icc 0 π))) := by

  rw [MeasureTheory.Measure.prod_restrict]
  apply MeasureTheory.Integrable.restrict
  exact N'_integrable d l hd

theorem buffon_short (h : l ≤ d) : 𝔼[N l B] = (2 * l) * (d * π)⁻¹ := by
  simp_rw [N, Function.comp_apply]

  rw [
    ← MeasureTheory.integral_map (f := N' l) hBₘ.aemeasurable (N'_strongly_measurable l).aestronglyMeasurable,
    hB,
    MeasureTheory.integral_smul_measure,
    B_range_volume d hd,
    ENNReal.ofReal_inv_of_pos (mul_pos hd Real.pi_pos),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hd.le Real.pi_pos.le)),
    smul_eq_mul, mul_comm, mul_eq_mul_right_iff
  ]

  apply Or.inl

  rw [
    (by rfl : (ℙ : Measure (ℝ × ℝ)) = Measure.prod ℙ ℙ),
    MeasureTheory.set_integral_prod _ (N'_integrable d l hd).integrableOn,
    MeasureTheory.integral_integral_swap ?integrable,
  ]

  case integrable =>
    simp_rw [Function.uncurry_def, Prod.mk.eta]
    exact N'_integrable_prod d l hd

  /-
    ⊢ ∫ (y : ℝ) in Set.Icc 0 π,
      ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2),
        N' (x, y) = 2 * l
  -/

  unfold N' needle_proj_x
  simp only [Set.mem_Icc]

  have indicator_eq (x θ : ℝ) :
    Set.indicator (Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)) 1 0 =
    Set.indicator (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) (1 : ℝ → ℝ) x := by
    sorry

  simp_rw [
    indicator_eq,
    MeasureTheory.set_integral_indicator measurableSet_Icc,
    -- critically, `hd` is used here, making this the "short" case.
    short_needle_inter_eq d l hl h _,
    Pi.one_apply,
    MeasureTheory.set_integral_const,
    Real.volume_Icc,
    smul_eq_mul,
    mul_one,
  ]

  ring_nf

  have : ∀ θ ∈ Set.Icc 0 π, θ.sin * l ≥ 0 := by
    intro θ hθ
    exact mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le
  rw [set_integral_toReal_ofReal measurableSet_Icc this]

  /-
    ⊢ ∫ (x : ℝ) in Set.Icc 0 π, Real.sin x * l = l * 2
  -/

  conv in (Real.sin _ * l) => rw [← smul_eq_mul]
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
