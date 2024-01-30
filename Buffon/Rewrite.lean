import Mathlib.Probability.Density
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals

open MeasureTheory (MeasureSpace IsProbabilityMeasure pdf.IsUniform Measure)
open ProbabilityTheory

lemma set_integral_toReal_ofReal [MeasureSpace α] {s : Set α} {f : α → ℝ}
    (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x ≥ 0) :
    ∫ (x : α) in s, ENNReal.toReal (ENNReal.ofReal (f x)) = ∫ (x : α) in s, f x := by

  have comp_eq : (fun x => ENNReal.toReal (ENNReal.ofReal (f x))) = (ENNReal.toReal ∘ ENNReal.ofReal ∘ f) := by rfl
  simp_rw [comp_eq]

  have eq_on : Set.EqOn (ENNReal.toReal ∘ ENNReal.ofReal ∘ f) f s := by
    intro x hx
    simp only [Function.comp_apply, ENNReal.toReal_ofReal_eq_iff]
    exact hf x hx

  rw [MeasureTheory.set_integral_congr hs eq_on]

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
-/
noncomputable def N : Ω → ℝ :=
  fun ω =>
    match B ω with
    | ⟨x, θ⟩ => Set.indicator (needle_proj_x l x θ) 1 0

lemma needle_measurable (θ : ℝ) :
    MeasurableSet (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) := by
  sorry

lemma short_needle_inter_eq (h : l ≤ d)  (θ : ℝ) :
    Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) =
    Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) := by
  sorry

abbrev B_range := Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π

lemma B_range_volume : ℙ (B_range d) = ENNReal.ofReal (d * π) := by
  simp_rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_Icc]
  ring_nf
  exact (ENNReal.ofReal_mul hd.le).symm

lemma B_range_nonzero : ℙ (B_range d) ≠ 0 := by sorry
lemma B_range_nontop : ℙ (B_range d) ≠ ⊤ := by sorry
lemma B_range_measurable : MeasurableSet (B_range d) :=
  MeasurableSet.prod measurableSet_Icc measurableSet_Icc

instance instBHasPDF : MeasureTheory.HasPDF B ℙ :=
  MeasureTheory.pdf.IsUniform.hasPDF
    (B_range_measurable d) (B_range_nonzero d) (B_range_nontop d) hB

theorem buffon_short (h : l ≤ d) : 𝔼[N l B] = (2 * l) * (d * π)⁻¹ := by
  let N' (p : ℝ × ℝ) : ℝ := Set.indicator (needle_proj_x l p.1 p.2) 1 0

  unfold N
  rw [
    ← MeasureTheory.integral_map (f := N') hBₘ.aemeasurable,
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
    MeasureTheory.set_integral_prod,
    MeasureTheory.integral_integral_swap,
  ]

  /-
    ⊢ ∫ (y : ℝ) in Set.Icc 0 π,
      ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2),
        N' (x, y) = 2 * l
  -/

  unfold_let N'
  unfold needle_proj_x
  simp only [Set.mem_Icc]

  have indicator_eq (x θ : ℝ) :
    Set.indicator (Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)) 1 0 =
    Set.indicator (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) (1 : ℝ → ℝ) x := by
    sorry

  have Θ_range_measurable : MeasurableSet (Set.Icc (-d / 2) (d / 2)) :=
    measurableSet_Icc

  simp_rw [
    indicator_eq,
    MeasureTheory.set_integral_indicator (needle_measurable l _),
    -- critically, `hd` is used here, making this the "short" case.
    short_needle_inter_eq d l h _,
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

  all_goals sorry
