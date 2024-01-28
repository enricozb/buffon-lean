import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Probability.Density
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory ProbabilityTheory

set_option quotPrecheck false
notation "π" => Real.pi
notation X " ~ " "Unif[" s "]" => MeasureTheory.pdf.IsUniform X s ℙ

/- Probability theory variables. -/
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

namespace Playground

variable (X : Ω → ℝ) (hX : X ~ Unif[Set.Icc 0 1])

example : 𝔼[X] = 1 / 2 := by
  rw [hX.integral_eq, ← set_integral_congr_set_ae Ioc_ae_eq_Icc,
    ← intervalIntegral.integral_of_le zero_le_one]
  all_goals simp

example : ∫ θ in (-π/2)..(π/2), ∫ _ in (-d/2)..(d/2), (1 : ℝ) = π * d := by
  simp
  ring

lemma pi_le_two_pi : π ≤ 2 * π := by sorry

example : ∫ θ in (-π/2)..(π/2), ∫ _ in (-d/2 * θ.cos)..(d/2 * θ.cos), (1 : ℝ) = 2 * d := by
  conv => lhs; arg 1; intro θ; simp; rw [neg_div, neg_mul, sub_neg_eq_add]; ring_nf
  simp
  rw [Real.sin_half_eq_neg_sqrt]
  · simp; ring_nf
  · norm_num; exact pi_le_two_pi
  · simp; exact le_of_lt Real.pi_pos

end Playground

/- Probability theory variables. -/
variable {Ω : Type _} [hΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable
  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l: ℝ)
  (hd : d > 0)
  (hl : l > 0)

  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hB : Measurable B)
  /- `B` is uniformly distributed on `[-d/2, d/2] × [-π/2, π/2]`. -/
  (hBₘ : pdf.IsUniform B (Set.Icc (-d/2) (d/2) ×ˢ Set.Icc (-π/2) (π/2)) ℙ)

abbrev X_def : Ω → ℝ := fun ω ↦ (B ω).1
abbrev Θ_def : Ω → ℝ := fun ω ↦ (B ω).2

notation "X" => X_def B
notation "Θ" => Θ_def B

notation "X_measurable" => Measurable.fst hB
notation "X_aemeasurable" => Measurable.aemeasurable X_measurable
notation "Θ_measurable" => Measurable.snd hB
notation "Θ_aemeasurable" => Measurable.aemeasurable Θ_measurable

lemma X_uniform_def : X ~ Unif[Set.Icc (-d/2) (d/2)] := by
  simp [pdf.IsUniform]
lemma Θ_uniform_def : Θ ~ Unif[Set.Icc (-π/2) (π/2)] := by sorry

notation "X_uniform" => X_uniform_def d B
notation "Θ_uniform" => Θ_uniform_def d B

/--
  Projection of a needle onto the x-axis. The needle's center is at
  x-coordinate `x`, of length `l` and angle `θ`. Note, `θ` is measured
  relative to the y-axis, that is, a vertical needle has `θ = 0`.
-/
def needle_set (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * d / 2) (x + θ.sin * d / 2)

/-- Random variable representing whether a needle crosses a line. -/
noncomputable def N (ω : Ω) : ℝ := Set.indicator {ω | 0 ∈ needle_set d (X ω) (Θ ω)} 1 ω

/-- Short case, where `l < d`. -/
theorem buffon_short (hlₛ : l < d) : 𝔼[N d B] = 2 * l / (π * d) := by
  unfold N needle_set
  rw [MeasureTheory.integral_indicator_one ?measurable]
  simp

  case measurable =>
    simp
    conv => arg 1; intro ω; rw [and_comm]; lhs; rw [add_comm, ←sub_le_iff_le_add', zero_sub]
    conv => arg 1; intro ω; rw [←Set.mem_Icc]



  have : {ω | X ω ≤ Real.sin (Θ ω) * l / 2 ∧ 0 ≤ X ω + Real.sin (Θ ω) * l / 2} =
    {ω | X ω ≤ Real.sin (Θ ω) * l / 2} ∩ {ω | 0 ≤ X ω + Real.sin (Θ ω) * l / 2} := sorry
  rw [this]




