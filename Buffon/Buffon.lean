import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Probability.Density
import Mathlib.Probability.Notation

open MeasureTheory ProbabilityTheory Measure

set_option quotPrecheck false
notation "π" => Real.pi

/- Probability theory variables. -/
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/- Buffon's needle variables. -/
variable
  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : d > 0)
  (hl : l > 0)

  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)

  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)

lemma B_range_volume : ℙ (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) = ENNReal.ofReal (d * π) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp only [Real.volume_Icc]
  ring_nf
  exact (ENNReal.ofReal_mul (le_of_lt hd)).symm

instance hB_PDF : HasPDF B ℙ := by
  apply MeasureTheory.pdf.IsUniform.hasPDF ?mes ?top ?zero hB
  case top =>
    rw [B_range_volume d hd]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, gt_iff_lt]
    exact mul_pos hd Real.pi_pos
  case zero =>
    rw [B_range_volume d hd]
    simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  case mes =>
    simp only [ge_iff_le, not_le, gt_iff_lt, Set.Icc_prod_Icc, Prod.mk_le_mk, not_and, Prod.mk_lt_mk,
      measurableSet_Icc]

abbrev X_def : Ω → ℝ := fun ω ↦ (B ω).1
abbrev Θ_def : Ω → ℝ := fun ω ↦ (B ω).2

notation "X" => X_def B
notation "Θ" => Θ_def B

/--
  Projection of a needle onto the x-axis. The needle's center is at
  x-coordinate `x`, of length `l` and angle `θ`. Note, `θ` is measured
  relative to the y-axis, that is, a vertical needle has `θ = 0`.
-/
def needle_set (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

noncomputable def N' : (ℝ × ℝ) → ℝ := fun ⟨x, θ⟩ => by
  haveI : Decidable (0 ∈ needle_set l x θ) := Classical.dec _
  exact if 0 ∈ needle_set l x θ then 1 else 0

lemma N'_eq (x θ : ℝ) : N' l (x, θ) = Set.indicator (Set.Icc (-l * θ.sin / 2) (l * θ.sin / 2)) 1 x := by
  simp only [N', needle_set]
  by_cases hx : x ∈ (Set.Icc (-l * θ.sin / 2) (l * θ.sin / 2))
  · rw [Set.indicator_of_mem hx]
    simp; simp at hx
    apply And.intro; all_goals linarith
  · rw [Set.indicator_of_not_mem hx]
    have : 0 ∉ Set.Icc (x - Real.sin θ * l / 2) (x + Real.sin θ * l / 2) := by
      intro hz
      simp at hz
      rw [mul_comm, and_comm, add_comm, ←sub_le_iff_le_add', _root_.zero_sub] at hz
      rw [Set.mem_Icc, neg_mul, neg_div] at hx
      exact hx hz
    rw [if_neg this]

/-- Random variable representing whether a needle crosses a line. -/
noncomputable def N_def : Ω → ℝ := (N' l ∘ B)
notation "N" => N_def l B

#check (HSMul NNReal ℝ ℝ)

-- lemma indicator_ennreal (hc : c ≠ 0) : Set.indicator s ((ENNReal.ofReal c)⁻¹ • 1) = ENNReal.ofReal ∘ (Set.indicator s 1) := by sorry
lemma indicator_ennreal' (hc : c ≥ 0) : Set.indicator s ((ENNReal.ofReal c)⁻¹ • 1) = fun x => ENNReal.ofNNReal (Set.indicator s (fun x => ⟨c, hc⟩⁻¹) x) := by sorry
lemma indicator_nnreal (s : Set (ℝ × ℝ)) (x θ c : ℝ) (hc : c ≥ 0) :
  Set.indicator s (fun x => ⟨c, hc⟩⁻¹ : ℝ × ℝ → NNReal) (x, y) • N' l (x, θ) =
  Set.indicator s (fun x => c⁻¹ : ℝ × ℝ → ℝ) (x, y) * N' l (x, θ) := by sorry

lemma indicator_prod :
  Set.indicator
    (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π)
    (fun a => (d * π)⁻¹ * N' l a)
    (x, θ) =
  (d * π)⁻¹ * Set.indicator
    (Set.Icc 0 π)
    (fun θ => Set.indicator (Set.Icc (-d / 2) (d / 2)) (N' l ⟨·, θ⟩) x)
    θ := by sorry

lemma d_pi_pos : d * π ≥ 0 := by sorry
lemma d_pi_inv_neq_zero : (d * π)⁻¹ ≠ 0 := by sorry

lemma Real_measure_prod : (ℙ : Measure (ℝ × ℝ)) = Measure.prod (ℙ : Measure ℝ) (ℙ : Measure ℝ) := rfl

lemma X_space_measurable : MeasurableSet (Set.Icc (-d / 2) (d / 2)) := by sorry
lemma Θ_space_measurable : MeasurableSet (Set.Icc 0 π) := by sorry

lemma l_sin_pos (l θ : ℝ) (hl : l ≥ 0) : l * θ.sin ≥ 0 := by sorry

lemma buffon_short_inter (d l θ : ℝ) (h : l ≤ d) :
  Set.Icc (-(l * Real.sin θ) / 2) (l * Real.sin θ / 2) ∩ Set.Icc (-d / 2) (d / 2) =
  Set.Icc (-(l * Real.sin θ) / 2) (l * Real.sin θ / 2) := by sorry

theorem buffon_short (h : l ≤ d) : 𝔼[N] = (2 * l) * (d * π)⁻¹ := by

  haveI : HasPDF B ℙ := hB_PDF d hd B hB
  unfold N_def
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  have : ∀ ω, ENNReal.ofReal ((N' l ∘ B) ω) = ((ENNReal.ofReal ∘ (N' l)) ∘ B) ω  := by intro ω; rfl
  conv => lhs; arg 1; arg 2; intro ω; rw [this ω]
  rw [MeasureTheory.lintegral_comp]
  simp only [Function.comp_apply, Pi.mul_apply]
  rw [←MeasureTheory.ofReal_integral_eq_lintegral_ofReal, ENNReal.toReal_ofReal]
  rw [MeasureTheory.map_eq_withDensity_pdf B ℙ]
  rw [MeasureTheory.withDensity_congr_ae (MeasureTheory.pdf.IsUniform.pdf_eq _ ?zero ?top hB)]
  rw [B_range_volume d hd]
  rw [Real_measure_prod]
  rw [indicator_ennreal' (d_pi_pos d)]
  rw [integral_withDensity_eq_integral_smul ?mes (N' l)]
  rw [integral_prod]

  conv =>
    lhs; arg 2; intro x; arg 2; intro θ;
    rw [indicator_nnreal]
    rw [←Set.indicator_mul_left]
    simp only [Pi.one_apply, one_mul]
    rw [indicator_prod]

  conv => lhs; arg 2; intro x; arg 2; intro θ; rw [mul_comm, ← smul_eq_mul]
  conv => lhs; arg 2; intro x; rw [integral_smul_const]
  rw [integral_smul_const, smul_eq_mul]
  apply mul_eq_mul_right_iff.mpr
  apply (or_iff_left (d_pi_inv_neq_zero d)).mpr

  conv => lhs; arg 2; intro x; rw [integral_indicator Θ_space_measurable]
  rw [MeasureTheory.integral_integral, MeasureTheory.integral_prod_symm]
  simp only [ge_iff_le, not_le, gt_iff_lt, Set.mem_Icc, not_and]
  conv => lhs; arg 2; intro θ; rw [integral_indicator (X_space_measurable d)]

  conv => lhs; arg 2; intro θ; arg 2; intro x; rw [N'_eq l x θ]
  simp

  /-
    The next line is the first use of `h : l ≤ d`. Everything prior should work
    without this restriction.

    The current goal is:
      ∫ (θ : ℝ) in Set.Icc (-π / 2) (π / 2),
        ENNReal.toReal (↑↑ℙ (
          Set.Icc (-(l * Real.sin θ) / 2) (l * Real.sin θ / 2) ∩ Set.Icc (-d / 2) (d / 2)
        ))
        ∂ℙ = 2 * l

    Which looks like a pretty manageable form.
  -/

  conv => lhs; arg 2; intro θ; rw [buffon_short_inter d l θ h]

  simp
  conv => lhs; ring_nf

  conv => lhs; arg 2; intro θ; rw [ENNReal.toReal_ofReal sorry]
  conv => lhs; arg 2; intro θ; rw [mul_comm]
  rw [← set_integral_congr_set_ae Ioc_ae_eq_Icc]
  rw [← intervalIntegral.integral_of_le]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_sin]
  simp
  norm_num
