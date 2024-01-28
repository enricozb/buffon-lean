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

/--
  Projection of a needle onto the x-axis. The needle's center is at
  x-coordinate `x`, of length `l` and angle `θ`. Note, `θ` is measured
  relative to the y-axis, that is, a vertical needle has `θ = 0`.
-/
def needle_set (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/-- Random variable representing whether a needle crosses a line. -/
noncomputable def N : (ℝ × ℝ) → ℝ := fun ⟨x, θ⟩ => by
  haveI : Decidable (0 ∈ needle_set l x θ) := Classical.dec _
  exact if 0 ∈ needle_set l x θ then 1 else 0

/- Lemmas that are not specific to Buffon's needle. -/
section general_lemmas

lemma indicator_const (c : ℝ) :
  Set.indicator s (fun x => c) x =
  c * (Set.indicator s 1 x) := by sorry

lemma indicator_prod_left {α β γ : Type _} [Zero γ] {s₁ : Set α} {s₂ : Set β} {f : α × β → γ} {a : α} {b : β} :
  Set.indicator (s₁ ×ˢ s₂) f (a, b) = Set.indicator s₁ (fun a => Set.indicator s₂ (fun b => f ⟨a, b⟩) b) a := by
  simp_rw [Set.indicator]
  by_cases h : (a, b) ∈ s₁ ×ˢ s₂
  · rw [if_pos h, if_pos (Set.mem_prod.mp h).left, if_pos (Set.mem_prod.mp h).right]
  · rw [if_neg h]
    apply Or.elim (not_and_or.mp h)
    · intro ha; rw [if_neg ha]
    · intro hb; rw [if_neg hb, ite_self]

lemma indicator_prod_right {α β γ : Type _} [Zero γ] {s₁ : Set α} {s₂ : Set β} {f : α × β → γ} {a : α} {b : β} :
  Set.indicator (s₁ ×ˢ s₂) f (a, b) = Set.indicator s₂ (fun b => Set.indicator s₁ (fun a => f ⟨a, b⟩) a) b := by
  simp_rw [Set.indicator]
  by_cases h : (a, b) ∈ s₁ ×ˢ s₂
  · rw [if_pos h, if_pos (Set.mem_prod.mp h).left, if_pos (Set.mem_prod.mp h).right]
  · rw [if_neg h]
    apply Or.elim (not_and_or.mp h)
    · intro ha; rw [if_neg ha, ite_self]
    · intro hb; rw [if_neg hb]

lemma integral_prod_eq_set_integrals {s₁ : Set ℝ} {s₂ : Set ℝ} {f : ℝ × ℝ → ℝ}
  (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂)
  (hf : MeasureTheory.IntegrableOn f (s₁ ×ˢ s₂)):
  ∫ (a : ℝ × ℝ), Set.indicator (s₁ ×ˢ s₂) 1 a * f a ∂Measure.prod ℙ ℙ =
  ∫ y in s₂, ∫ x in s₁, f (x, y) := by
  rw [integral_prod_symm]
  simp_rw [indicator_prod_left, mul_comm, Pi.one_apply, ←Pi.one_def]

  conv in (_ * _) => rw [mul_comm]
  simp_rw [← smul_eq_mul, ← Set.indicator_smul_const_apply, Pi.one_apply]

  have (x y : ℝ) :
    Set.indicator s₁ (fun _ => Set.indicator s₂ (fun _ => f (x, y)) y) x =
    Set.indicator s₁ (fun x => Set.indicator s₂ (fun y => f (x, y)) y) x := by rfl

  simp_rw [smul_eq_mul, one_mul]
  conv in (Set.indicator _ _ _) => rw [this]
  simp_rw [integral_indicator hs₁]

  have (x y : ℝ) : Set.indicator s₂ (fun y => f (x, y)) y =
    Set.indicator s₂ (fun _ => f (x, y)) y := by rfl

  simp_rw [this, indicator_const, ← smul_eq_mul, integral_smul_const, smul_eq_mul, ← indicator_const]

  have (y : ℝ) : Set.indicator s₂ (fun _ => ∫ (x : ℝ) in s₁, f (x, y) ∂ℙ) y =
    Set.indicator s₂ (fun y => ∫ (x : ℝ) in s₁, f (x, y) ∂ℙ) y := by rfl

  simp_rw [this, integral_indicator hs₂, mul_comm, ←indicator_const]
  exact (MeasureTheory.integrable_indicator_iff (MeasurableSet.prod hs₁ hs₂)).mpr hf

end general_lemmas

section lemmas₁

lemma N_eq (x θ : ℝ) : N l (x, θ) = Set.indicator (Set.Icc (-l * θ.sin / 2) (l * θ.sin / 2)) 1 x := by
  simp only [N, needle_set]
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

lemma N_pos (p : ℝ × ℝ) : N l p ≥ 0 := by
  simp_rw [N]
  by_cases h : 0 ∈ needle_set l p.1 p.2
  · rw [if_pos h]; exact zero_le_one
  · rw [if_neg h]

lemma N_measurable : Measurable (N l) := by sorry

lemma B_range_volume : ℙ (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) = ENNReal.ofReal (d * π) := by
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  simp only [Real.volume_Icc]
  ring_nf
  exact (ENNReal.ofReal_mul (le_of_lt hd)).symm

instance instBHasPDF : HasPDF B ℙ := by
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

lemma indicator_ofReal_inv_eq (hc : c ≥ 0) :
  Set.indicator s ((ENNReal.ofReal c)⁻¹ • 1) =
  fun x => ENNReal.ofNNReal (Set.indicator s (fun x => ⟨c, hc⟩⁻¹) x) := by sorry

lemma indicator_NNReal_smul_eq (s : Set α) (c₁ c₂ : ℝ) (hc₁ : c₁ ≥ 0) :
  Set.indicator s (fun x => ⟨c₁, hc₁⟩⁻¹ : α → NNReal) a • c₂ =
  Set.indicator s (fun x => c₁⁻¹ : α → ℝ) a * c₂ := by sorry

lemma mul_pi_ge_zero (r : ℝ) (hr : r ≥ 0) : r * π ≥ 0 := by sorry
lemma mul_pi_ne_zero (r : ℝ) (hr : r ≠ 0) : (r * π)⁻¹ ≠ 0 := by sorry

lemma Real_measure_prod : (ℙ : Measure (ℝ × ℝ)) = Measure.prod (ℙ : Measure ℝ) (ℙ : Measure ℝ) := rfl

lemma X_space_measurable : MeasurableSet (Set.Icc (-d / 2) (d / 2)) := measurableSet_Icc
lemma Θ_space_measurable : MeasurableSet (Set.Icc 0 π) := measurableSet_Icc

lemma buffon_short_inter (d l θ : ℝ) (h : l ≤ d) :
  Set.Icc (-(l * Real.sin θ) / 2) (l * Real.sin θ / 2) ∩ Set.Icc (-d / 2) (d / 2) =
  Set.Icc (-(l * Real.sin θ) / 2) (l * Real.sin θ / 2) := by sorry

end lemmas₁

-- Lemmas that are clear(er) steps in the proof.
section lemmas₂
  lemma N_expectation_eq_prod_integral : 𝔼[N l ∘ B] = ∫ (x : ℝ × ℝ), N l x ∂map B ℙ := by
    have N_ae_pos₁ : 0 ≤ᶠ[ae ℙ] (N l ∘ B) := by
      unfold Filter.EventuallyLE
      simp only [Pi.zero_apply, Function.comp_apply]
      apply Filter.eventually_of_forall
      exact fun ω => N_pos l (B ω)

    have N_ae_pos₂ : 0 ≤ᶠ[ae (map B ℙ)] N l := by
      unfold Filter.EventuallyLE
      simp only [Pi.zero_apply, ge_iff_le]
      apply Filter.eventually_of_forall
      exact N_pos l

    /-
      TODO: I have no idea if this is true.
      - I don't know what almost-everywhere strongly measurable means.
      - However, the range of `(N l ∘ B)` is a closed set in `R`, and it's a
        simple shape in 2D space so hopefully its "niceness" is sufficient.

      - Actually I think this is true because I think `Integrable N l` is true,
        and integrability implies this.
    -/
    have ae_strongly_measurable : AEStronglyMeasurable (N l ∘ B) ℙ := by sorry
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae N_ae_pos₁ ae_strongly_measurable]

    have ofReal_comp : ∀ ω, ENNReal.ofReal ((N l ∘ B) ω) = ((ENNReal.ofReal ∘ (N l)) ∘ B) ω  := fun ω => rfl
    conv => lhs; arg 1; arg 2; intro ω; rw [ofReal_comp ω]

    have N_measurable' : Measurable (ENNReal.ofReal ∘ N l) :=
      Measurable.comp ENNReal.measurable_ofReal (N_measurable l)
    rw [MeasureTheory.lintegral_comp N_measurable' hBₘ]
    simp only [Function.comp_apply, Pi.mul_apply]

    have N_integral_pos : 0 ≤ ∫ (x : ℝ × ℝ), N l x ∂map B ℙ :=
      MeasureTheory.integral_nonneg (N_pos l)

    have N_integrable : Integrable (N l) (map B ℙ) := by sorry
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal N_integrable N_ae_pos₂,
      ENNReal.toReal_ofReal N_integral_pos]

  lemma N_integral_eq_indicator_integral : ∫ (x : ℝ × ℝ), N l x ∂map B ℙ =
    (d * π)⁻¹ * (∫ (a : ℝ × ℝ), Set.indicator (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) 1 a * N l a ∂Measure.prod ℙ ℙ) := by
    haveI : HasPDF B ℙ := instBHasPDF d hd B hB
    rw [MeasureTheory.map_eq_withDensity_pdf B ℙ]
    rw [MeasureTheory.withDensity_congr_ae (MeasureTheory.pdf.IsUniform.pdf_eq _ ?zero ?top hB)]
    rw [B_range_volume d hd]
    rw [Real_measure_prod]
    rw [indicator_ofReal_inv_eq (mul_pi_ge_zero d (le_of_lt hd))]
    rw [integral_withDensity_eq_integral_smul ?mes (N l)]
    simp_rw [indicator_NNReal_smul_eq, indicator_const, mul_assoc]

    conv => lhs; arg 2; intro p; rw [mul_comm, ← smul_eq_mul]
    rw [integral_smul_const, smul_eq_mul, mul_comm]

    all_goals sorry

end lemmas₂

theorem buffon_short (h : l ≤ d) : 𝔼[N l ∘ B] = (2 * l) * (d * π)⁻¹ := by
  -- ∫ (a : Ω), (N l ∘ B) a = 2 * l * (d * π)⁻¹
  rw [N_expectation_eq_prod_integral l B hBₘ]
  rw [N_integral_eq_indicator_integral d l hd B hB]

  rw [mul_comm]
  apply mul_eq_mul_right_iff.mpr
  apply (or_iff_left (mul_pi_ne_zero d (ne_of_lt hd).symm)).mpr

  have : IntegrableOn (N l) ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) := by sorry

  simp_rw [integral_prod_eq_set_integrals (X_space_measurable d) Θ_space_measurable this, N_eq]

  have : ∀ θ, MeasurableSet (Set.Icc (-l * Real.sin θ / 2) (l * Real.sin θ / 2)) := by sorry

  conv => lhs; arg 2; intro θ; rw [integral_indicator (this θ)]
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

  all_goals sorry
