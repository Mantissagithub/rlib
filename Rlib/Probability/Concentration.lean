module

public import Rlib.Probability.Empirical
public import Mathlib.Probability.Moments.SubGaussian

/-! # Concentration of independent bounded sample means -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Rlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ}

omit [IsProbabilityMeasure μ] in
private theorem measure_sampleMean_ge_le
    {Y : Fin (n + 1) → Ω → ℝ} (hindep : iIndepFun Y μ)
    (hsub : ∀ i, HasSubgaussianMGF (Y i) (1 / 4) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ sampleMean (fun i => Y i ω)} ≤
      Real.exp (-2 * (n + 1 : ℝ) * ε ^ 2) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
    (s := Finset.univ) (fun i _ => hsub i) (mul_nonneg (le_of_lt hn) hε)
  have hevent : {ω | ε ≤ sampleMean (fun i => Y i ω)} =
      {ω | (n + 1 : ℝ) * ε ≤ ∑ i ∈ Finset.univ, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sampleMean, le_div_iff₀ hn]
    rw [mul_comm]
  rw [hevent]
  convert h using 1
  congr 1
  norm_num [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_add, NNReal.coe_natCast]
  field_simp
  ring

/-- Hoeffding's two-sided bound for independent observations in `[0,1]` with a common mean.
Identical distributions are not required. -/
theorem measure_abs_sampleMean_sub_le
    {X : Fin (n + 1) → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {θ : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = θ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |sampleMean (fun i => X i ω) - θ|} ≤
      2 * Real.exp (-2 * (n + 1 : ℝ) * ε ^ 2) := by
  have hsub (i) : HasSubgaussianMGF (fun ω => X i ω - θ) (1 / 4) μ := by
    convert hasSubgaussianMGF_of_mem_Icc (hmeas i) (hbound i) using 1
    · simp only [hmean i]
    · norm_num
  have hu := measure_sampleMean_ge_le
    (hindep.comp (fun _ x => x - θ) (fun _ => by fun_prop)) hsub hε
  have hl := measure_sampleMean_ge_le
    (hindep.comp (fun _ x => -(x - θ)) (fun _ => by fun_prop)) (fun i => (hsub i).neg) hε
  have hcenter (ω) : sampleMean (fun i => X i ω - θ) =
      sampleMean (fun i => X i ω) - θ := by
    simp [sub_eq_add_neg, sampleMean_add]
  have hneg (ω) : sampleMean (fun i => -(X i ω - θ)) =
      -(sampleMean (fun i => X i ω) - θ) := by
    simp only [sampleMean, Finset.sum_neg_distrib, neg_div]
    exact congrArg Neg.neg (hcenter ω)
  simp only [Function.comp_def, hcenter] at hu
  simp only [Function.comp_def, hneg] at hl
  have hevent : {ω | ε ≤ |sampleMean (fun i => X i ω) - θ|} =
      {ω | ε ≤ sampleMean (fun i => X i ω) - θ} ∪
      {ω | ε ≤ -(sampleMean (fun i => X i ω) - θ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith)

/-- Hoeffding's two-sided bound for independent observations bounded by `c` in absolute value
with a common mean. Identical distributions are not required. -/
theorem measure_abs_sampleMean_sub_le_of_abs_le
    {X : Fin (n + 1) → Ω → ℝ} (hindep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ c)
    {θ : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂μ = θ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |sampleMean (fun i => X i ω) - θ|} ≤
      2 * Real.exp (-((n + 1 : ℝ) * ε ^ 2) / (2 * c ^ 2)) := by
  have h2c : 0 < 2 * c := by positivity
  set Y : Fin (n + 1) → Ω → ℝ := fun i ω => (X i ω + c) / (2 * c)
  have hY := measure_abs_sampleMean_sub_le (X := Y)
    (hindep.comp (fun _ x => (x + c) / (2 * c)) (fun _ => by fun_prop))
    (fun i => ((hmeas i).add_const c).div_const (2 * c))
    (fun i => by
      filter_upwards [hbound i] with ω h
      rw [abs_le] at h
      constructor
      · exact div_nonneg (by linarith) h2c.le
      · rw [div_le_one h2c]
        linarith)
    (θ := (θ + c) / (2 * c))
    (fun i => by
      have hint : Integrable (X i) μ :=
        Integrable.of_bound (hmeas i).aestronglyMeasurable c
          (by simpa [Real.norm_eq_abs] using hbound i)
      simp only [Y]
      rw [integral_div, integral_add hint (integrable_const c), hmean i]
      simp)
    (div_nonneg hε h2c.le)
  have hmeanY (ω : Ω) : sampleMean (fun i => Y i ω) - (θ + c) / (2 * c) =
      (sampleMean (fun i => X i ω) - θ) / (2 * c) := by
    simp only [Y, sampleMean, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hevent : {ω | ε ≤ |sampleMean (fun i => X i ω) - θ|} =
      {ω | ε / (2 * c) ≤ |sampleMean (fun i => Y i ω) - (θ + c) / (2 * c)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hmeanY, abs_div, abs_of_pos h2c]
    exact (div_le_div_iff_of_pos_right h2c).symm
  rw [hevent]
  refine hY.trans_eq ?_
  congr 2
  field_simp

end Rlib
