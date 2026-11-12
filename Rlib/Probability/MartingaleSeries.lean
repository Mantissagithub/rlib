module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Weighted sums of bounded martingale differences

Bounded noise with zero conditional mean, weighted by square-summable coefficients, has almost
surely convergent partial sums. This is the probabilistic step in stochastic approximation.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Rlib

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {w : ℕ → Ω → ℝ} {α : ℕ → ℝ} {C : ℝ}

/-- Bounded noise that is known at the next time and has zero conditional mean given the
current time, weighted by square-summable coefficients, has almost surely convergent partial
sums. -/
theorem ae_tendsto_sum_mul_of_condExp_eq_zero
    (hmeas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (w n))
    (hbdd : ∀ n, ∀ᵐ ω ∂μ, |w n ω| ≤ C)
    (hmean : ∀ n, μ[w n | ℱ n] =ᵐ[μ] 0)
    (hα : Summable fun n => α n ^ 2) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ k ∈ Finset.range n, α k * w k ω) atTop (𝓝 c) := by
  set M : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, α k * w k ω
  set B : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, |α k| * C
  have hall : ∀ᵐ ω ∂μ, ∀ n, |w n ω| ≤ C := ae_all_iff.2 hbdd
  have hbound {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (b : ℝ)
      (hb : ∀ᵐ ω ∂μ, |f ω| ≤ b) : Integrable f μ :=
    Integrable.of_bound hf b (by simpa [Real.norm_eq_abs] using hb)
  have hMsm (n : ℕ) : StronglyMeasurable[ℱ n] (M n) :=
    Finset.stronglyMeasurable_fun_sum _ fun k hk =>
      ((hmeas k).mono (ℱ.mono (by simpa using hk : k + 1 ≤ n))).const_mul (α k)
  have hwae (n : ℕ) : AEStronglyMeasurable (w n) μ :=
    ((hmeas n).mono (ℱ.le _)).aestronglyMeasurable
  have hMae (n : ℕ) : AEStronglyMeasurable (M n) μ :=
    ((hMsm n).mono (ℱ.le _)).aestronglyMeasurable
  have hMb (n : ℕ) : ∀ᵐ ω ∂μ, |M n ω| ≤ B n := by
    filter_upwards [hall] with ω h
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h k) (abs_nonneg _)
  have hwi (n : ℕ) : Integrable (w n) μ := hbound (hwae n) C (hbdd n)
  have hMi (n : ℕ) : Integrable (M n) μ := hbound (hMae n) (B n) (hMb n)
  have hMwi (n : ℕ) : Integrable (M n * w n) μ := by
    refine hbound ((hMae n).mul (hwae n)) (B n * C) ?_
    filter_upwards [hMb n, hbdd n] with ω h1 h2
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hM2i (n : ℕ) : Integrable (fun ω => M n ω ^ 2) μ := by
    refine hbound ((hMae n).pow 2) (B n ^ 2) ?_
    filter_upwards [hMb n] with ω h
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hw2i (n : ℕ) : Integrable (fun ω => w n ω ^ 2) μ := by
    refine hbound ((hwae n).pow 2) (C ^ 2) ?_
    filter_upwards [hbdd n] with ω h
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hmart : Martingale M ℱ μ := by
    refine martingale_of_condExp_sub_eq_zero_nat (fun n => hMsm n) hMi fun n => ?_
    have hdiff : M (n + 1) - M n = α n • w n := by
      funext ω
      simp [M, Finset.sum_range_succ]
    rw [hdiff]
    refine (condExp_smul _ _ _).trans ?_
    filter_upwards [hmean n] with ω h
    simp [h]
  have hcross (n : ℕ) : ∫ ω, M n ω * w n ω ∂μ = 0 := by
    calc
      ∫ ω, M n ω * w n ω ∂μ = ∫ ω, (μ[M n * w n | ℱ n]) ω ∂μ :=
        (integral_condExp (ℱ.le n)).symm
      _ = ∫ ω, (M n * μ[w n | ℱ n]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left (hMsm n) (hMwi n) (hwi n))
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hmean n] with ω h
        simp [h]
  have hw2 (n : ℕ) : ∫ ω, w n ω ^ 2 ∂μ ≤ C ^ 2 := by
    calc
      ∫ ω, w n ω ^ 2 ∂μ ≤ ∫ _, C ^ 2 ∂μ := by
        refine integral_mono_ae (hw2i n) (integrable_const _) ?_
        filter_upwards [hbdd n] with ω h
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = C ^ 2 := by simp
  have hsq (n : ℕ) : ∫ ω, M n ω ^ 2 ∂μ ≤ C ^ 2 * ∑ k ∈ Finset.range n, α k ^ 2 := by
    induction n with
    | zero => simp [M]
    | succ n ih =>
      have hexp : (fun ω => M (n + 1) ω ^ 2) = fun ω =>
          (M n ω ^ 2 + 2 * α n * (M n ω * w n ω)) + α n ^ 2 * w n ω ^ 2 := by
        funext ω
        simp only [M, Finset.sum_range_succ]
        ring
      have hcrossi : Integrable (fun ω => 2 * α n * (M n ω * w n ω)) μ :=
        (hMwi n).const_mul (2 * α n)
      have hfirst : Integrable (fun ω => M n ω ^ 2 + 2 * α n * (M n ω * w n ω)) μ :=
        (hM2i n).add hcrossi
      have hlast : Integrable (fun ω => α n ^ 2 * w n ω ^ 2) μ := (hw2i n).const_mul _
      rw [hexp, integral_add hfirst hlast,
        integral_add (hM2i n) hcrossi, integral_const_mul, integral_const_mul, hcross n,
        Finset.sum_range_succ]
      nlinarith [mul_le_mul_of_nonneg_left (hw2 n) (sq_nonneg (α n))]
  have hL1 (n : ℕ) :
      eLpNorm (M n) 1 μ ≤ ENNReal.ofReal ((1 + C ^ 2 * ∑' k, α k ^ 2) / 2) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hMi n)]
    apply ENNReal.ofReal_le_ofReal
    have hS : ∑ k ∈ Finset.range n, α k ^ 2 ≤ ∑' k, α k ^ 2 :=
      hα.sum_le_tsum _ fun k _ => sq_nonneg (α k)
    calc
      ∫ ω, ‖M n ω‖ ∂μ ≤ ∫ ω, (1 + M n ω ^ 2) / 2 ∂μ := by
        refine integral_mono (hMi n).norm (((integrable_const 1).add (hM2i n)).div_const 2)
          fun ω => ?_
        rw [Real.norm_eq_abs]
        nlinarith [sq_abs (M n ω), sq_nonneg (|M n ω| - 1)]
      _ = (1 + ∫ ω, M n ω ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add (integrable_const 1) (hM2i n)]
        simp
      _ ≤ (1 + C ^ 2 * ∑' k, α k ^ 2) / 2 := by
        nlinarith [hsq n, mul_le_mul_of_nonneg_left hS (sq_nonneg C)]
    exact hMae n
  exact hmart.submartingale.exists_ae_tendsto_of_bdd hL1

end Rlib
