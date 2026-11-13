module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic

/-! # Real expectation on finite types -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Rlib

variable {X : Type*} [Fintype X]

/-- The real probabilities of a finite probability mass function sum to one. -/
theorem probability_sum (p : PMF X) : ∑ x, (p x).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x),
    ← tsum_fintype (L := .unconditional X), p.tsum_coe, ENNReal.toReal_one]

/-- The expectation of a real function under a finite probability mass function. -/
def expect (p : PMF X) (f : X → ℝ) : ℝ :=
  ∑ x, (p x).toReal * f x

/-- Integrating a real function against a finite PMF agrees with its finite expectation. -/
theorem integral_toMeasure_eq_expect [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) (f : X → ℝ) : (∫ x, f x ∂p.toMeasure) = expect p f := by
  simpa only [expect, smul_eq_mul] using PMF.integral_eq_sum p f

/-- A constant has its constant value as expectation. -/
@[simp] theorem expect_const (p : PMF X) (c : ℝ) : expect p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, probability_sum, one_mul]

/-- The zero function has zero expectation. -/
@[simp] theorem expect_zero (p : PMF X) : expect p (fun _ => 0) = 0 :=
  expect_const p 0

/-- Expectation preserves addition. -/
theorem expect_add (p : PMF X) (f g : X → ℝ) :
    expect p (fun x => f x + g x) = expect p f + expect p g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

/-- A real scalar can be moved outside expectation. -/
theorem expect_mul (p : PMF X) (c : ℝ) (f : X → ℝ) :
    expect p (fun x => c * f x) = c * expect p f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

/-- Expectation of a finite sum is the sum of the expectations. -/
theorem expect_sum {ι : Type*} (p : PMF X) (s : Finset ι) (f : ι → X → ℝ) :
    expect p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, expect p (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Expectation preserves pointwise inequalities. -/
theorem expect_mono (p : PMF X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    expect p f ≤ expect p g := by
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) ENNReal.toReal_nonneg

/-- Expectation does not increase the sup-norm distance between finite real functions. -/
theorem norm_expect_sub_expect_le (p : PMF X) (f g : X → ℝ) :
    ‖expect p f - expect p g‖ ≤ ‖f - g‖ := by
  calc
    ‖expect p f - expect p g‖ = ‖∑ x, (p x).toReal * (f x - g x)‖ := by
      simp [expect, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ x, ‖(p x).toReal * (f x - g x)‖ := norm_sum_le _ _
    _ ≤ ∑ x, (p x).toReal * ‖f - g‖ := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (f - g) x) ENNReal.toReal_nonneg
    _ = ‖f - g‖ := by rw [← Finset.sum_mul, probability_sum, one_mul]

/-- Expectation under a point mass evaluates the function at that point. -/
@[simp] theorem expect_pure (x : X) (f : X → ℝ) : expect (PMF.pure x) f = f x := by
  classical
  simp [expect, PMF.pure_apply, apply_ite, ite_mul]

/-- Expectation under sequential sampling is the corresponding iterated expectation. -/
theorem expect_bind {Y : Type*} [Fintype Y] (p : PMF X) (q : X → PMF Y)
    (f : Y → ℝ) : expect (p.bind q) f = expect p (fun x => expect (q x) f) := by
  classical
  simp only [expect, PMF.bind_apply, tsum_fintype (L := .unconditional X),
    ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (p.apply_ne_top x)
      ((q x).apply_ne_top _)), ENNReal.toReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/-- Mapping samples composes the function whose expectation is taken. -/
theorem expect_map {Y : Type*} [Fintype Y] (p : PMF X) (g : X → Y) (f : Y → ℝ) :
    expect (p.map g) f = expect p (fun x => f (g x)) := by
  simp [PMF.map, expect_bind]

end Rlib
