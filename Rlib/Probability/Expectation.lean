module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
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

end Rlib
