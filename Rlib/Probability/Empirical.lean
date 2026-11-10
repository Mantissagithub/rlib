module

public import Rlib.Probability.Expectation

/-! # Empirical probability mass functions and sample means -/

@[expose] public section

noncomputable section

open scoped BigOperators ENNReal

namespace Rlib

variable {S : Type*} {n : ℕ}

/-- The arithmetic mean of a nonempty sequence of real observations. -/
def sampleMean (x : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, x i) / (n + 1 : ℝ)

/-- A constant sequence has its constant value as sample mean. -/
@[simp] theorem sampleMean_const (c : ℝ) : sampleMean (fun _ : Fin (n + 1) => c) = c := by
  simp only [sampleMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_div_cancel_left₀ c (by positivity)

/-- Sample means preserve addition. -/
theorem sampleMean_add (x y : Fin (n + 1) → ℝ) :
    sampleMean (fun i => x i + y i) = sampleMean x + sampleMean y := by
  simp [sampleMean, Finset.sum_add_distrib, add_div]

/-- A real scalar can be moved outside a sample mean. -/
theorem sampleMean_mul (c : ℝ) (x : Fin (n + 1) → ℝ) :
    sampleMean (fun i => c * x i) = c * sampleMean x := by
  unfold sampleMean
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The empirical distribution assigns equal mass to each observation, counting repetitions. -/
def empiricalPMF (x : Fin (n + 1) → S) : PMF S :=
  (PMF.ofFintype (fun _ : Fin (n + 1) => (n + 1 : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simpa only [Nat.cast_add, Nat.cast_one] using
      ENNReal.mul_inv_cancel (a := (↑(n + 1) : ℝ≥0∞)) (by simp) (by simp))).map x

private theorem sample_weight_toReal :
    ((n + 1 : ℝ≥0∞)⁻¹).toReal = (n + 1 : ℝ)⁻¹ := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast,
    ENNReal.toReal_one]

/-- Empirical expectation is the sample mean of the observed function values. -/
theorem expect_empiricalPMF [Fintype S] (x : Fin (n + 1) → S) (f : S → ℝ) :
    expect (empiricalPMF x) f = sampleMean (fun i => f (x i)) := by
  rw [empiricalPMF, expect_map]
  simp only [expect, PMF.ofFintype_apply, sample_weight_toReal, sampleMean]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

open scoped Classical in
/-- The real empirical mass at a state is its observed relative frequency. -/
theorem empiricalPMF_apply_toReal (x : Fin (n + 1) → S) (s : S) :
    ((empiricalPMF x) s).toReal =
      sampleMean (fun i => if x i = s then 1 else 0) := by
  classical
  simp only [empiricalPMF, PMF.map_apply, tsum_fintype (L := .unconditional (Fin (n + 1)))]
  rw [ENNReal.toReal_sum (fun i _ => by
    split_ifs <;> simp)]
  simp only [PMF.ofFintype_apply, sampleMean, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : s = x i
  · rw [ite_eq_left h, ite_eq_left h.symm, one_mul, sample_weight_toReal]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), ENNReal.toReal_zero, zero_mul]

end Rlib
