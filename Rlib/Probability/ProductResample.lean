module

public import Rlib.Probability.Expectation
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Resampling one coordinate of a finite product

Under a product of finite distributions, a function `G ω y` that does not depend on coordinate
`c` of `ω` has the same expectation at `y = ω c` as when `y` is drawn afresh from the law of that
coordinate. This is the independence fact behind the "stack of samples" description of
interaction.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Rlib

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- An integral against a product of finite distributions is a weighted finite sum. -/
theorem integral_pi_eq_sum (ν : ι → PMF S) (f : (ι → S) → ℝ) :
    ∫ ω, f ω ∂(Measure.pi fun i => (ν i).toMeasure) =
      ∑ ω, (∏ i, (ν i (ω i)).toReal) * f ω := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [smul_eq_mul, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- **Resampling a coordinate.** If `G (update ω c z) y = G ω y` for all `ω`, `z`, and `y`, then
`E [G ω (ω c)] = E [E_{y ∼ ν c} G ω y]` under the product of the `ν i`. -/
theorem integral_pi_resample (ν : ι → PMF S) (c : ι) (G : (ι → S) → S → ℝ)
    (hG : ∀ ω z y, G (Function.update ω c z) y = G ω y) :
    ∫ ω, G ω (ω c) ∂(Measure.pi fun i => (ν i).toMeasure) =
      ∫ ω, expect (ν c) (G ω) ∂(Measure.pi fun i => (ν i).toMeasure) := by
  rw [integral_pi_eq_sum, integral_pi_eq_sum]
  set w' : (ι → S) → ℝ := fun ω => ∏ i ∈ Finset.univ.erase c, (ν i (ω i)).toReal
  have hw (ω : ι → S) : ∏ i, (ν i (ω i)).toReal = (ν c (ω c)).toReal * w' ω :=
    Fintype.prod_eq_mul_prod_compl c _ |>.trans (by simp only [w', Finset.compl_singleton])
  have hw' (ω : ι → S) (y : S) : w' (Function.update ω c y) = w' ω :=
    Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  -- The involution `(ω, y) ↦ (update ω c y, ω c)` swaps the two sides.
  set e : (ι → S) × S ≃ (ι → S) × S :=
    { toFun := fun p => (Function.update p.1 c p.2, p.1 c)
      invFun := fun p => (Function.update p.1 c p.2, p.1 c)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hsum1 : ∑ ω, (∏ i, (ν i (ω i)).toReal) * expect (ν c) (G ω) =
      ∑ p : (ι → S) × S, (ν c (p.1 c)).toReal * (ν c p.2).toReal * w' p.1 * G p.1 p.2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hw, expect, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hsum2 : ∑ p : (ι → S) × S, (ν c (p.1 c)).toReal * (ν c p.2).toReal * w' p.1 * G p.1 p.2 =
      ∑ p : (ι → S) × S, (ν c (p.1 c)).toReal * (ν c p.2).toReal * w' p.1 * G p.1 (p.1 c) := by
    refine (Fintype.sum_equiv e _ _ fun p => ?_).symm
    simp only [e, Equiv.coe_fn_mk, Function.update_self, hw', hG]
    ring
  rw [hsum1, hsum2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hone : ∑ y, (ν c y).toReal = 1 := probability_sum _
  rw [hw]
  calc (ν c (ω c)).toReal * w' ω * G ω (ω c)
      = (ν c (ω c)).toReal * w' ω * G ω (ω c) * ∑ y, (ν c y).toReal := by rw [hone, mul_one]
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring

end Rlib
