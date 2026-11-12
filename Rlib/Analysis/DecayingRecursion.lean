module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Recursions with decaying step sizes

A sequence that moves a fraction `a n` of the way toward a vanishing target eventually stays
below every positive level, provided the fractions are not summable. This is the
deterministic core of stochastic approximation arguments.
-/

@[expose] public section

open Filter Topology

namespace Rlib

/-- Moving a non-summable fraction of the way toward targets that tend to zero eventually
brings the sequence below every positive level. -/
theorem eventually_le_of_le_one_sub_mul_add {x a d : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1) (hsum : ¬Summable a)
    (hd : Tendsto d atTop (𝓝 0))
    (hx : ∀ n, x (n + 1) ≤ (1 - a n) * x n + a n * d n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, x n ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hd.eventually (Iio_mem_nhds hε2))
  set z : ℕ → ℝ := fun n => max (x n - ε / 2) 0
  have hz0 (n : ℕ) : 0 ≤ z n := le_max_right _ _
  have hstep (n : ℕ) (hn : N ≤ n) : z (n + 1) ≤ (1 - a n) * z n := by
    have hdn : d n < ε / 2 := hN n hn
    have hmul : (1 - a n) * (x n - ε / 2) ≤ (1 - a n) * z n :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr (ha1 n))
    apply max_le
    · nlinarith [hx n, mul_le_mul_of_nonneg_left hdn.le (ha0 n)]
    · exact mul_nonneg (sub_nonneg.mpr (ha1 n)) (hz0 n)
  have hdecay (k : ℕ) :
      z (k + N) ≤ Real.exp (-∑ i ∈ Finset.range k, a (i + N)) * z N := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, neg_add, Real.exp_add, Nat.succ_add]
      calc
        z (k + N + 1) ≤ (1 - a (k + N)) * z (k + N) := hstep _ (Nat.le_add_left N k)
        _ ≤ Real.exp (-a (k + N)) * (Real.exp (-∑ i ∈ Finset.range k, a (i + N)) * z N) := by
          apply mul_le_mul _ ih (hz0 _) (Real.exp_pos _).le
          linarith [Real.add_one_le_exp (-a (k + N))]
        _ = _ := by ring
  have htail : Tendsto (fun k => ∑ i ∈ Finset.range k, a (i + N)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun i => ha0 (i + N)).1
      fun h => hsum ((summable_nat_add_iff N).1 h)
  have hlim : Tendsto (fun k => Real.exp (-∑ i ∈ Finset.range k, a (i + N)) * z N)
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp htail).mul_const (z N)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hε2))
  refine eventually_atTop.2 ⟨K + N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
  have hzk : z (k + N) < ε / 2 := (hdecay k).trans_lt (hK k (by omega))
  have := le_max_left (x (k + N) - ε / 2) 0
  linarith

/-- A nonnegative sequence that moves a non-summable fraction of the way toward targets that
tend to zero converges to zero. -/
theorem tendsto_zero_of_le_one_sub_mul_add {x a d : ℕ → ℝ} (hx0 : ∀ n, 0 ≤ x n)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1) (hsum : ¬Summable a)
    (hd : Tendsto d atTop (𝓝 0))
    (hx : ∀ n, x (n + 1) ≤ (1 - a n) * x n + a n * d n) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (eventually_le_of_le_one_sub_mul_add ha0 ha1 hsum hd hx (half_pos hε))
  refine ⟨n₀, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hx0 n)]
  linarith [hn₀ n hn]

/-- Averaging inputs with non-summable fractions drives the average to zero when the partial
sums of the weighted inputs converge. The convergence may be conditional. -/
theorem tendsto_zero_of_eq_one_sub_mul_add_of_tendsto_sum {W a w : ℕ → ℝ} {c : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1) (hsum : ¬Summable a)
    (hw : Tendsto (fun n => ∑ k ∈ Finset.range n, a k * w k) atTop (𝓝 c))
    (hW : ∀ n, W (n + 1) = (1 - a n) * W n + a n * w n) :
    Tendsto W atTop (𝓝 0) := by
  set R : ℕ → ℝ := fun n => c - ∑ k ∈ Finset.range n, a k * w k
  have hR : Tendsto R atTop (𝓝 0) := by simpa using hw.const_sub c
  have hRstep (n : ℕ) : R n = a n * w n + R (n + 1) := by
    simp only [R, Finset.sum_range_succ]
    ring
  have hV (n : ℕ) : W (n + 1) + R (n + 1) = (1 - a n) * (W n + R n) + a n * R n := by
    rw [hW n, hRstep n]
    ring
  have hVneg (n : ℕ) :
      -(W (n + 1) + R (n + 1)) = (1 - a n) * -(W n + R n) + a n * -R n := by
    rw [hV n]
    ring
  have hV0 : Tendsto (fun n => W n + R n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (eventually_le_of_le_one_sub_mul_add
      (x := fun n => W n + R n) ha0 ha1 hsum hR (fun n => (hV n).le) (half_pos hε))
    obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 (eventually_le_of_le_one_sub_mul_add
      (x := fun n => -(W n + R n)) ha0 ha1 hsum (by simpa using hR.neg)
      (fun n => (hVneg n).le) (half_pos hε))
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hn₁ n (le_of_max_le_left hn), hn₂ n (le_of_max_le_right hn)]
  simpa using hV0.sub hR

end Rlib
