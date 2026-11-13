module

public import Rlib.Probability.Concentration
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Bernstein's inequality

For independent observations within `M` of a common mean `θ` with variance at most `σ²`, the
sample mean of `n + 1` observations deviates from `θ` by at least `ε` with probability at most
`2 * exp (-(n + 1) * ε ^ 2 / (2 * σ ^ 2 + 2 * M * ε / 3))`. This is the form stated in Agarwal,
Jiang, Kakade, and Sun, *Reinforcement Learning: Theory and Algorithms*, and in Boucheron,
Lugosi, and Massart, *Concentration Inequalities*, Theorem 2.10. The proof bounds the moment
generating function with `exp u - 1 - u ≤ u ^ 2 / (2 * (1 - c / 3))` for `u ≤ c < 3`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Nat

namespace Rlib

/-- `(k + 2)! ≥ 2 * 3 ^ k`. -/
theorem two_mul_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2)! := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

/-- For `0 ≤ u < 3`, `exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3))`. -/
theorem exp_sub_one_sub_le_of_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3)) := by
  have hr0 : 0 ≤ u / 3 := by positivity
  have hr1 : u / 3 < 1 := by linarith
  have hs := Real.summable_pow_div_factorial u
  have hs1 : Summable fun n : ℕ => u ^ (n + 1) / (n + 1)! := (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable fun n : ℕ => u ^ (n + 2) / (n + 2)! := (summable_nat_add_iff 2).mpr hs
  have hexp : Real.exp u = 1 + u + ∑' n : ℕ, u ^ (n + 2) / (n + 2)! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    change ∑' n : ℕ, u ^ n / (n ! : ℝ) = _
    rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
      Nat.factorial_one]
    ring_nf
  have hterm (n : ℕ) : u ^ (n + 2) / (n + 2)! ≤ u ^ 2 / 2 * (u / 3) ^ n := by
    have hf : (2 * 3 ^ n : ℝ) ≤ (n + 2)! := by exact_mod_cast two_mul_three_pow_le_factorial n
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    calc u ^ (n + 2) / (n + 2)! ≤ u ^ (n + 2) / (2 * 3 ^ n) :=
          div_le_div_of_nonneg_left (by positivity) hpos hf
      _ = u ^ 2 / 2 * (u / 3) ^ n := by rw [div_pow]; field_simp; ring
  have hgeom : Summable fun n : ℕ => u ^ 2 / 2 * (u / 3) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle := hs2.tsum_le_tsum hterm hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
  have : u ^ 2 / 2 * (1 - u / 3)⁻¹ = u ^ 2 / (2 * (1 - u / 3)) := by
    field_simp
  linarith

/-- For `u ≤ 0`, `exp u - 1 - u ≤ u ^ 2 / 2`. -/
theorem exp_sub_one_sub_le_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
  set f : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hf (x : ℝ) : HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    have h := (((hasDerivAt_id x).neg.const_add 1).add
      ((hasDerivAt_pow 2 x).div_const 2)).sub (hasDerivAt_neg x).exp
    convert h using 1
    · funext y
      simp only [f, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
      ring
    · norm_num
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hf x).continuousAt.continuousWithinAt)
      (fun x _ => (hf x).differentiableAt.differentiableWithinAt) fun x _ => ?_
    rw [(hf x).deriv]
    linarith [Real.add_one_le_exp (-x)]
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (neg_nonneg.mpr hu))
    (neg_nonneg.mpr hu)
  simp only [f, neg_neg, neg_zero, Real.exp_zero] at h
  nlinarith

/-- For `0 ≤ c < 3` and `u ≤ c`, `exp u - 1 - u ≤ u ^ 2 / (2 * (1 - c / 3))`. -/
theorem exp_sub_one_sub_le {u c : ℝ} (hc0 : 0 ≤ c) (hc3 : c < 3) (hu : u ≤ c) :
    Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - c / 3)) := by
  have hk : 0 < 2 * (1 - c / 3) := by linarith
  rcases le_or_gt u 0 with h | h
  · refine (exp_sub_one_sub_le_of_nonpos h).trans ?_
    exact div_le_div_of_nonneg_left (sq_nonneg _) hk (by linarith)
  · refine (exp_sub_one_sub_le_of_nonneg h.le (by linarith)).trans ?_
    exact div_le_div_of_nonneg_left (sq_nonneg _) hk (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}

/-- **Bernstein's bound on the moment generating function.** If `|Y| ≤ M`, `E Y = 0`, and
`E Y ^ 2 ≤ v`, then `E exp (λ Y) ≤ exp (λ ^ 2 * v / (2 * (1 - λ * M / 3)))` for
`0 ≤ λ` with `λ * M < 3`. -/
theorem mgf_le_of_abs_le {Y : Ω → ℝ} (hmeas : AEMeasurable Y μ) {M v l : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ M) (hmean : ∫ ω, Y ω ∂μ = 0) (hvar : ∫ ω, Y ω ^ 2 ∂μ ≤ v)
    (hl : 0 ≤ l) (hlM : l * M < 3) :
    mgf Y μ l ≤ Real.exp (l ^ 2 * v / (2 * (1 - l * M / 3))) := by
  have hK : 0 < 2 * (1 - l * M / 3) := by linarith
  have hintY : Integrable Y μ := Integrable.of_bound hmeas.aestronglyMeasurable M
    (by simpa [Real.norm_eq_abs] using hbound)
  have hintY2 : Integrable (fun ω => Y ω ^ 2) μ := Integrable.of_bound
    (hmeas.pow_const 2).aestronglyMeasurable (M ^ 2) (by
      filter_upwards [hbound] with ω h
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  have hintE : Integrable (fun ω => Real.exp (l * Y ω)) μ := Integrable.of_bound
    ((hmeas.const_mul l).exp).aestronglyMeasurable (Real.exp (l * M)) (by
      filter_upwards [hbound] with ω h
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans h) hl))
  have hpt : ∀ᵐ ω ∂μ, Real.exp (l * Y ω) ≤
      1 + l * Y ω + l ^ 2 / (2 * (1 - l * M / 3)) * Y ω ^ 2 := by
    filter_upwards [hbound] with ω h
    have hu : l * Y ω ≤ l * M := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans h) hl
    have := exp_sub_one_sub_le (mul_nonneg hl hM) hlM hu
    have heq : (l * Y ω) ^ 2 / (2 * (1 - l * M / 3)) =
        l ^ 2 / (2 * (1 - l * M / 3)) * Y ω ^ 2 := by ring
    linarith
  have hint2 : Integrable (fun ω => 1 + l * Y ω + l ^ 2 / (2 * (1 - l * M / 3)) * Y ω ^ 2) μ :=
    ((integrable_const 1).add (hintY.const_mul l)).add (hintY2.const_mul _)
  calc mgf Y μ l = ∫ ω, Real.exp (l * Y ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + l * Y ω + l ^ 2 / (2 * (1 - l * M / 3)) * Y ω ^ 2) ∂μ :=
        integral_mono_ae hintE hint2 hpt
    _ = 1 + l * 0 + l ^ 2 / (2 * (1 - l * M / 3)) * ∫ ω, Y ω ^ 2 ∂μ := by
        rw [integral_add (f := fun ω => 1 + l * Y ω)
            (g := fun ω => l ^ 2 / (2 * (1 - l * M / 3)) * Y ω ^ 2)
            ((integrable_const 1).add (hintY.const_mul l)) (hintY2.const_mul _),
          integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => l * Y ω) (integrable_const 1)
            (hintY.const_mul l), integral_const_mul, integral_const_mul, hmean]
        simp
    _ ≤ 1 + l ^ 2 * v / (2 * (1 - l * M / 3)) := by
        have := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ l ^ 2 / (2 * (1 - l * M / 3)))
        have heq : l ^ 2 / (2 * (1 - l * M / 3)) * v = l ^ 2 * v / (2 * (1 - l * M / 3)) := by
          ring
        linarith
    _ ≤ _ := by linarith [Real.add_one_le_exp (l ^ 2 * v / (2 * (1 - l * M / 3)))]

/-- **Bernstein's inequality for sums.** For independent `Y i`, `i < n + 1`, with `|Y i| ≤ M`,
mean zero, and `E (Y i) ^ 2 ≤ v` where `v > 0`, the sum exceeds `t ≥ 0` with probability at most
`exp (-t ^ 2 / (2 * ((n + 1) * v + M * t / 3)))`. -/
theorem measure_sum_ge_le_bernstein {Y : Fin (n + 1) → Ω → ℝ} (hindep : iIndepFun Y μ)
    (hmeas : ∀ i, AEMeasurable (Y i) μ) {M v : ℝ} (hM : 0 ≤ M) (hv : 0 < v)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ M) (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, Y i ω} ≤
      Real.exp (-t ^ 2 / (2 * ((n + 1) * v + M * t / 3))) := by
  set N : ℝ := n + 1
  have hN : 0 < N := by positivity
  set D := N * v + M * t / 3
  have hD : 0 < D := by positivity
  set l := t / D
  have hl : 0 ≤ l := div_nonneg ht hD.le
  have hlM : l * M < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    simp only [D]
    nlinarith [mul_pos hN hv]
  have h1 : 1 - l * M / 3 = N * v / D := by
    simp only [l, D]; field_simp; ring
  have hmgf (i : Fin (n + 1)) := mgf_le_of_abs_le (hmeas i) hM (hbound i) (hmean i) (hvar i) hl hlM
  have hsum : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by
    funext ω; simp [Finset.sum_apply]
  have hmeasS : AEMeasurable (fun ω => ∑ i, Y i ω) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ => hmeas i
  have hint : Integrable (fun ω => Real.exp (l * ∑ i, Y i ω)) μ := Integrable.of_bound
    ((hmeasS.const_mul l).exp).aestronglyMeasurable (Real.exp (l * (N * M))) (by
      have hall : ∀ᵐ ω ∂μ, ∀ i, |Y i ω| ≤ M := ae_all_iff.mpr hbound
      filter_upwards [hall] with ω h
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hl)
      calc ∑ i, Y i ω ≤ ∑ _i : Fin (n + 1), M :=
            Finset.sum_le_sum fun i _ => (le_abs_self _).trans (h i)
        _ = N * M := by simp [N, Finset.sum_const, Finset.card_univ])
  have hch := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i, Y i ω) t hl hint
  have hprod : mgf (fun ω => ∑ i, Y i ω) μ l = ∏ i, mgf (Y i) μ l := by
    rw [hsum]; exact hindep.mgf_sum₀ hmeas Finset.univ
  have hprodle : ∏ i, mgf (Y i) μ l ≤
      ∏ _i : Fin (n + 1), Real.exp (l ^ 2 * v / (2 * (1 - l * M / 3))) :=
    Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) fun i _ => hmgf i
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul] at hprodle
  refine hch.trans ?_
  rw [hprod]
  calc Real.exp (-l * t) * ∏ i, mgf (Y i) μ l
      ≤ Real.exp (-l * t) * Real.exp (↑(n + 1) * (l ^ 2 * v / (2 * (1 - l * M / 3)))) :=
        mul_le_mul_of_nonneg_left hprodle (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (2 * ((n + 1) * v + M * t / 3))) := by
        rw [← Real.exp_add, h1]
        congr 1
        simp only [l, D, N]
        push_cast
        field_simp
        ring

/-- **Bernstein's inequality (two-sided, sample mean).** For independent observations
`X i`, `i < n + 1`, with `|X i - θ| ≤ M`, mean `θ`, and variance at most `σ2 > 0`, the sample
mean deviates from `θ` by at least `ε ≥ 0` with probability at most
`2 * exp (-(n + 1) * ε ^ 2 / (2 * σ2 + 2 * M * ε / 3))`. -/
theorem measure_abs_sampleMean_sub_le_bernstein {X : Fin (n + 1) → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ) {M σ2 θ : ℝ} (hM : 0 ≤ M)
    (hσ : 0 < σ2) (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω - θ| ≤ M) (hmean : ∀ i, ∫ ω, X i ω ∂μ = θ)
    (hvar : ∀ i, ∫ ω, (X i ω - θ) ^ 2 ∂μ ≤ σ2) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |sampleMean (fun i => X i ω) - θ|} ≤
      2 * Real.exp (-((n + 1) * ε ^ 2) / (2 * σ2 + 2 * M * ε / 3)) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hint (i : Fin (n + 1)) : Integrable (X i) μ := by
    have h : Integrable (fun ω => X i ω - θ) μ := Integrable.of_bound
      ((hmeas i).sub_const θ).aestronglyMeasurable M (by simpa [Real.norm_eq_abs] using hbound i)
    exact (h.add (integrable_const θ)).congr (Filter.Eventually.of_forall fun ω => by simp)
  have hmean0 (i : Fin (n + 1)) : ∫ ω, (X i ω - θ) ∂μ = 0 := by
    rw [integral_sub (hint i) (integrable_const θ), hmean i]; simp
  have hmean0' (i : Fin (n + 1)) : ∫ ω, -(X i ω - θ) ∂μ = 0 := by
    rw [integral_neg, hmean0 i, neg_zero]
  set t := (n + 1 : ℝ) * ε
  have ht : 0 ≤ t := by positivity
  have hu := measure_sum_ge_le_bernstein (Y := fun i ω => X i ω - θ)
    (hindep.comp (fun _ x => x - θ) (fun _ => by fun_prop)) (fun i => (hmeas i).sub_const θ) hM
    hσ hbound hmean0 hvar ht
  have hl := measure_sum_ge_le_bernstein (Y := fun i ω => -(X i ω - θ))
    (hindep.comp (fun _ x => -(x - θ)) (fun _ => by fun_prop))
    (fun i => ((hmeas i).sub_const θ).neg) hM hσ
    (fun i => by filter_upwards [hbound i] with ω h; rwa [abs_neg]) hmean0'
    (fun i => by simp only [neg_sq]; exact hvar i) ht
  have hexp : -t ^ 2 / (2 * ((n + 1) * σ2 + M * t / 3)) =
      -((n + 1) * ε ^ 2) / (2 * σ2 + 2 * M * ε / 3) := by
    simp only [t]; field_simp
  rw [hexp] at hu hl
  have hcenter (ω : Ω) : ∑ i, (X i ω - θ) = (n + 1) * (sampleMean (fun i => X i ω) - θ) := by
    simp only [sampleMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hevent : {ω | ε ≤ |sampleMean (fun i => X i ω) - θ|} ⊆
      {ω | t ≤ ∑ i, (X i ω - θ)} ∪ {ω | t ≤ ∑ i, -(X i ω - θ)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib, hcenter] at hω ⊢
    rcases le_abs'.mp hω with h | h
    · right; simp only [t]; nlinarith
    · left; simp only [t]; nlinarith
  calc _ ≤ μ.real ({ω | t ≤ ∑ i, (X i ω - θ)} ∪ {ω | t ≤ ∑ i, -(X i ω - θ)}) :=
        measureReal_mono hevent
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

/-- **Bernstein's inequality, high-probability form.** Under the conditions of
`measure_abs_sampleMean_sub_le_bernstein`, for `0 < δ ≤ 1`, the sample mean deviates from `θ` by
at least `√(2 * σ2 * log (2 / δ) / (n + 1)) + 2 * M * log (2 / δ) / (3 * (n + 1))` with
probability at most `δ`. -/
theorem measure_abs_sampleMean_sub_ge_le_bernstein {X : Fin (n + 1) → Ω → ℝ}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ) {M σ2 θ : ℝ} (hM : 0 ≤ M)
    (hσ : 0 < σ2) (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω - θ| ≤ M) (hmean : ∀ i, ∫ ω, X i ω ∂μ = θ)
    (hvar : ∀ i, ∫ ω, (X i ω - θ) ^ 2 ∂μ ≤ σ2) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | Real.sqrt (2 * σ2 * Real.log (2 / δ) / (n + 1)) +
        2 * M * Real.log (2 / δ) / (3 * (n + 1)) ≤ |sampleMean (fun i => X i ω) - θ|} ≤ δ := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  set L := Real.log (2 / δ)
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  set a := Real.sqrt (2 * σ2 * L / (n + 1))
  set b := 2 * M * L / (3 * (n + 1))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := by positivity
  have ha2 : a ^ 2 = 2 * σ2 * L / (n + 1) := Real.sq_sqrt (by positivity)
  set ε := a + b
  have hε : 0 ≤ ε := add_nonneg ha hb
  refine (measure_abs_sampleMean_sub_le_bernstein hindep hmeas hM hσ hbound hmean hvar hε).trans ?_
  have hden : 0 < 2 * σ2 + 2 * M * ε / 3 := by positivity
  -- `(n + 1) * ε ^ 2 ≥ L * (2 * σ2 + 2 * M * ε / 3)`.
  have hkey : L * (2 * σ2 + 2 * M * ε / 3) ≤ (n + 1) * ε ^ 2 := by
    have h1 : (n + 1) * a ^ 2 = 2 * σ2 * L := by rw [ha2]; field_simp
    have h2 : (n + 1) * (ε * b) = 2 * M * ε / 3 * L := by simp only [b]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb : a ≤ ε) (mul_nonneg hN.le ha),
      mul_nonneg hN.le (mul_nonneg hε hb)]
  have hexp : Real.exp (-((n + 1) * ε ^ 2) / (2 * σ2 + 2 * M * ε / 3)) ≤ δ / 2 := by
    calc Real.exp (-((n + 1) * ε ^ 2) / (2 * σ2 + 2 * M * ε / 3)) ≤ Real.exp (-L) := by
          refine Real.exp_le_exp.mpr ?_
          rw [neg_div, neg_le_neg_iff, le_div_iff₀ hden]
          exact hkey
      _ = δ / 2 := by
          simp only [L]
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
  linarith

end Rlib
