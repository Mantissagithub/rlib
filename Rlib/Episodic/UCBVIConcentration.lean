module

public import Rlib.Episodic.UCBVILaw
public import Rlib.Probability.Concentration

/-! # Model errors of UCB-VI

Under the law of the draws, the first `n` draws at a stage, state, and action are independent
with law `P_h (· | s, a)`, so the empirical model built from them concentrates. This file proves
a uniform Hoeffding bound over stages, pairs, visit numbers, and a finite family of functions,
and reduces the bound of Agarwal, Jiang, Kakade, and Sun, Lemma 7.2, for every function with
values in `[0, H]` to the bounds for indicators of sets of states.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib

namespace EpisodicMDP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] {H K : ℕ}

omit [Fintype A] [DecidableEq S] [DecidableEq A] in
/-- If every set of states has nearly the same mass under `p` and `q`, then every function with
values in `[0, B]` has nearly the same expectation: `|E_p f - E_q f| ≤ B ε`. -/
theorem abs_expect_sub_le_of_sets (p q : PMF S) {ε B : ℝ}
    (hT : ∀ T : Finset S, |∑ t ∈ T, (p t).toReal - ∑ t ∈ T, (q t).toReal| ≤ ε)
    (hB : 0 ≤ B) {f : S → ℝ} (hf : ∀ t, f t ∈ Set.Icc 0 B) :
    |expect p f - expect q f| ≤ B * ε := by
  classical
  set d : S → ℝ := fun t => (p t).toReal - (q t).toReal
  have hdiff : expect p f - expect q f = ∑ t, d t * f t := by
    simp only [expect, d, sub_mul, Finset.sum_sub_distrib]
  set Tp := Finset.univ.filter fun t => 0 < d t
  set Tn := Finset.univ.filter fun t => d t < 0
  rw [hdiff, abs_le]
  constructor
  · have hlow (t : S) : (if d t < 0 then d t * B else 0) ≤ d t * f t := by
      split_ifs with h
      · exact mul_le_mul_of_nonpos_left (hf t).2 h.le
      · exact mul_nonneg (not_lt.mp h) (hf t).1
    have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hlow t
    rw [← Finset.sum_filter, ← Finset.sum_mul] at hsum
    have hTn := hT Tn
    rw [← Finset.sum_sub_distrib] at hTn
    have := (abs_le.mp hTn).1
    nlinarith
  · have hup (t : S) : d t * f t ≤ if 0 < d t then d t * B else 0 := by
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (hf t).2 h.le
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (hf t).1
    have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hup t
    rw [← Finset.sum_filter, ← Finset.sum_mul] at hsum
    have hTp := hT Tp
    rw [← Finset.sum_sub_distrib] at hTp
    have := (abs_le.mp hTp).2
    nlinarith

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq S] [DecidableEq A] in
/-- The index of draw number `i < m + 1` at stage `h`, state `s`, and action `a`. -/
theorem drawIndex_lt {K : ℕ} (m : Fin K) (i : Fin (m + 1)) : (i : ℕ) < K :=
  lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt) m.isLt

omit [DecidableEq S] [DecidableEq A] in
/-- **Hoeffding for the first draws.** For `|f| ≤ B` with `B > 0` and `0 < δ ≤ 2`, the mean of
`f` over the first `m + 1` draws at `(h, s, a)` deviates from `E_{P_h (s, a)} f` by at least
`B √(2 log (2 / δ) / (m + 1))` with probability at most `δ`. -/
theorem measure_tape_sampleMean_le (M : EpisodicMDP S A) (h : Fin H) (s : S) (a : A)
    (m : Fin K) {f : S → ℝ} {B : ℝ} (hB : 0 < B) (hf : ∀ t, |f t| ≤ B) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ2 : δ ≤ 2) :
    (M.tapeLaw H K).real {ω | B * Real.sqrt (2 * Real.log (2 / δ) / (m + 1)) ≤
      |sampleMean (fun i : Fin (m + 1) => f (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) -
        expect (M.transition h s a) f|} ≤ δ := by
  set ν : TapeIndex S A H K → PMF S := fun c => M.transition c.1 c.2.1 c.2.2.1
  set g : Fin (m + 1) → TapeIndex S A H K := fun i => (h, s, a, ⟨i, drawIndex_lt m i⟩)
  have hg : Function.Injective g := by
    intro i j hij
    simp only [g, Prod.mk.injEq, Fin.mk.injEq, true_and] at hij
    exact Fin.ext hij
  have hfm : Measurable f := measurable_of_countable f
  have hall : iIndepFun (fun (c : TapeIndex S A H K) (ω : TapeIndex S A H K → S) => ω c)
      (M.tapeLaw H K) :=
    iIndepFun_pi (μ := fun c => (ν c).toMeasure) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hindep := (hall.precomp hg).comp (fun _ => f) (fun _ => hfm)
  have hlaw (i : Fin (m + 1)) :
      ∫ ω : TapeIndex S A H K → S, f (ω (g i)) ∂M.tapeLaw H K =
        expect (M.transition h s a) f := by
    have hmap : (M.tapeLaw H K).map (fun ω => ω (g i)) = (ν (g i)).toMeasure :=
      (measurePreserving_eval (fun c => (ν c).toMeasure) (g i)).map_eq
    rw [← integral_map (measurable_pi_apply (g i)).aemeasurable hfm.aestronglyMeasurable, hmap,
      integral_toMeasure_eq_expect]
  have hN : (0 : ℝ) < m + 1 := by positivity
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  set ε := B * Real.sqrt (2 * Real.log (2 / δ) / (m + 1))
  have hε : 0 ≤ ε := by positivity
  have hH := measure_abs_sampleMean_sub_le_of_abs_le
    (X := fun i (ω : TapeIndex S A H K → S) => f (ω (g i)))
    hindep (fun i => (hfm.comp (measurable_pi_apply (g i))).aemeasurable) hB
    (fun i => ae_of_all _ fun ω => hf _) hlaw hε
  have hexp : 2 * Real.exp (-(((m : ℕ) + 1 : ℝ) * ε ^ 2) / (2 * B ^ 2)) = δ := by
    have hsq : ε ^ 2 = B ^ 2 * (2 * Real.log (2 / δ) / (m + 1)) := by
      simp only [ε, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (2 / δ) / (m + 1))]
    rw [hsq, show -(((m : ℝ) + 1) * (B ^ 2 * (2 * Real.log (2 / δ) / (m + 1)))) / (2 * B ^ 2) =
      -Real.log (2 / δ) by field_simp, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hexp] at hH
  exact hH

omit [DecidableEq S] [DecidableEq A] in
/-- **Uniform Hoeffding over a finite family.** For functions `F j h` with `|F j h| ≤ B` and
`0 < δ ≤ 1`, with probability at least `1 - δ`, at every `j`, stage `h < H`, pair, and visit
number `m + 1 ≤ K`, the mean of `F j h` over the first `m + 1` draws is within
`B √(2 log (2 |J| H |S| |A| K / δ) / (m + 1))` of `E_{P_h} F j h`. -/
theorem measure_tape_exists_le (M : EpisodicMDP S A) {J : Type*} [Fintype J]
    (F : J → ℕ → S → ℝ) {B : ℝ} (hB : 0 < B) (hF : ∀ j h t, |F j h t| ≤ B) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (M.tapeLaw H K).real {ω | ∃ j, ∃ h : Fin H, ∃ s a, ∃ m : Fin K,
      B * Real.sqrt (2 * Real.log (2 * (Fintype.card J * H * Fintype.card S *
        Fintype.card A * K) / δ) / (m + 1)) ≤
      |sampleMean (fun i : Fin (m + 1) => F j h (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) -
        expect (M.transition h s a) (F j h)|} ≤ δ := by
  classical
  set C : ℝ := Fintype.card J * H * Fintype.card S * Fintype.card A * K
  have hC : C = Fintype.card (J × Fin H × S × A × Fin K) := by
    simp only [C, Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  by_cases hne : Nonempty (J × Fin H × S × A × Fin K)
  swap
  · have hempty : {ω : TapeIndex S A H K → S | ∃ j, ∃ h : Fin H, ∃ s a, ∃ m : Fin K,
        B * Real.sqrt (2 * Real.log (2 * C / δ) / (m + 1)) ≤
        |sampleMean (fun i : Fin (m + 1) => F j h (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) -
          expect (M.transition h s a) (F j h)|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun j h s a m _ => hne ⟨(j, h, s, a, m)⟩
    rw [hempty, measureReal_empty]
    exact hδ0.le
  have hC1 : 1 ≤ C := by rw [hC]; exact Nat.one_le_cast.mpr Fintype.card_pos
  set δ' := δ / C
  have hδ'0 : 0 < δ' := div_pos hδ0 (by linarith)
  have hδ'2 : δ' ≤ 2 := ((div_le_one (by linarith)).mpr (by linarith)).trans (by norm_num)
  have hlog : Real.log (2 / δ') = Real.log (2 * C / δ) := by
    simp only [δ']; congr 1; field_simp
  have hsub : {ω : TapeIndex S A H K → S | ∃ j, ∃ h : Fin H, ∃ s a, ∃ m : Fin K,
      B * Real.sqrt (2 * Real.log (2 * C / δ) / (m + 1)) ≤
      |sampleMean (fun i : Fin (m + 1) => F j h (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) -
        expect (M.transition h s a) (F j h)|} ⊆
      ⋃ q : J × Fin H × S × A × Fin K, {ω | B * Real.sqrt (2 * Real.log (2 / δ') /
        (q.2.2.2.2 + 1)) ≤ |sampleMean (fun i : Fin (q.2.2.2.2 + 1) =>
          F q.1 q.2.1 (ω (q.2.1, q.2.2.1, q.2.2.2.1, ⟨i, drawIndex_lt q.2.2.2.2 i⟩))) -
          expect (M.transition q.2.1 q.2.2.1 q.2.2.2.1) (F q.1 q.2.1)|} := by
    rintro ω ⟨j, h, s, a, m, hω⟩
    refine Set.mem_iUnion.mpr ⟨(j, h, s, a, m), ?_⟩
    simp only [Set.mem_ofPred_eq, hlog]
    exact hω
  refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
  calc _ ≤ ∑ _q : J × Fin H × S × A × Fin K, δ' := Finset.sum_le_sum fun q _ =>
        M.measure_tape_sampleMean_le q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 hB (hF q.1 q.2.1) hδ'0
          hδ'2
    _ = δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hC]
        simp only [δ']
        field_simp

end EpisodicMDP

end Rlib
