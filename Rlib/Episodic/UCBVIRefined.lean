module

public import Rlib.Episodic.UCBVIRegret
public import Rlib.Probability.Bernstein
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The refined analysis of UCB-VI

This file follows Agarwal, Jiang, Kakade, and Sun, Section 7.4. If every coordinate of the
empirical model satisfies the Bernstein-type bound of their Lemma 7.8,
`|P̂ (s') - P (s')| ≤ √(2 P (s') L' / N) + 2 L' / N`, then for every `f` with values in `[0, H]`,
`(P̂ - P) f ≤ E_P f / H + 3 H ^ 2 |S| L' / N` (their Lemma 7.7). Unrolling the gap between the
optimistic value and the value of the episode's policy then loses only the factor
`(1 + 1 / H) ^ H ≤ e` (their Lemmas 7.9 and 7.10). The book's display in Lemma 7.9 omits one
bonus term; the formal recursion keeps it, so the bonus enters with the factor `2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Rlib

namespace EpisodicMDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]

omit [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] in
/-- **Refined model error (Agarwal, Jiang, Kakade, and Sun, Lemma 7.7).** If every coordinate of
`p` is within `√(2 q (s') L / n) + 2 L / n` of `q`, then for every `f` with values in `[0, H]`,
`H ≥ 1`, `E_p f - E_q f ≤ E_q f / H + 3 H ^ 2 |S| L / n`. -/
theorem expect_sub_expect_le_refined (p q : PMF S) {n L H : ℝ} (hn : 0 < n) (hL : 0 ≤ L)
    (hH : 1 ≤ H)
    (hc : ∀ t, |(p t).toReal - (q t).toReal| ≤
      Real.sqrt (2 * (q t).toReal * L / n) + 2 * L / n)
    {f : S → ℝ} (hf : ∀ t, f t ∈ Set.Icc 0 H) :
    expect p f - expect q f ≤ expect q f / H + 3 * H ^ 2 * Fintype.card S * L / n := by
  have hH0 : 0 < H := by linarith
  have hterm (t : S) : ((p t).toReal - (q t).toReal) * f t ≤
      (q t).toReal * f t / H + (H ^ 2 * L / (2 * n) + 2 * H * L / n) := by
    have hq : 0 ≤ (q t).toReal := ENNReal.toReal_nonneg
    set x := Real.sqrt (2 * (q t).toReal * L / n)
    -- `x ≤ q / H + H L / (2 n)` by the arithmetic-geometric mean inequality.
    have hx : x ≤ (q t).toReal / H + H * L / (2 * n) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have hsq : 0 ≤ ((q t).toReal / H - H * L / (2 * n)) ^ 2 := sq_nonneg _
      have hprod : 4 * ((q t).toReal / H) * (H * L / (2 * n)) = 2 * (q t).toReal * L / n := by
        field_simp; ring
      nlinarith
    have hft := hf t
    calc ((p t).toReal - (q t).toReal) * f t ≤ |(p t).toReal - (q t).toReal| * f t :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hft.1
      _ ≤ (x + 2 * L / n) * f t := mul_le_mul_of_nonneg_right (hc t) hft.1
      _ = x * f t + 2 * L / n * f t := by ring
      _ ≤ ((q t).toReal / H + H * L / (2 * n)) * f t + 2 * L / n * H := by
          gcongr
          · exact hft.1
          · exact hft.2
      _ ≤ (q t).toReal * f t / H + (H ^ 2 * L / (2 * n) + 2 * H * L / n) := by
          have h1 : H * L / (2 * n) * f t ≤ H * L / (2 * n) * H :=
            mul_le_mul_of_nonneg_left hft.2 (by positivity)
          have h2 : (q t).toReal / H * f t = (q t).toReal * f t / H := by ring
          have h3 : H * L / (2 * n) * H = H ^ 2 * L / (2 * n) := by ring
          have h4 : 2 * L / n * H = 2 * H * L / n := by ring
          nlinarith
  have hdiff : expect p f - expect q f = ∑ t, ((p t).toReal - (q t).toReal) * f t := by
    simp only [expect, sub_mul, Finset.sum_sub_distrib]
  rw [hdiff]
  calc ∑ t, ((p t).toReal - (q t).toReal) * f t
      ≤ ∑ t, ((q t).toReal * f t / H + (H ^ 2 * L / (2 * n) + 2 * H * L / n)) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = expect q f / H + Fintype.card S * (H ^ 2 * L / (2 * n) + 2 * H * L / n) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, expect,
          Finset.sum_div]
    _ ≤ expect q f / H + 3 * H ^ 2 * Fintype.card S * L / n := by
        have hS : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
        have hHH : H ≤ H ^ 2 := by nlinarith
        have hHL : 2 * H * L / n ≤ 2 * H ^ 2 * L / n :=
          div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hHH hL]) hn.le
        have heq : Fintype.card S * (H ^ 2 * L / (2 * n) + 2 * H ^ 2 * L / n) =
            5 / 2 * (H ^ 2 * Fintype.card S * L / n) := by field_simp; ring
        have hpos : 0 ≤ H ^ 2 * Fintype.card S * L / n := by positivity
        have hle := mul_le_mul_of_nonneg_left (add_le_add_left hHL (H ^ 2 * L / (2 * n))) hS
        have h3 : 3 * H ^ 2 * Fintype.card S * L / n = 3 * (H ^ 2 * Fintype.card S * L / n) := by
          ring
        linarith

/-- `(1 + 1 / H) ^ j ≤ e` for `j ≤ H`. -/
theorem one_add_inv_pow_le_exp_one {H j : ℕ} (hH : 0 < H) (hj : j ≤ H) :
    (1 + 1 / (H : ℝ)) ^ j ≤ Real.exp 1 := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  calc (1 + 1 / (H : ℝ)) ^ j ≤ Real.exp (1 / H) ^ j :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (H : ℝ))]) j
    _ = Real.exp (j * (1 / H)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        rw [mul_one_div, div_le_one hH']
        exact_mod_cast hj

/-- The per-visit cost of the refined analysis: `2 H` at an unvisited pair and
`4 H √(L / N) + 3 H ^ 2 |S| L' / N` otherwise. -/
def refinedCost (S : Type*) [Fintype S] (H : ℕ) (L L' : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 2 * H else 4 * H * Real.sqrt (L / n) + 3 * H ^ 2 * Fintype.card S * L' / n

omit [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A] in
theorem refinedCost_nonneg (H : ℕ) {L L' : ℝ} (hL' : 0 ≤ L') (n : ℕ) :
    0 ≤ refinedCost S H L L' n := by
  unfold refinedCost; split_ifs <;> positivity

omit [DecidableEq S] [DecidableEq A] in
/-- **One episode, refined (Agarwal, Jiang, Kakade, and Sun, Lemma 7.10).** Suppose that at every
visited pair the empirical model satisfies Lemma 7.3, `|(P̂ - P) V*_{h+1}| ≤ 2 H √(L / N)`, and
the coordinate bounds of Lemma 7.8, `|P̂ (s') - P (s')| ≤ √(2 P (s') L' / N) + 2 L' / N`. Then
the regret of the episode's policy is at most `e` times the expected refined visit cost along
its state distribution. -/
theorem optValue_sub_value_ucbviPolicy_le_refined (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) {H : ℕ} (hH : 0 < H) {L L' : ℝ}
    (hL' : 0 ≤ L') (samples : ℕ → S → A → ℕ → S) (N : ℕ → S → A → ℕ) (s₀ : S)
    (h73 : ∀ h, h < H → ∀ s a, 0 < N h s a →
      |expect (empiricalModel samples N h s a) (M.optValue H (h + 1)) -
        expect (M.transition h s a) (M.optValue H (h + 1))| ≤ 2 * H * Real.sqrt (L / N h s a))
    (h78 : ∀ h, h < H → ∀ s a, 0 < N h s a → ∀ t,
      |(empiricalModel samples N h s a t).toReal - (M.transition h s a t).toReal| ≤
        Real.sqrt (2 * (M.transition h s a t).toReal * L' / N h s a) + 2 * L' / N h s a) :
    M.optValue H 0 s₀ - M.value (M.ucbviPolicy H L samples N) H 0 s₀ ≤
      Real.exp 1 * ∑ h ∈ Finset.range H, expect (M.stateDist (M.ucbviPolicy H L samples N) s₀ h)
        (fun s => refinedCost S H L L' (N h s (M.ucbviPolicy H L samples N h s))) := by
  set Phat := empiricalModel samples N
  set b := ucbBonus H L N
  set π := M.ucbviPolicy H L samples N
  set Vhat := M.ucbValue Phat b H
  set V := M.value π H
  set Vs := M.optValue H
  set c : ℕ → S → ℝ := fun h s => refinedCost S H L L' (N h s (π h s))
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hbnn := ucbBonus_nonneg (S := S) (A := A) H (L := L) N
  have hVs (h : ℕ) (t : S) : Vs (h + 1) t ∈ Set.Icc 0 (H : ℝ) := by
    refine ⟨M.optValue_nonneg (fun h s a => (hr h s a).1) H (h + 1) t, ?_⟩
    by_cases hh : h + 1 ≤ H
    · have := M.optValue_le (fun h s a => (hr h s a).2) hh t
      push_cast at this
      linarith
    · simp only [Vs]; rw [M.optValue_of_le (by omega)]; positivity
  have hopt (h : ℕ) (t : S) : Vs h t ≤ Vhat h t :=
    M.optValue_le_ucbValue hr Phat b H (fun h hh s a => by
      rcases hN : N h s a with _ | m
      · simp only [b, ucbBonus, hN]
        exact abs_expect_sub_expect_le _ _ (hVs h)
      · have := h73 h hh s a (by omega)
        simp only [hN] at this
        simp only [b, ucbBonus, hN]
        push_cast at this ⊢
        exact this) h t
  have hVhat (h : ℕ) (t : S) : Vhat h t ∈ Set.Icc 0 (H : ℝ) :=
    M.ucbValue_mem_Icc hr Phat hbnn H h t
  have hVle (h : ℕ) (t : S) : V h t ≤ Vs h t := M.value_le_optValue π H h t
  set Δ : ℕ → S → ℝ := fun h t => Vhat h t - V h t
  have hΔ0 (h : ℕ) (t : S) : 0 ≤ Δ h t := by
    simp only [Δ]; linarith [hopt h t, hVle h t]
  -- One step of the recursion.
  have hrec (h : ℕ) (hh : h < H) (s : S) : Δ h s ≤ c h s + (1 + 1 / (H : ℝ)) *
      expect (M.transition h s (π h s)) (Δ (h + 1)) := by
    set a := π h s
    have hEΔ : 0 ≤ expect (M.transition h s a) (Δ (h + 1)) := by
      have := expect_mono (M.transition h s a) (f := fun _ => 0) (hΔ0 (h + 1))
      rwa [expect_zero] at this
    have hupper : Δ h s ≤ b h s a + (expect (Phat h s a) (Vhat (h + 1)) -
        expect (M.transition h s a) (Vhat (h + 1))) +
        expect (M.transition h s a) (Δ (h + 1)) := by
      have h1 : Vhat h s = M.ucbQ Phat b H h s a := M.ucbValue_of_lt Phat b hh s
      have h2 : V h s = M.reward h s a + expect (M.transition h s a) (V (h + 1)) :=
        M.value_of_lt π hh s
      have h3 := min_le_left (M.reward h s a + b h s a + expect (Phat h s a) (Vhat (h + 1)))
        (H : ℝ)
      have h4 : expect (M.transition h s a) (Δ (h + 1)) =
          expect (M.transition h s a) (Vhat (h + 1)) -
            expect (M.transition h s a) (V (h + 1)) := expect_sub _ _ _
      simp only [Δ, ucbQ] at h1 h3 ⊢
      linarith
    simp only [c, refinedCost]
    rcases hN : N h s a with _ | m
    · simp only [↓reduceIte]
      have hb : b h s a = H := by simp only [b, ucbBonus, hN]
      have herr := abs_expect_sub_expect_le (Phat h s a) (M.transition h s a) (hVhat (h + 1))
      have hmul : expect (M.transition h s a) (Δ (h + 1)) ≤
          (1 + 1 / (H : ℝ)) * expect (M.transition h s a) (Δ (h + 1)) := by
        have : 0 ≤ 1 / (H : ℝ) * expect (M.transition h s a) (Δ (h + 1)) := by positivity
        linarith
      linarith [le_abs_self (expect (Phat h s a) (Vhat (h + 1)) -
        expect (M.transition h s a) (Vhat (h + 1)))]
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have hNpos : 0 < N h s a := by omega
      have hb : b h s a = 2 * H * Real.sqrt (L / ((m : ℝ) + 1)) := by
        simp only [b, ucbBonus, hN]
      set f : S → ℝ := fun t => Vhat (h + 1) t - Vs (h + 1) t
      have hf (t : S) : f t ∈ Set.Icc 0 (H : ℝ) := by
        simp only [f]
        constructor
        · linarith [hopt (h + 1) t]
        · linarith [(hVhat (h + 1) t).2, (hVs h t).1]
      have h77 := expect_sub_expect_le_refined (Phat h s a) (M.transition h s a)
        (n := (N h s a : ℝ)) (by exact_mod_cast hNpos) hL' hH1 (h78 h hh s a hNpos) hf
      have hsplit : expect (Phat h s a) (Vhat (h + 1)) - expect (M.transition h s a)
          (Vhat (h + 1)) = (expect (Phat h s a) f - expect (M.transition h s a) f) +
          (expect (Phat h s a) (Vs (h + 1)) - expect (M.transition h s a) (Vs (h + 1))) := by
        simp only [f, expect_sub]; ring
      have hfΔ : expect (M.transition h s a) f ≤ expect (M.transition h s a) (Δ (h + 1)) :=
        expect_mono _ fun t => by simp only [f, Δ]; linarith [hVle (h + 1) t]
      have h3 := h73 h hh s a hNpos
      rw [hN] at h77 h3
      have hdivle : expect (M.transition h s a) f / H ≤
          1 / (H : ℝ) * expect (M.transition h s a) (Δ (h + 1)) := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hfΔ (by positivity)
      push_cast at hb h77 h3 ⊢
      nlinarith [le_abs_self (expect (Phat h s a) (Vs (h + 1)) -
        expect (M.transition h s a) (Vs (h + 1)))]
  -- Unroll along the state distribution of `π`.
  set d := M.stateDist π s₀
  set D : ℕ → ℝ := fun h => expect (d h) (Δ h)
  set κ : ℝ := 1 + 1 / (H : ℝ)
  have hκ : 0 ≤ κ := by positivity
  have key : ∀ h, h ≤ H → D h ≤ ∑ j ∈ Finset.Ico h H, κ ^ (j - h) * expect (d j) (c j) := by
    refine stage_induction (P := fun h => h ≤ H → D h ≤
      ∑ j ∈ Finset.Ico h H, κ ^ (j - h) * expect (d j) (c j)) H (fun h hh hh' => ?_)
      (fun h hh ih _ => ?_)
    · rw [show h = H by omega]
      simp only [D, Finset.Ico_self, Finset.sum_empty]
      have h0 (t : S) : Δ H t = 0 := by
        simp only [Δ, Vhat, V]
        rw [M.ucbValue_of_le Phat b le_rfl, M.value_of_le π le_rfl, sub_zero]
      rw [show Δ H = fun _ => 0 from funext h0, expect_zero]
    · have hstep : D h ≤ expect (d h) (c h) + κ * D (h + 1) := by
        have hb := expect_mono (d h) (hrec h hh)
        rw [expect_add, expect_mul] at hb
        simp only [D, d, stateDist, expect_bind]
        exact hb
      have ih' := mul_le_mul_of_nonneg_left (ih (by omega)) hκ
      rw [Finset.sum_eq_sum_Ico_succ_bot hh, Nat.sub_self, pow_zero, one_mul]
      have hshift : κ * ∑ j ∈ Finset.Ico (h + 1) H, κ ^ (j - (h + 1)) * expect (d j) (c j) =
          ∑ j ∈ Finset.Ico (h + 1) H, κ ^ (j - h) * expect (d j) (c j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := (Finset.mem_Ico.mp hj).1
        rw [show j - h = (j - (h + 1)) + 1 by omega, pow_succ]
        ring
      linarith
  have hfin := key 0 (Nat.zero_le H)
  simp only [D, d, stateDist, expect_pure, Δ] at hfin
  have hc0 (j : ℕ) : 0 ≤ expect (d j) (c j) := by
    have := expect_mono (d j) (f := fun _ => 0) (g := c j) fun t =>
      refinedCost_nonneg (S := S) H hL' _
    rwa [expect_zero] at this
  calc M.optValue H 0 s₀ - M.value π H 0 s₀ ≤ Vhat 0 s₀ - V 0 s₀ := by
        linarith [hopt 0 s₀]
    _ ≤ ∑ j ∈ Finset.Ico 0 H, κ ^ (j - 0) * expect (d j) (c j) := hfin
    _ ≤ ∑ j ∈ Finset.range H, Real.exp 1 * expect (d j) (c j) := by
        rw [Finset.range_eq_Ico]
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (hc0 j)
        rw [Nat.sub_zero]
        exact one_add_inv_pow_le_exp_one hH (Finset.mem_Ico.mp hj).2.le
    _ = _ := by rw [Finset.mul_sum]

/-! ### Coordinate concentration (Lemma 7.8) -/

variable [MeasurableSpace S] [MeasurableSingletonClass S] {H K : ℕ}

omit [Nonempty A] [DecidableEq A] in
/-- **Bernstein for one coordinate.** For `0 < δ ≤ 1`, the frequency of `t` among the first
`m + 1` draws at `(h, s, a)` deviates from `P_h (t | s, a)` by at least
`√(2 P (t) log (2 / δ) / (m + 1)) + 2 log (2 / δ) / (3 (m + 1))` with probability at most `δ`. -/
theorem measure_tape_coord_le (M : EpisodicMDP S A) (h : Fin H) (s : S) (a : A) (m : Fin K)
    (t : S) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (M.tapeLaw H K).real {ω | Real.sqrt (2 * (M.transition h s a t).toReal * Real.log (2 / δ) /
        (m + 1)) + 2 * 1 * Real.log (2 / δ) / (3 * (m + 1)) ≤
      |sampleMean (fun i : Fin (m + 1) =>
        (fun x => if x ∈ ({t} : Finset S) then (1 : ℝ) else 0)
          (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) - (M.transition h s a t).toReal|} ≤ δ := by
  set ν : TapeIndex S A H K → PMF S := fun c => M.transition c.1 c.2.1 c.2.2.1
  set g : Fin (m + 1) → TapeIndex S A H K := fun i => (h, s, a, ⟨i, drawIndex_lt m i⟩)
  set ind : S → ℝ := fun x => if x ∈ ({t} : Finset S) then (1 : ℝ) else 0
  set p := (M.transition h s a t).toReal
  have hg : Function.Injective g := by
    intro i j hij
    simp only [g, Prod.mk.injEq, Fin.mk.injEq, true_and] at hij
    exact Fin.ext hij
  have hfm : Measurable ind := measurable_of_countable ind
  have hall : iIndepFun (fun (c : TapeIndex S A H K) (ω : TapeIndex S A H K → S) => ω c)
      (M.tapeLaw H K) :=
    iIndepFun_pi (μ := fun c => (ν c).toMeasure) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hindep := (hall.precomp hg).comp (fun _ => ind) (fun _ => hfm)
  have hlaw (i : Fin (m + 1)) (f : S → ℝ) :
      ∫ ω : TapeIndex S A H K → S, f (ω (g i)) ∂M.tapeLaw H K =
        expect (M.transition h s a) f := by
    have hmap : (M.tapeLaw H K).map (fun ω => ω (g i)) = (ν (g i)).toMeasure :=
      (measurePreserving_eval (fun c => (ν c).toMeasure) (g i)).map_eq
    rw [← integral_map (measurable_pi_apply (g i)).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable, hmap, integral_toMeasure_eq_expect]
  have hp : expect (M.transition h s a) ind = p := by
    rw [expect_indicator]; simp [p]
  have hp1 : p ≤ 1 := by
    have := Finset.single_le_sum (f := fun x => (M.transition h s a x).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ t)
    rwa [probability_sum] at this
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  exact measure_abs_sampleMean_sub_ge_le_bernstein
    (X := fun i (ω : TapeIndex S A H K → S) => ind (ω (g i))) hindep
    (fun i => (hfm.comp (measurable_pi_apply (g i))).aemeasurable) (M := 1) (σ2 := p) one_pos hp0
    (fun i => ae_of_all _ fun ω => by
      simp only [ind]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith)
    (fun i => by rw [hlaw i ind, hp])
    (fun i => by
      rw [hlaw i (fun x => (ind x - p) ^ 2)]
      have hpt (x : S) : (ind x - p) ^ 2 = (1 - 2 * p) * ind x + p ^ 2 := by
        simp only [ind]; split_ifs <;> ring
      simp only [hpt, expect_add, expect_mul, expect_const, hp]
      nlinarith) hδ0 hδ1

/-- The third bad event: some coordinate of some empirical model misses its probability by the
Bernstein width of Lemma 7.8. -/
def badCoord (M : EpisodicMDP S A) (H K : ℕ) (δ : ℝ) : Set (TapeIndex S A H K → S) :=
  {ω | ∃ h : Fin H, ∃ s a, ∃ m : Fin K, ∃ t : S,
    Real.sqrt (2 * (M.transition h s a t).toReal * Real.log (2 * (H * Fintype.card S *
      Fintype.card A * K * Fintype.card S) / δ) / (m + 1)) +
      2 * 1 * Real.log (2 * (H * Fintype.card S * Fintype.card A * K * Fintype.card S) / δ) /
        (3 * (m + 1)) ≤
    |sampleMean (fun i : Fin (m + 1) =>
      (fun x => if x ∈ ({t} : Finset S) then (1 : ℝ) else 0)
        (ω (h, s, a, ⟨i, drawIndex_lt m i⟩))) - (M.transition h s a t).toReal|}

omit [Nonempty A] [DecidableEq A] in
/-- **Uniform coordinate concentration (Lemma 7.8).** For `0 < δ ≤ 1`, the third bad event has
probability at most `δ`. -/
theorem measure_badCoord_le (M : EpisodicMDP S A) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (M.tapeLaw H K).real (M.badCoord H K δ) ≤ δ := by
  classical
  set C : ℝ := H * Fintype.card S * Fintype.card A * K * Fintype.card S
  have hC : C = Fintype.card (Fin H × S × A × Fin K × S) := by
    simp only [C, Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  by_cases hne : Nonempty (Fin H × S × A × Fin K × S)
  swap
  · have hempty : M.badCoord H K δ = ∅ := by
      ext ω
      simp only [badCoord, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun h s a m t _ => hne ⟨(h, s, a, m, t)⟩
    rw [hempty, measureReal_empty]
    exact hδ0.le
  have hC1 : 1 ≤ C := by rw [hC]; exact Nat.one_le_cast.mpr Fintype.card_pos
  set δ' := δ / C
  have hδ'0 : 0 < δ' := div_pos hδ0 (by linarith)
  have hδ'1 : δ' ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hlog : Real.log (2 / δ') = Real.log (2 * C / δ) := by
    simp only [δ']; congr 1; field_simp
  have hsub : M.badCoord H K δ ⊆ ⋃ q : Fin H × S × A × Fin K × S, {ω |
      Real.sqrt (2 * (M.transition q.1 q.2.1 q.2.2.1 q.2.2.2.2).toReal * Real.log (2 / δ') /
        (q.2.2.2.1 + 1)) + 2 * 1 * Real.log (2 / δ') / (3 * (q.2.2.2.1 + 1)) ≤
      |sampleMean (fun i : Fin (q.2.2.2.1 + 1) =>
        (fun x => if x ∈ ({q.2.2.2.2} : Finset S) then (1 : ℝ) else 0)
          (ω (q.1, q.2.1, q.2.2.1, ⟨i, drawIndex_lt q.2.2.2.1 i⟩))) -
        (M.transition q.1 q.2.1 q.2.2.1 q.2.2.2.2).toReal|} := by
    rintro ω ⟨h, s, a, m, t, hω⟩
    refine Set.mem_iUnion.mpr ⟨(h, s, a, m, t), ?_⟩
    simp only [Set.mem_ofPred_eq, hlog]
    exact hω
  refine (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
  calc _ ≤ ∑ _q : Fin H × S × A × Fin K × S, δ' := Finset.sum_le_sum fun q _ =>
        M.measure_tape_coord_le q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 hδ'0 hδ'1
    _ = δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hC]
        simp only [δ']
        field_simp

/-- `∑_{j < n} 1 / j ≤ 1 + log n`, with the term at `j = 0` equal to zero. -/
theorem sum_range_one_div_le_one_add_log (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / (j : ℝ) ≤ 1 + Real.log n := by
  rcases n with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    have hh := harmonic_le_one_add_log n
    have hcast : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ) := by
      simp [harmonic]
    rw [← hcast]
    refine hh.trans (add_le_add_right ?_ _)
    rcases n with _ | n
    · simp
    · exact Real.log_le_log (by positivity) (by push_cast; linarith)

omit [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Nonempty A] in
/-- `∑_{k < K} 1 / N_h^k` at one stage is at most `|S| |A| (1 + log K)`. -/
theorem sum_one_div_visitCount_le (τ : ℕ → ℕ → S × A) (h K : ℕ) [DecidableEq (S × A)] :
    ∑ k ∈ Finset.range K, 1 / (visitCount τ k h (τ k h) : ℝ) ≤
      Fintype.card S * Fintype.card A * (1 + Real.log K) := by
  rw [sum_visitCount_eq τ h (fun n => 1 / (n : ℝ)) K]
  calc ∑ x, ∑ j ∈ Finset.range (visitCount τ K h x), 1 / (j : ℝ)
      ≤ ∑ _x : S × A, (1 + Real.log K) := Finset.sum_le_sum fun x _ => by
        refine (sum_range_one_div_le_one_add_log _).trans (add_le_add_right ?_ _)
        rcases Nat.eq_zero_or_pos (visitCount τ K h x) with h0 | hpos
        · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
          rcases Nat.eq_zero_or_pos K with hK | hK
          · simp [hK]
          · exact Real.log_nonneg (by exact_mod_cast hK)
        · refine Real.log_le_log (by exact_mod_cast hpos) ?_
          have : visitCount τ K h x ≤ K := by
            simp only [visitCount]
            exact (Finset.card_filter_le _ _).trans (by simp)
          exact_mod_cast this
    _ = _ := by simp [Fintype.card_prod]; ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Off the coordinate bad event, every coordinate of every empirical model of episode `k < K`
satisfies the bound of Lemma 7.8 with `L' = log (2 H |S| |A| K |S| / δ)`. -/
theorem good_coord (M : EpisodicMDP S A) {L δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s₀ : S)
    (ω : TapeIndex S A H K → S)
    (hω : ω ∉ M.badCoord H K δ) {k : ℕ} (hk : k < K) (h : ℕ) (hh : h < H) (s : S) (a : A)
    (hpos : 0 < M.ucbviCounts H L s₀ (tapeSamples ω) k h s a) (t : S) :
    |(empiricalModel (tapeSamples ω) (M.ucbviCounts H L s₀ (tapeSamples ω) k) h s a t).toReal -
      (M.transition h s a t).toReal| ≤
      Real.sqrt (2 * (M.transition h s a t).toReal *
        Real.log (2 * (H * Fintype.card S * Fintype.card A * K * Fintype.card S) / δ) /
          M.ucbviCounts H L s₀ (tapeSamples ω) k h s a) +
      2 * Real.log (2 * (H * Fintype.card S * Fintype.card A * K * Fintype.card S) / δ) /
        M.ucbviCounts H L s₀ (tapeSamples ω) k h s a := by
  set N := M.ucbviCounts H L s₀ (tapeSamples ω) k
  set L' := Real.log (2 * (H * Fintype.card S * Fintype.card A * K * Fintype.card S) / δ)
  obtain ⟨m, hm, hN⟩ : ∃ m, m < K ∧ N h s a = m + 1 :=
    ⟨N h s a - 1, by
      have := M.ucbviCounts_le H L s₀ (tapeSamples ω) k h s a
      change N h s a ≤ k at this
      omega, by omega⟩
  simp only [badCoord, Set.mem_ofPred_eq, not_exists, not_le] at hω
  have hbad := (hω ⟨h, hh⟩ s a ⟨m, hm⟩ t).le
  have hP : (empiricalModel (tapeSamples ω) N h s a t).toReal =
      sampleMean (fun i : Fin (m + 1) =>
        (fun x => if x ∈ ({t} : Finset S) then (1 : ℝ) else 0)
          (ω (⟨h, hh⟩, s, a, ⟨i, drawIndex_lt (⟨m, hm⟩ : Fin K) i⟩))) := by
    have := expect_empiricalModel_tape ω N hh s a hm hN
      (fun x => if x ∈ ({t} : Finset S) then (1 : ℝ) else 0)
    rw [expect_indicator] at this
    simpa using this
  rw [hP, hN]
  refine hbad.trans ?_
  have hL'0 : 0 ≤ L' := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ0]
    have hS1 : (1 : ℝ) ≤ Fintype.card S := by
      have : Nonempty S := ⟨s₀⟩; exact Nat.one_le_cast.mpr Fintype.card_pos
    have hA1 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have := mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hH1 hS1 zero_le_one (by positivity))
      hA1 zero_le_one (by positivity)) hK1 zero_le_one (by positivity)) hS1 zero_le_one
      (by positivity)
    linarith
  push_cast
  have h3 : 2 * 1 * L' / (3 * ((m : ℝ) + 1)) ≤ 2 * L' / ((m : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  simp only [L'] at h3 ⊢
  linarith

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Off the value bad event, every episode `k < K` satisfies Lemma 7.3 with
`L = log (2 H |S| |A| K / δ)`. -/
theorem good_value (M : EpisodicMDP S A) (hH : 0 < H) (s₀ : S) {δ : ℝ}
    (ω : TapeIndex S A H K → S) (hω : ω ∉ M.badValue H K δ) {k : ℕ} (hk : k < K) :
    let L := Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)
    let N := M.ucbviCounts H L s₀ (tapeSamples ω) k
    ∀ h, h < H → ∀ s a, 0 < N h s a →
      |expect (empiricalModel (tapeSamples ω) N h s a) (M.optValue H (h + 1)) -
        expect (M.transition h s a) (M.optValue H (h + 1))| ≤
        2 * H * Real.sqrt (L / N h s a) := by
  intro L N h hh s a hpos
  simp only [badValue, Set.mem_ofPred_eq, not_exists, not_le] at hω
  set C : ℝ := H * Fintype.card S * Fintype.card A * K
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by
    have : Nonempty S := ⟨s₀⟩; exact Nat.one_le_cast.mpr Fintype.card_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hC1 : 1 ≤ C := by
    simp only [C]
    have := mul_le_mul hH1 hS1 zero_le_one (by positivity)
    have := mul_le_mul this hA1 zero_le_one (by positivity)
    have := mul_le_mul this hK1 zero_le_one (by positivity)
    linarith
  obtain ⟨m, hm, hN⟩ : ∃ m, m < K ∧ N h s a = m + 1 :=
    ⟨N h s a - 1, by
      have := M.ucbviCounts_le H L s₀ (tapeSamples ω) k h s a
      change N h s a ≤ k at this
      omega, by omega⟩
  rw [expect_empiricalModel_tape ω N hh s a hm hN, hN]
  have h1 := (hω () ⟨h, hh⟩ s a ⟨m, hm⟩).le
  simp only [Fintype.card_unit, Nat.cast_one, one_mul] at h1
  refine h1.trans ?_
  push_cast
  have hsq : Real.sqrt (2 * L / (m + 1)) ≤ 2 * Real.sqrt (L / (m + 1)) := by
    rw [show 2 * L / (m + 1) = 2 * (L / (m + 1)) by ring, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  simp only [L] at hsq ⊢
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ H)]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- **Counting the refined costs.** Along the realized trajectories, the refined visit costs add
up to at most `2 H ^ 2 |S| |A| + 8 H ^ 2 √L √(|S| |A| K) + 3 H ^ 3 |S| ^ 2 |A| L' (1 + log K)`. -/
theorem sum_refinedCost_le (M : EpisodicMDP S A) (H : ℕ) {L L' : ℝ} (hL' : 0 ≤ L') (s₀ : S)
    (samples : ℕ → S → A → ℕ → S) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, refinedCost S H L L'
      (M.ucbviCounts H L s₀ samples k h (M.ucbviTrajectory H L s₀ samples k h).1
        (M.ucbviTrajectory H L s₀ samples k h).2) ≤
      2 * H * (H * (Fintype.card S * Fintype.card A)) +
        4 * H * Real.sqrt L * (2 * H * Real.sqrt (Fintype.card (S × A) * K)) +
        3 * H ^ 2 * Fintype.card S * L' *
          (H * (Fintype.card S * Fintype.card A * (1 + Real.log K))) := by
  set τ : ℕ → ℕ → S × A := fun k h => M.ucbviTrajectory H L s₀ samples k h
  have hN (k h : ℕ) : M.ucbviCounts H L s₀ samples k h (τ k h).1 (τ k h).2 =
      visitCount τ k h (τ k h) := rfl
  have hcost (n : ℕ) : refinedCost S H L L' n ≤
      2 * H * (if n = 0 then 1 else 0) + 4 * H * Real.sqrt L * (1 / Real.sqrt n) +
        3 * H ^ 2 * Fintype.card S * L' * (1 / (n : ℝ)) := by
    unfold refinedCost
    split_ifs with hn
    · subst hn; simp
    · rw [Real.sqrt_div' _ (Nat.cast_nonneg n)]
      simp only [mul_zero, zero_add]
      apply le_of_eq
      field_simp
  have hfirst (h : ℕ) : ∑ k ∈ Finset.range K, (if visitCount τ k h (τ k h) = 0 then (1 : ℝ)
      else 0) ≤ Fintype.card S * Fintype.card A := by
    rw [sum_visitCount_eq τ h (fun j => if j = 0 then (1 : ℝ) else 0) K]
    calc ∑ x, ∑ j ∈ Finset.range (visitCount τ K h x), (if j = 0 then (1 : ℝ) else 0)
        ≤ ∑ _x : S × A, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
          rw [Finset.sum_ite_eq']
          split_ifs <;> norm_num
      _ = _ := by simp [Fintype.card_prod]
  have hpig := sum_one_div_sqrt_visitCount_le τ H K
  have hharm : ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K, 1 / (visitCount τ k h (τ k h) : ℝ) ≤
      H * (Fintype.card S * Fintype.card A * (1 + Real.log K)) := by
    calc _ ≤ ∑ _h ∈ Finset.range H, (Fintype.card S * Fintype.card A * (1 + Real.log K)) :=
          Finset.sum_le_sum fun h _ => sum_one_div_visitCount_le τ h K
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, refinedCost S H L L'
        (M.ucbviCounts H L s₀ samples k h (τ k h).1 (τ k h).2)
      ≤ ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        (2 * H * (if visitCount τ k h (τ k h) = 0 then 1 else 0) +
          4 * H * Real.sqrt L * (1 / Real.sqrt (visitCount τ k h (τ k h))) +
          3 * H ^ 2 * Fintype.card S * L' * (1 / (visitCount τ k h (τ k h) : ℝ))) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun h _ => by rw [hN]; exact hcost _
    _ = 2 * H * ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K,
          (if visitCount τ k h (τ k h) = 0 then (1 : ℝ) else 0) +
        4 * H * Real.sqrt L * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
          1 / Real.sqrt (visitCount τ k h (τ k h)) +
        3 * H ^ 2 * Fintype.card S * L' * ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K,
          1 / (visitCount τ k h (τ k h) : ℝ) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm (f := fun k h => if visitCount τ k h (τ k h) = 0 then (1 : ℝ) else 0),
          Finset.sum_comm (f := fun k h => 1 / (visitCount τ k h (τ k h) : ℝ))]
    _ ≤ _ := by
        have h1 : ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range K,
            (if visitCount τ k h (τ k h) = 0 then (1 : ℝ) else 0) ≤
            H * (Fintype.card S * Fintype.card A) := by
          calc _ ≤ ∑ _h ∈ Finset.range H, ((Fintype.card S : ℝ) * Fintype.card A) :=
                Finset.sum_le_sum fun h _ => hfirst h
            _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        gcongr

/-- **Improved regret of UCB-VI (Agarwal, Jiang, Kakade, and Sun, Theorem 7.6).** Take rewards in
`[0, 1]`, horizon `H > 0`, `K` episodes from `s₀`, `0 < δ ≤ 1`, the bonus with
`L = log (2 H |S| |A| K / δ)`, and `L' = log (2 H |S| |A| K |S| / δ)`. Then the expected regret is
at most `e (2 H ^ 2 |S| |A| + 8 H ^ 2 √L √(|S| |A| K) + 3 H ^ 3 |S| ^ 2 |A| L' (1 + log K)) +
2 δ K H`. -/
theorem regret_ucbvi_refined_le (M : EpisodicMDP S A)
    (hr : ∀ h s a, M.reward h s a ∈ Set.Icc (0 : ℝ) 1) (hH : 0 < H) (s₀ : S) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ ω, ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (M.ucbviPolicyAt H
        (Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)) s₀ (tapeSamples ω) k)
        H 0 s₀) ∂M.tapeLaw H K ≤
      Real.exp 1 * (2 * H * (H * (Fintype.card S * Fintype.card A)) +
        4 * H * Real.sqrt (Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)) *
          (2 * H * Real.sqrt (Fintype.card (S × A) * K)) +
        3 * H ^ 2 * Fintype.card S *
          Real.log (2 * (H * Fintype.card S * Fintype.card A * K * Fintype.card S) / δ) *
          (H * (Fintype.card S * Fintype.card A * (1 + Real.log K)))) + 2 * δ * (K * H) := by
  set L := Real.log (2 * (H * Fintype.card S * Fintype.card A * K) / δ)
  set L' := Real.log (2 * (H * Fintype.card S * Fintype.card A * K * Fintype.card S) / δ)
  set μ := M.tapeLaw H K
  set Bad := M.badValue H K δ ∪ M.badCoord H K δ
  set π : ℕ → (TapeIndex S A H K → S) → EpisodicPolicy S A :=
    fun k ω => M.ucbviPolicyAt H L s₀ (tapeSamples ω) k
  set N : ℕ → (TapeIndex S A H K → S) → ℕ → S → A → ℕ :=
    fun k ω => M.ucbviCounts H L s₀ (tapeSamples ω) k
  set cost : ℕ → ℕ → (TapeIndex S A H K → S) → S → ℝ :=
    fun k h ω s => refinedCost S H L L' (N k ω h s (π k ω h s))
  set C := 2 * H * (H * (Fintype.card S * Fintype.card A)) +
    4 * H * Real.sqrt L * (2 * H * Real.sqrt (Fintype.card (S × A) * K)) +
    3 * H ^ 2 * Fintype.card S * L' * (H * (Fintype.card S * Fintype.card A * (1 + Real.log K)))
  have hL'0 : 0 ≤ L' ∨ K = 0 := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · right; exact hK
    · left
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hδ0]
      have hS1 : (1 : ℝ) ≤ Fintype.card S := by
        have : Nonempty S := ⟨s₀⟩; exact Nat.one_le_cast.mpr Fintype.card_pos
      have hA1 : (1 : ℝ) ≤ Fintype.card A := Nat.one_le_cast.mpr Fintype.card_pos
      have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have := mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hH1 hS1 zero_le_one
        (by positivity)) hA1 zero_le_one (by positivity)) hK1 zero_le_one (by positivity)) hS1
        zero_le_one (by positivity)
      linarith
  rcases hL'0 with hL'0 | hK0
  swap
  · -- No episodes: the regret is zero.
    subst hK0
    simp only [Finset.range_zero, Finset.sum_empty, integral_zero]
    have hL'z : L' = 0 := by simp [L']
    have : 0 ≤ C := by
      simp only [C, hL'z, mul_zero, zero_mul, add_zero]
      positivity
    positivity
  have hVle (k : ℕ) (ω : TapeIndex S A H K → S) :
      M.optValue H 0 s₀ - M.value (π k ω) H 0 s₀ ≤ H := by
    have h1 := M.optValue_le (fun h s a => (hr h s a).2) (Nat.zero_le H) s₀
    have h2 := M.value_nonneg (fun h s a => (hr h s a).1) (π k ω) H 0 s₀
    push_cast at h1
    linarith
  have hcost0 (k h : ℕ) (ω : TapeIndex S A H K → S) (t : S) : 0 ≤ cost k h ω t :=
    refinedCost_nonneg H hL'0 _
  have hpt (ω : TapeIndex S A H K → S) :
      ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (π k ω) H 0 s₀) ≤
        Real.exp 1 * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
          expect (M.stateDist (π k ω) s₀ h) (cost k h ω) +
        Bad.indicator (fun _ => (K : ℝ) * H) ω := by
    have hsum0 : 0 ≤ Real.exp 1 * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        expect (M.stateDist (π k ω) s₀ h) (cost k h ω) :=
      mul_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun h _ => by
        have := expect_mono (M.stateDist (π k ω) s₀ h) (f := fun _ => 0) (hcost0 k h ω)
        rwa [expect_zero] at this)
    by_cases hω : ω ∈ Bad
    · rw [Set.indicator_of_mem hω]
      calc _ ≤ ∑ _k ∈ Finset.range K, (H : ℝ) := Finset.sum_le_sum fun k _ => hVle k ω
        _ = K * H := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := by linarith
    · rw [Set.indicator_of_notMem hω, add_zero, Finset.mul_sum]
      simp only [Bad, Set.mem_union, not_or] at hω
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      exact M.optValue_sub_value_ucbviPolicy_le_refined hr hH hL'0 (tapeSamples ω) (N k ω) s₀
        (M.good_value hH s₀ ω hω.1 hk') (fun h hh s a hpos t =>
          M.good_coord hδ0 hδ1 s₀ ω hω.2 hk' h hh s a hpos t)
  have hint : ∫ ω, ∑ k ∈ Finset.range K, (M.optValue H 0 s₀ - M.value (π k ω) H 0 s₀) ∂μ ≤
      Real.exp 1 * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        ∫ ω, expect (M.stateDist (π k ω) s₀ h) (cost k h ω) ∂μ + (K * H) * μ.real Bad := by
    calc _ ≤ ∫ ω, (Real.exp 1 * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
          expect (M.stateDist (π k ω) s₀ h) (cost k h ω) +
          Bad.indicator (fun _ => (K : ℝ) * H) ω) ∂μ :=
          integral_mono Integrable.of_finite Integrable.of_finite hpt
      _ = _ := by
          rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
            integral_finsetSum _ fun k _ => Integrable.of_finite]
          simp only [integral_finsetSum _ fun h _ => Integrable.of_finite]
          rw [integral_indicator_const _ (MeasurableSet.of_discrete), smul_eq_mul, mul_comm
            (μ.real Bad)]
  have hlaw : ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
      ∫ ω, expect (M.stateDist (π k ω) s₀ h) (cost k h ω) ∂μ =
      ∫ ω, ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, refinedCost S H L L'
        (M.ucbviCounts H L s₀ (tapeSamples ω) k h
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2) ∂μ := by
    rw [integral_finsetSum _ fun k _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ fun h _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun h hh => ?_
    have hpast : ∀ y, M.IsPast H K L s₀ k fun ω => cost k h ω y := by
      intro y ω ω' hagree
      obtain ⟨hN, hπ⟩ := M.ucbviCounts_policy_congr L s₀ k hagree
      simp only [cost, N, π, hN, hπ]
    rw [← M.integral_ucbviTrajectory_eq_stateDist L s₀ (Finset.mem_range.mp hk) h
      (Finset.mem_range.mp hh).le (cost k h) hpast]
    congr 1
    funext ω
    simp only [cost, N, π]
    rw [show (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2 =
      M.ucbviPolicyAt H L s₀ (tapeSamples ω) k h
        (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1 by rw [ucbviTrajectory_eq]]
  have hpath : ∫ ω, ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, refinedCost S H L L'
        (M.ucbviCounts H L s₀ (tapeSamples ω) k h
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).1
          (M.ucbviTrajectory H L s₀ (tapeSamples ω) k h).2) ∂μ ≤ C := by
    calc _ ≤ ∫ _ω, C ∂μ := integral_mono Integrable.of_finite Integrable.of_finite
          fun ω => M.sum_refinedCost_le H hL'0 s₀ (tapeSamples ω) K
      _ = C := by simp
  have hbad : μ.real Bad ≤ 2 * δ := by
    have h1 := M.measure_tape_exists_le (H := H) (K := K) (J := Unit)
      (fun _ h t => M.optValue H (h + 1) t) (B := H) (by exact_mod_cast hH) (fun _ h t => by
        have h0 := M.optValue_nonneg (fun h s a => (hr h s a).1) H (h + 1) t
        rw [abs_of_nonneg h0]
        by_cases hh : h + 1 ≤ H
        · have := M.optValue_le (fun h s a => (hr h s a).2) hh t
          push_cast at this
          linarith
        · rw [M.optValue_of_le (by omega)]; positivity) hδ0 hδ1
    have h2 := M.measure_badCoord_le (H := H) (K := K) hδ0 hδ1
    calc _ ≤ μ.real (M.badValue H K δ) + μ.real (M.badCoord H K δ) := measureReal_union_le _ _
      _ ≤ δ + δ := add_le_add h1 h2
      _ = 2 * δ := by ring
  have hKH : (0 : ℝ) ≤ K * H := by positivity
  calc _ ≤ Real.exp 1 * ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        ∫ ω, expect (M.stateDist (π k ω) s₀ h) (cost k h ω) ∂μ + (K * H) * μ.real Bad := hint
    _ ≤ Real.exp 1 * C + (K * H) * (2 * δ) := by
        rw [hlaw]
        exact add_le_add (mul_le_mul_of_nonneg_left hpath (Real.exp_pos 1).le)
          (mul_le_mul_of_nonneg_left hbad hKH)
    _ = _ := by simp only [C]; ring

end EpisodicMDP

end Rlib
