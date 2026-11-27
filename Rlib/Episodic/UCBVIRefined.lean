module

public import Rlib.Episodic.UCBVIRegret

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

end EpisodicMDP

end Rlib
