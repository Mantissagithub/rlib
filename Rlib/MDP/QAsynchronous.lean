module

public import Rlib.MDP.QSynchronous
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Bellman Q iterations with per-entry step sizes

Each state-action entry has its own step size at each step. An entry with step size zero is
left unchanged, so this covers asynchronous updates that touch only some entries.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- Mix each entry with its exact Bellman Q target plus a target error, using that entry's own
step size. -/
def qAsyncIteration (m : MDP S A) (β : ℕ → S → A → ℝ) (γ : ℝ) (e : ℕ → S → A → ℝ)
    (q₀ : S → A → ℝ) : ℕ → S → A → ℝ
  | 0 => q₀
  | n + 1 => fun s a =>
    (1 - β n s a) * m.qAsyncIteration β γ e q₀ n s a +
      β n s a * (m.qBellmanOperator γ (m.qAsyncIteration β γ e q₀ n) s a + e n s a)

/-- With per-entry step sizes in `[0, 1]`, a discount in `[0, 1)`, and target errors bounded by
`E`, the distance to a Bellman Q fixed point never exceeds `max ‖q₀ - r‖ (E / (1 - γ))`. -/
theorem norm_qAsyncIteration_sub_le (m : MDP S A) {β : ℕ → S → A → ℝ} {γ E : ℝ}
    (hβ0 : ∀ n s a, 0 ≤ β n s a) (hβ1 : ∀ n s a, β n s a ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (e : ℕ → S → A → ℝ) (he : ∀ n, ‖e n‖ ≤ E) (q₀ r : S → A → ℝ)
    (hr : m.qBellmanOperator γ r = r) (n : ℕ) :
    ‖m.qAsyncIteration β γ e q₀ n - r‖ ≤ max ‖q₀ - r‖ (E / (1 - γ)) := by
  set M := max ‖q₀ - r‖ (E / (1 - γ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (le_max_left _ _)
  have hEM : γ * M + E ≤ M := by
    have h := (div_le_iff₀ (sub_pos.mpr hγ1)).1 (le_max_right ‖q₀ - r‖ (E / (1 - γ)))
    linarith
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    set q := m.qAsyncIteration β γ e q₀ n
    have hB : ‖m.qBellmanOperator γ q - r‖ ≤ γ * M := by
      have h := m.norm_qBellmanOperator_sub_le γ q r
      rw [Real.norm_of_nonneg hγ0, hr] at h
      exact h.trans (mul_le_mul_of_nonneg_left ih hγ0)
    apply (pi_norm_le_iff_of_nonneg hM0).2
    intro s
    apply (pi_norm_le_iff_of_nonneg hM0).2
    intro a
    have hq : |q s a - r s a| ≤ M := by
      have h := (norm_le_pi_norm ((q - r) s) a).trans (norm_le_pi_norm (q - r) s)
      rw [Real.norm_eq_abs] at h
      exact h.trans ih
    have hBe : |m.qBellmanOperator γ q s a - r s a| ≤ γ * M := by
      have h := (norm_le_pi_norm ((m.qBellmanOperator γ q - r) s) a).trans
        (norm_le_pi_norm (m.qBellmanOperator γ q - r) s)
      rw [Real.norm_eq_abs] at h
      exact h.trans hB
    have hee : |e n s a| ≤ E := by
      have h := (norm_le_pi_norm (e n s) a).trans (norm_le_pi_norm (e n) s)
      rw [Real.norm_eq_abs] at h
      exact h.trans (he n)
    have hstep : m.qAsyncIteration β γ e q₀ (n + 1) s a - r s a =
        (1 - β n s a) * (q s a - r s a) +
          β n s a * ((m.qBellmanOperator γ q s a - r s a) + e n s a) := by
      simp only [qAsyncIteration, q]
      ring
    change ‖m.qAsyncIteration β γ e q₀ (n + 1) s a - r s a‖ ≤ M
    rw [Real.norm_eq_abs, hstep]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hβ1 n s a)),
      abs_of_nonneg (hβ0 n s a)]
    have hinner := (abs_add_le (m.qBellmanOperator γ q s a - r s a) (e n s a)).trans
      (add_le_add hBe hee)
    nlinarith [mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr (hβ1 n s a)),
      mul_le_mul_of_nonneg_left hinner (hβ0 n s a), hβ0 n s a]

/-- Bellman Q iterations with per-entry step sizes converge to the Bellman Q fixed point when
every entry's step sizes lie in `[0, 1]` and are not summable, the iterates stay bounded, and
the step-weighted partial sums of each entry's target errors converge. -/
theorem tendsto_qAsyncIteration (m : MDP S A) {β : ℕ → S → A → ℝ} {γ : ℝ}
    (hβ0 : ∀ n s a, 0 ≤ β n s a) (hβ1 : ∀ n s a, β n s a ≤ 1)
    (hβsum : ∀ s a, ¬Summable fun n => β n s a) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (e : ℕ → S → A → ℝ)
    (he : ∀ s a, ∃ c, Tendsto (fun n => ∑ k ∈ Finset.range n, β k s a * e k s a) atTop (𝓝 c))
    (q₀ r : S → A → ℝ) (hr : m.qBellmanOperator γ r = r)
    (hbdd : ∃ K, ∀ n, ‖m.qAsyncIteration β γ e q₀ n‖ ≤ K) :
    Tendsto (m.qAsyncIteration β γ e q₀) atTop (𝓝 r) := by
  set q := m.qAsyncIteration β γ e q₀
  let W : ℕ → S → A → ℝ := fun n s a =>
    Nat.rec 0 (fun k Wk => (1 - β k s a) * Wk + β k s a * e k s a) n
  have hW : Tendsto W atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun s => tendsto_pi_nhds.2 fun a => ?_
    obtain ⟨c, hc⟩ := he s a
    exact tendsto_zero_of_eq_one_sub_mul_add_of_tendsto_sum (W := fun n => W n s a)
      (fun n => hβ0 n s a) (fun n => hβ1 n s a) (hβsum s a) hc fun n => rfl
  have hWn : Tendsto (fun n => ‖W n‖) atTop (𝓝 0) := by
    simpa using hW.norm
  set δ : ℕ → S → A → ℝ := fun n => q n - r - W n
  have hqr (n : ℕ) : q n - r = δ n + W n := by simp [δ]
  have hentry (n : ℕ) (s : S) (a : A) :
      |δ (n + 1) s a| ≤ (1 - β n s a) * |δ n s a| + β n s a * (γ * (‖δ n‖ + ‖W n‖)) := by
    have hB : ‖m.qBellmanOperator γ (q n) - r‖ ≤ γ * (‖δ n‖ + ‖W n‖) := by
      have h := m.norm_qBellmanOperator_sub_le γ (q n) r
      rw [Real.norm_of_nonneg hγ0, hr, hqr n] at h
      exact h.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hγ0)
    have hBe : |m.qBellmanOperator γ (q n) s a - r s a| ≤ γ * (‖δ n‖ + ‖W n‖) := by
      have h := (norm_le_pi_norm ((m.qBellmanOperator γ (q n) - r) s) a).trans
        (norm_le_pi_norm (m.qBellmanOperator γ (q n) - r) s)
      rw [Real.norm_eq_abs] at h
      exact h.trans hB
    have hstep : δ (n + 1) s a =
        (1 - β n s a) * δ n s a + β n s a * (m.qBellmanOperator γ (q n) s a - r s a) := by
      simp only [δ, q, Pi.sub_apply, qAsyncIteration]
      change _ - _ - ((1 - β n s a) * W n s a + β n s a * e n s a) = _
      ring
    rw [hstep]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hβ1 n s a)),
      abs_of_nonneg (hβ0 n s a)]
    linarith [mul_le_mul_of_nonneg_left hBe (hβ0 n s a)]
  have hratchet (D : ℝ) (hD : ∀ᶠ n in atTop, ‖δ n‖ ≤ D) {ε : ℝ} (hε : 0 < ε) :
      ∀ᶠ n in atTop, ‖δ n‖ ≤ γ * D + ε := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hD
    have hall : ∀ s a, ∀ᶠ n in atTop, |δ n s a| ≤ γ * D + ε := by
      intro s a
      have hrec (k : ℕ) : |δ (k + 1 + N) s a| - γ * D ≤
          (1 - β (k + N) s a) * (|δ (k + N) s a| - γ * D) +
            β (k + N) s a * (γ * ‖W (k + N)‖) := by
        have h := hentry (k + N) s a
        rw [show k + N + 1 = k + 1 + N by omega] at h
        have hδ := hN (k + N) (Nat.le_add_left N k)
        nlinarith [hβ0 (k + N) s a, mul_le_mul_of_nonneg_left hδ
          (mul_nonneg (hβ0 (k + N) s a) hγ0)]
      have hd : Tendsto (fun k => γ * ‖W (k + N)‖) atTop (𝓝 0) := by
        simpa using (hWn.comp (tendsto_add_atTop_nat N)).const_mul γ
      obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_le_of_le_one_sub_mul_add
        (x := fun k => |δ (k + N) s a| - γ * D) (a := fun k => β (k + N) s a)
        (fun k => hβ0 (k + N) s a) (fun k => hβ1 (k + N) s a)
        (fun h => hβsum s a ((summable_nat_add_iff N).1 h)) hd hrec hε)
      refine eventually_atTop.2 ⟨K + N, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + N := ⟨n - N, by omega⟩
      have := hK k (by omega)
      linarith
    have hall' : ∀ᶠ n in atTop, ∀ s a, |δ n s a| ≤ γ * D + ε :=
      eventually_all.2 fun s => eventually_all.2 fun a => hall s a
    filter_upwards [hall', hD] with n hn hnD
    have h0 : 0 ≤ γ * D + ε := by
      have := (norm_nonneg (δ n)).trans hnD
      positivity
    apply (pi_norm_le_iff_of_nonneg h0).2
    intro s
    apply (pi_norm_le_iff_of_nonneg h0).2
    intro a
    rw [Real.norm_eq_abs]
    exact hn s a
  obtain ⟨K, hK⟩ := hbdd
  set D₀ := K + ‖r‖ + 1
  have hD₀ : ∀ᶠ n in atTop, ‖δ n‖ ≤ D₀ := by
    filter_upwards [hWn.eventually (Iio_mem_nhds one_pos)] with n hn
    have h1 : ‖δ n‖ ≤ ‖q n - r‖ + ‖W n‖ := by
      have : δ n = (q n - r) - W n := rfl
      rw [this]
      exact norm_sub_le _ _
    have h2 : ‖q n - r‖ ≤ ‖q n‖ + ‖r‖ := norm_sub_le _ _
    linarith [hK n]
  have hD₀nonneg : 0 ≤ D₀ := by
    have := (norm_nonneg (q 0)).trans (hK 0)
    positivity
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hiter {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
      ∀ᶠ n in atTop, ‖δ n‖ ≤ γ ^ k * D₀ + ε / (1 - γ) := by
    induction k with
    | zero =>
      filter_upwards [hD₀] with n hn
      have : 0 ≤ ε / (1 - γ) := div_nonneg hε.le hγ.le
      simp only [pow_zero, one_mul]
      linarith
    | succ k ih =>
      filter_upwards [hratchet _ ih hε] with n hn
      have : γ * (γ ^ k * D₀ + ε / (1 - γ)) + ε = γ ^ (k + 1) * D₀ + ε / (1 - γ) := by
        field_simp
        ring
      linarith
  have hδ : Tendsto (fun n => ‖δ n‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const D₀
      |>.eventually (Iio_mem_nhds (by simpa using half_pos hη : (0 : ℝ) * D₀ < η / 2))).exists
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hiter (by positivity : 0 < η * (1 - γ) / 2) k)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    have heq : η * (1 - γ) / 2 / (1 - γ) = η / 2 := by
      field_simp
    rw [heq] at h
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    linarith
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hδ.add hWn)
  rw [hqr n]
  exact norm_add_le _ _

end Rlib.MDP
