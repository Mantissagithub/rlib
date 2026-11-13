module

public import Rlib.MDP.PerformanceDifference

/-! # Discounted state visitation

The discounted visitation of a state is `1 - γ` times the value of the policy when the reward
is one at that state and zero elsewhere. Values with any reward are averages of the expected
reward under this visitation.
-/

@[expose] public section

noncomputable section

namespace Rlib.MDP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- The discounted visitation of state `s` from start state `s₀` under a stationary policy. -/
def discountedVisitation (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (s₀ s : S) : ℝ :=
  (1 - γ) * (m.withReward fun t _ => if t = s then 1 else 0).policyValue π hγ0 hγ1 s₀

/-- **Value as an average over discounted visitation.** For a discount in `[0, 1)` and any
reward `g`, `1 - γ` times the value of a policy is the sum over states of the discounted
visitation times the expected reward there. -/
theorem policyValue_withReward_eq_sum (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → A → ℝ) (s₀ : S) :
    (1 - γ) * (m.withReward g).policyValue π hγ0 hγ1 s₀ =
      ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * expect (π s) (g s) := by
  set ind : S → S → A → ℝ := fun s t _ => if t = s then 1 else 0
  set W : S → S → ℝ := fun s => (m.withReward (ind s)).policyValue π hγ0 hγ1
  set gbar : S → ℝ := fun s => expect (π s) (g s)
  have hW (s t : S) : W s t = (if t = s then 1 else 0) +
      γ * expect (π t) (fun a => expect (m.transition t a) (W s)) := by
    have h := congrFun ((m.withReward (ind s)).oneStepValue_policyValue π hγ0 hγ1) t
    change expect (π t) (fun a => (if t = s then 1 else 0) +
      γ * expect (m.transition t a) (W s)) = W s t at h
    rw [expect_add, expect_const, expect_mul] at h
    exact h.symm
  set F : S → ℝ := fun t => ∑ s, gbar s * W s t
  have hF : F = (m.withReward g).policyValue π hγ0 hγ1 := by
    apply eq_policyValue_of_fixedPoint
    funext t
    have hinner (a : A) : expect (m.transition t a) F =
        ∑ s, gbar s * expect (m.transition t a) (W s) := by
      simp only [F]
      rw [expect_sum]
      exact Finset.sum_congr rfl fun s _ => expect_mul _ _ _
    change expect (π t) (fun a => g t a + γ * expect (m.transition t a) F) = F t
    simp only [hinner]
    rw [expect_add, expect_mul]
    have hswap : expect (π t) (fun a => ∑ s, gbar s * expect (m.transition t a) (W s)) =
        ∑ s, gbar s * expect (π t) (fun a => expect (m.transition t a) (W s)) := by
      rw [expect_sum]
      exact Finset.sum_congr rfl fun s _ => expect_mul _ _ _
    rw [hswap]
    symm
    calc
      F t = ∑ s, (gbar s * (if t = s then 1 else 0) +
          γ * (gbar s * expect (π t) (fun a => expect (m.transition t a) (W s)))) :=
        Finset.sum_congr rfl fun s _ => by
          rw [hW s t]
          ring
      _ = ∑ s, gbar s * (if t = s then 1 else 0) +
          γ * ∑ s, gbar s * expect (π t) (fun a => expect (m.transition t a) (W s)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = expect (π t) (g t) +
          γ * ∑ s, gbar s * expect (π t) (fun a => expect (m.transition t a) (W s)) := by
        simp [gbar]
  rw [← hF]
  simp only [F, discountedVisitation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by
    simp only [W, ind, gbar]
    ring

/-- Discounted visitation is nonnegative. -/
theorem discountedVisitation_nonneg (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ s : S) : 0 ≤ m.discountedVisitation π hγ0 hγ1 s₀ s := by
  refine mul_nonneg (sub_nonneg.mpr hγ1.le) ((m.withReward _).policyValue_nonneg π hγ0 hγ1
    (fun t => ?_) s₀)
  have h := expect_mono (π t) (f := fun _ => (0 : ℝ))
    (g := fun _ => if t = s then (1 : ℝ) else 0) fun a => by split_ifs <;> norm_num
  rw [expect_zero] at h
  exact h

/-- Discounted visitation sums to one over states. -/
theorem sum_discountedVisitation (m : MDP S A) (π : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ : S) : ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s = 1 := by
  have h := m.policyValue_withReward_eq_sum π hγ0 hγ1 (fun _ _ => 1) s₀
  have hone : (m.withReward fun _ _ => (1 : ℝ)).policyValue π hγ0 hγ1 = fun _ => 1 / (1 - γ) := by
    symm
    apply eq_policyValue_of_fixedPoint
    funext t
    change expect (π t) (fun _ => 1 + γ * expect (m.transition t _) fun _ => 1 / (1 - γ)) =
      1 / (1 - γ)
    simp only [expect_const]
    field_simp [(sub_pos.mpr hγ1).ne']
    ring
  simp only [hone, expect_const, mul_one] at h
  rw [← h]
  field_simp [(sub_pos.mpr hγ1).ne']

/-- **Performance difference lemma, visitation form.** For a discount in `[0, 1)`, `1 - γ` times
the gain of `π'` over `π` from a start state is the average over the discounted visitation of
`π'` of the expected advantage of `π` under `π'`. -/
theorem sub_policyValue_eq_sum_visitation (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ : S) :
    (1 - γ) * (m.policyValue π' hγ0 hγ1 s₀ - m.policyValue π hγ0 hγ1 s₀) =
      ∑ s, m.discountedVisitation π' hγ0 hγ1 s₀ s *
        expect (π' s) (m.advantage π hγ0 hγ1 s) := by
  rw [← Pi.sub_apply (m.policyValue π' hγ0 hγ1), m.policyValue_sub_policyValue π π' hγ0 hγ1,
    m.policyValue_withReward_eq_sum π' hγ0 hγ1]

end Rlib.MDP
