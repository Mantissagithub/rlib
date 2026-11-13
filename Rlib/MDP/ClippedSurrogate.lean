module

public import Rlib.MDP.Visitation

/-! # The PPO clipped surrogate objective

PPO scores a new policy by importance-weighted advantages of the old policy, and clips the
probability ratio so that moving beyond `[1 - ε, 1 + ε]` earns no extra credit.
-/

@[expose] public section

noncomputable section

namespace Rlib

/-- The clipped term for probability ratio `ρ`, advantage `adv`, and clip range `ε`. -/
def ppoClip (ε ρ adv : ℝ) : ℝ :=
  min (ρ * adv) (max (1 - ε) (min ρ (1 + ε)) * adv)

/-- The clipped term never exceeds the unclipped term. -/
theorem ppoClip_le (ε ρ adv : ℝ) : ppoClip ε ρ adv ≤ ρ * adv :=
  min_le_left _ _

/-- Inside the clip range the clipped term is the unclipped term. -/
theorem ppoClip_eq_of_mem {ε ρ : ℝ} (hlo : 1 - ε ≤ ρ) (hhi : ρ ≤ 1 + ε) (adv : ℝ) :
    ppoClip ε ρ adv = ρ * adv := by
  simp [ppoClip, min_eq_left hhi, max_eq_right hlo]

/-- With a nonnegative advantage, raising the ratio beyond `1 + ε` earns nothing more. -/
theorem ppoClip_of_le_ratio {ε ρ adv : ℝ} (hε : 0 ≤ ε) (hρ : 1 + ε ≤ ρ) (hadv : 0 ≤ adv) :
    ppoClip ε ρ adv = (1 + ε) * adv := by
  have hclip : max (1 - ε) (min ρ (1 + ε)) = 1 + ε := by
    rw [min_eq_right hρ, max_eq_right (by linarith)]
  rw [ppoClip, hclip, min_eq_right (mul_le_mul_of_nonneg_right hρ hadv)]

/-- With a nonpositive advantage, lowering the ratio below `1 - ε` earns nothing more. -/
theorem ppoClip_of_ratio_le {ε ρ adv : ℝ} (hε : 0 ≤ ε) (hρ : ρ ≤ 1 - ε) (hadv : adv ≤ 0) :
    ppoClip ε ρ adv = (1 - ε) * adv := by
  have hclip : max (1 - ε) (min ρ (1 + ε)) = 1 - ε := by
    rw [min_eq_left (by linarith), max_eq_left hρ]
  rw [ppoClip, hclip, min_eq_right (mul_le_mul_of_nonpos_right hρ hadv)]

variable {X : Type*} [Fintype X]

/-- **Importance weighting.** If `p` is positive wherever `q` is, reweighting by `q / p` turns
an expectation under `p` into an expectation under `q`. -/
theorem expect_ratio_mul (p q : PMF X) (hsupp : ∀ x, q x ≠ 0 → p x ≠ 0) (f : X → ℝ) :
    expect p (fun x => (q x).toReal / (p x).toReal * f x) = expect q f := by
  unfold expect
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hq : q x = 0
  · simp [hq]
  · have hp : (p x).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨hsupp x hq, PMF.apply_ne_top p x⟩
    field_simp

namespace MDP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- The probability ratio of a new policy to an old one at a state and action. -/
def policyRatio (π π' : StationaryPolicy S A) (s : S) (a : A) : ℝ :=
  (π' s a).toReal / (π s a).toReal

/-- The surrogate objective: the old policy's visitation average of importance-weighted
advantages of the old policy. -/
def surrogate (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (s₀ : S) : ℝ :=
  ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s *
    expect (π s) (fun a => policyRatio π π' s a * m.advantage π hγ0 hγ1 s a)

/-- The PPO clipped surrogate objective with clip range `ε`. -/
def clippedSurrogate (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (ε : ℝ) (s₀ : S) : ℝ :=
  ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s *
    expect (π s) (fun a => ppoClip ε (policyRatio π π' s a) (m.advantage π hγ0 hγ1 s a))

/-- **Pessimism of the clipped surrogate.** The clipped surrogate never exceeds the surrogate. -/
theorem clippedSurrogate_le_surrogate (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (ε : ℝ) (s₀ : S) :
    m.clippedSurrogate π π' hγ0 hγ1 ε s₀ ≤ m.surrogate π π' hγ0 hγ1 s₀ :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (expect_mono _ fun _ => ppoClip_le _ _ _) (m.discountedVisitation_nonneg π hγ0 hγ1 s₀ s)

/-- If the old policy is positive wherever the new one is, the surrogate is the old policy's
visitation average of the new policy's expected advantage of the old policy. -/
theorem surrogate_eq (m : MDP S A) (π π' : StationaryPolicy S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hsupp : ∀ s a, π' s a ≠ 0 → π s a ≠ 0) (s₀ : S) :
    m.surrogate π π' hγ0 hγ1 s₀ =
      ∑ s, m.discountedVisitation π hγ0 hγ1 s₀ s * expect (π' s) (m.advantage π hγ0 hγ1 s) :=
  Finset.sum_congr rfl fun s _ => by
    rw [← expect_ratio_mul (π s) (π' s) (hsupp s)]
    rfl

end MDP
end Rlib
