module

public import Rlib.MDP.PolicyGradient
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Softmax policies and their gradient

A softmax policy chooses actions with probabilities proportional to the exponential of action
scores. Moving the scores in a direction `u` changes the policy value at rate
`(1 - γ)⁻¹ * ∑ s, d s * ∑ a, π a * u s a * A s a`.
-/

@[expose] public section

noncomputable section

namespace Rlib

variable {S A : Type*} [Fintype A] [Nonempty A]

/-- The softmax policy with action scores `θ`. -/
def softmaxPolicy (θ : S → A → ℝ) : StationaryPolicy S A := fun s =>
  PMF.ofFintype (fun a => ENNReal.ofReal (Real.exp (θ s a) / ∑ b, Real.exp (θ s b))) (by
    have hZ : 0 < ∑ b, Real.exp (θ s b) := Finset.sum_pos (fun b _ => Real.exp_pos _)
      Finset.univ_nonempty
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => by positivity, ← Finset.sum_div,
      div_self hZ.ne', ENNReal.ofReal_one])

/-- Softmax probabilities are normalized exponentials of the scores. -/
theorem softmaxPolicy_apply (θ : S → A → ℝ) (s : S) (a : A) :
    (softmaxPolicy θ s a).toReal = Real.exp (θ s a) / ∑ b, Real.exp (θ s b) := by
  simp only [softmaxPolicy, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (by positivity)

/-- Moving softmax scores in direction `u` changes each action probability at rate
`π a * (u a - ∑ b, π b * u b)`. -/
theorem hasDerivAt_softmaxPolicy (θ u : S → A → ℝ) (s : S) (a : A) :
    HasDerivAt (fun t => (softmaxPolicy (fun s a => θ s a + t * u s a) s a).toReal)
      ((softmaxPolicy θ s a).toReal *
        (u s a - ∑ b, (softmaxPolicy θ s b).toReal * u s b)) 0 := by
  have hexp (b : A) : HasDerivAt (fun t => Real.exp (θ s b + t * u s b))
      (Real.exp (θ s b) * u s b) 0 := by
    have := ((hasDerivAt_mul_const (u s b)).const_add (θ s b)).exp (x := 0)
    simpa using this
  have hZ : 0 < ∑ b, Real.exp (θ s b) := Finset.sum_pos (fun b _ => Real.exp_pos _)
    Finset.univ_nonempty
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun b t => Real.exp (θ s b + t * u s b)) fun b _ => hexp b
  have hdiv := (hexp a).div hsum (by simpa using hZ.ne')
  simp only [softmaxPolicy_apply]
  convert hdiv using 1
  have hsum' : (∑ b, Real.exp (θ s b) / (∑ c, Real.exp (θ s c)) * u s b) =
      (∑ b, Real.exp (θ s b) * u s b) / ∑ c, Real.exp (θ s c) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [zero_mul, add_zero, hsum']
  field_simp

namespace MDP

variable [Fintype S] [DecidableEq S]

/-- **Softmax policy gradient along a direction.** Moving softmax scores `θ` in direction `u`
changes the value of the softmax policy at rate
`(1 - γ)⁻¹ * ∑ s, d s * ∑ a, π a * u s a * A s a`, where `π`, `d`, and `A` are the softmax
policy, its discounted visitation, and its advantage. -/
theorem hasDerivAt_policyValue_softmax (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (θ u : S → A → ℝ) (s₀ : S) :
    HasDerivAt (fun t => m.policyValue (softmaxPolicy fun s a => θ s a + t * u s a) hγ0 hγ1 s₀)
      ((1 - γ)⁻¹ * ∑ s, m.discountedVisitation (softmaxPolicy θ) hγ0 hγ1 s₀ s *
        ∑ a, (softmaxPolicy θ s a).toReal * u s a *
          m.advantage (softmaxPolicy θ) hγ0 hγ1 s a) 0 := by
  have h := m.hasDerivAt_policyValue (fun t => softmaxPolicy fun s a => θ s a + t * u s a)
    hγ0 hγ1 _ (fun s a => hasDerivAt_softmaxPolicy θ u s a) s₀
  have hθ : (softmaxPolicy fun s a => θ s a + (0 : ℝ) * u s a) = softmaxPolicy θ := by
    simp
  simp only [hθ] at h
  have heq : (∑ s, m.discountedVisitation (softmaxPolicy θ) hγ0 hγ1 s₀ s *
      ∑ a, (softmaxPolicy θ s a).toReal * (u s a - ∑ b, (softmaxPolicy θ s b).toReal * u s b) *
        m.advantage (softmaxPolicy θ) hγ0 hγ1 s a) =
      ∑ s, m.discountedVisitation (softmaxPolicy θ) hγ0 hγ1 s₀ s *
        ∑ a, (softmaxPolicy θ s a).toReal * u s a *
          m.advantage (softmaxPolicy θ) hγ0 hγ1 s a := by
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    have hzero := m.expect_advantage (softmaxPolicy θ) hγ0 hγ1 s
    unfold expect at hzero
    have hsplit (a : A) : (softmaxPolicy θ s a).toReal *
        (u s a - ∑ b, (softmaxPolicy θ s b).toReal * u s b) *
          m.advantage (softmaxPolicy θ) hγ0 hγ1 s a =
        (softmaxPolicy θ s a).toReal * u s a * m.advantage (softmaxPolicy θ) hγ0 hγ1 s a -
          (∑ b, (softmaxPolicy θ s b).toReal * u s b) *
            ((softmaxPolicy θ s a).toReal * m.advantage (softmaxPolicy θ) hγ0 hγ1 s a) := by
      ring
    simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, sub_zero]
  rw [← heq]
  exact h

variable [DecidableEq A]

/-- **Softmax policy gradient.** The partial derivative of the softmax policy value with respect
to the score of action `a₁` at state `s₁` is `(1 - γ)⁻¹ * d s₁ * π a₁ * A s₁ a₁`. -/
theorem hasDerivAt_policyValue_softmax_single (m : MDP S A) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (θ : S → A → ℝ) (s₀ s₁ : S) (a₁ : A) :
    HasDerivAt (fun t => m.policyValue (softmaxPolicy fun s a =>
        θ s a + t * (if s = s₁ ∧ a = a₁ then 1 else 0)) hγ0 hγ1 s₀)
      ((1 - γ)⁻¹ * m.discountedVisitation (softmaxPolicy θ) hγ0 hγ1 s₀ s₁ *
        (softmaxPolicy θ s₁ a₁).toReal * m.advantage (softmaxPolicy θ) hγ0 hγ1 s₁ a₁) 0 := by
  convert m.hasDerivAt_policyValue_softmax hγ0 hγ1 θ
    (fun s a => if s = s₁ ∧ a = a₁ then 1 else 0) s₀ using 1
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single s₁ (fun s _ hs => by simp [hs]) (by simp),
    Finset.sum_eq_single a₁ (fun a _ ha => by simp [ha]) (by simp)]
  simp only [and_self, ↓reduceIte]
  ring

end MDP
end Rlib
