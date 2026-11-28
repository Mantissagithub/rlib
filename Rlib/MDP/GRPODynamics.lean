module

public import Rlib.MDP.KLPenaltyPPO
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-! # GRPO dynamics with verifiable rewards

This file follows Mroueh, *Reinforcement Learning with Verifiable Rewards: GRPO's Loss, Dynamics,
and Success Amplification* (ICML 2026), Section 2. Fix one prompt with finitely many outcomes, a
binary reward `r`, a reference policy `π_ref`, a KL weight `β > 0`, and a stabilizer `ε > 0`.
With success probability `p` of the previous policy, GRPO's mean-and-standard-deviation
normalization gives each success the advantage `ω⁺ = (1 - p) / √(p (1 - p) + ε)` and each failure
`-ω⁻ = -p / √(p (1 - p) + ε)`. Each GRPO iteration maximizes, over policies `π`, the expected
advantage under `π` minus `β * KL (π ‖ π_ref)`.

* `isGRPOStep_iff`: the maximizer is unique and tilts `π_ref` by `exp (A / β)` (Theorem 1).
* `successProb_grpoPolicy_succ`: the success probabilities follow `p_n = h (p_{n-1})` with
  `h p = 1 / (1 + (1 - p_ref) / p_ref * exp (-1 / (β √(p (1 - p) + ε))))` (Theorem 2).
* `exists_grpoMap_fixedPoint`: `h` has a fixed point in `[0, 1]` (Proposition 1).
* `lt_grpoMap` and `successProb_grpoPolicy_gt`: if `0 < p_ref < 1`, every iterate after the first
  and every fixed point has success probability above `p_ref` (success amplification).
* `tendsto_successProb_grpoPolicy`: if `8 β ε √ε > 1`, the fixed point is unique and the success
  probabilities converge to it linearly with ratio `1 / (8 β ε √ε)`.

The paper proves convergence only locally, near a fixed point where `|h'| < 1`; the global
condition `8 β ε √ε > 1` is a sufficient condition added here, from `|h'| ≤ 1 / (8 β ε √ε)` on
`[0, 1]`. The formal KL divergence treats `0 * log (x / 0)` as `0`, so the statements assume that
`π_ref` gives every outcome positive probability, as a softmax policy does.
-/

@[expose] public section

noncomputable section

namespace Rlib

section Tilt

variable {X : Type*} [Fintype X]

/-- The normalizer `∑ x, q x * exp (g x)` of the Gibbs tilt. -/
def gibbsNormalizer (q : PMF X) (g : X → ℝ) : ℝ :=
  ∑ x, (q x).toReal * Real.exp (g x)

/-- The Gibbs normalizer is positive. -/
theorem gibbsNormalizer_pos (q : PMF X) (g : X → ℝ) : 0 < gibbsNormalizer q g := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < (q x).toReal := by
    by_contra h
    push Not at h
    have := probability_sum q
    have : ∑ x, (q x).toReal ≤ 0 := Finset.sum_nonpos fun x _ => h x
    linarith
  exact Finset.sum_pos' (fun y _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
    ⟨x, Finset.mem_univ x, mul_pos hx (Real.exp_pos _)⟩

/-- The Gibbs tilt of `q` by `exp g`: the distribution proportional to `q x * exp (g x)`. -/
def gibbsTilt (q : PMF X) (g : X → ℝ) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal ((q x).toReal * Real.exp (g x) / gibbsNormalizer q g))
    (by
      have hZ := gibbsNormalizer_pos q g
      rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => div_nonneg
        (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hZ.le, ← Finset.sum_div]
      change ENNReal.ofReal (gibbsNormalizer q g / gibbsNormalizer q g) = 1
      rw [div_self hZ.ne', ENNReal.ofReal_one])

/-- The Gibbs tilt gives `x` probability `q x * exp (g x) / Z`. -/
theorem gibbsTilt_apply (q : PMF X) (g : X → ℝ) (x : X) :
    (gibbsTilt q g x).toReal = (q x).toReal * Real.exp (g x) / gibbsNormalizer q g := by
  simp only [gibbsTilt, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (div_nonneg
    (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) (gibbsNormalizer_pos q g).le)

/-- The Gibbs tilt of a full-support distribution has full support. -/
theorem gibbsTilt_ne_zero (q : PMF X) (g : X → ℝ) (hq : ∀ x, q x ≠ 0) (x : X) :
    gibbsTilt q g x ≠ 0 := by
  intro h
  have := gibbsTilt_apply q g x
  rw [h, ENNReal.toReal_zero] at this
  exact (div_pos (mul_pos (ENNReal.toReal_pos (hq x) (q.apply_ne_top x)) (Real.exp_pos _))
    (gibbsNormalizer_pos q g)).ne' this.symm

/-- **Gibbs variational principle.** For `c > 0` and `q` with full support, a distribution
maximizes `E_p g - c * KL (p ‖ q)` exactly when it is the tilt of `q` by `exp (g / c)`. -/
theorem isMax_expect_sub_mul_kl_iff (q : PMF X) (g : X → ℝ) {c : ℝ} (hc : 0 < c)
    (hq : ∀ x, q x ≠ 0) (π : PMF X) :
    (∀ p : PMF X, expect p g - c * kl p q ≤ expect π g - c * kl π q) ↔
      π = gibbsTilt q fun x => g x / c := by
  set r := gibbsTilt q fun x => g x / c
  have hid (p : PMF X) : expect p g - c * kl p q =
      c * Real.log (gibbsNormalizer q fun x => g x / c) - c * kl p r :=
    expect_sub_mul_kl_eq p q r g hc.ne' (gibbsNormalizer_pos q _) hq
      (gibbsTilt_apply q fun x => g x / c)
  have hr := gibbsTilt_ne_zero q (fun x => g x / c) hq
  constructor
  · intro h
    have h1 := h r
    rw [hid, hid, kl_self] at h1
    have h2 := kl_nonneg_of_ne_zero π r hr
    exact eq_of_kl_eq_zero π r hr (le_antisymm (by nlinarith) h2)
  · rintro rfl p
    rw [hid, hid, kl_self]
    nlinarith [kl_nonneg_of_ne_zero p r hr]

end Tilt

section Dynamics

variable {O : Type*} [Fintype O] (r : O → Bool)

/-- The probability that an outcome drawn from `π` has reward one. -/
def successProb (π : PMF O) : ℝ :=
  expect π fun o => if r o then 1 else 0

/-- Success probabilities lie in `[0, 1]`. -/
theorem successProb_mem_Icc (π : PMF O) : successProb r π ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · calc (0 : ℝ) = expect π fun _ => 0 := (expect_const π 0).symm
      _ ≤ _ := expect_mono π fun o => by split_ifs <;> norm_num
  · calc successProb r π ≤ expect π fun _ => 1 := expect_mono π fun o => by split_ifs <;> norm_num
      _ = 1 := expect_const π 1

/-- GRPO's advantage of a success, `ω⁺ = (1 - p) / √(p (1 - p) + ε)`. -/
def grpoWeightPos (ε p : ℝ) : ℝ := (1 - p) / Real.sqrt (p * (1 - p) + ε)

/-- GRPO's advantage of a failure is `-ω⁻`, with `ω⁻ = p / √(p (1 - p) + ε)`. -/
def grpoWeightNeg (ε p : ℝ) : ℝ := p / Real.sqrt (p * (1 - p) + ε)

/-- GRPO's advantage of an outcome when the previous success probability is `p`. -/
def grpoAdvantage (ε p : ℝ) (o : O) : ℝ :=
  if r o then grpoWeightPos ε p else -grpoWeightNeg ε p

/-- One GRPO iteration in policy space: `π` maximizes the expected advantage under `π` minus
`β * KL (π ‖ π_ref)`, with advantages computed from the success probability `p`. -/
def IsGRPOStep (πref : PMF O) (β ε p : ℝ) (π : PMF O) : Prop :=
  ∀ σ : PMF O, expect σ (grpoAdvantage r ε p) - β * kl σ πref ≤
    expect π (grpoAdvantage r ε p) - β * kl π πref

/-- **GRPO policy dynamics (Mroueh, Theorem 1).** With `β > 0` and `π_ref` of full support, the
GRPO iteration has exactly one solution, the tilt of `π_ref` by `exp (A / β)`. -/
theorem isGRPOStep_iff (πref : PMF O) (hπref : ∀ o, πref o ≠ 0) {β : ℝ} (hβ : 0 < β)
    (ε p : ℝ) (π : PMF O) :
    IsGRPOStep r πref β ε p π ↔ π = gibbsTilt πref fun o => grpoAdvantage r ε p o / β :=
  isMax_expect_sub_mul_kl_iff πref _ hβ hπref π

/-- The GRPO iterates: `π₀ = π_ref`, and each step tilts `π_ref` by `exp (A / β)` with advantages
computed from the previous success probability. -/
def grpoPolicy (πref : PMF O) (β ε : ℝ) : ℕ → PMF O
  | 0 => πref
  | n + 1 => gibbsTilt πref fun o =>
      grpoAdvantage r ε (successProb r (grpoPolicy πref β ε n)) o / β

/-- Any sequence of GRPO iterations started at `π_ref` is `grpoPolicy`. -/
theorem eq_grpoPolicy (πref : PMF O) (hπref : ∀ o, πref o ≠ 0) {β : ℝ} (hβ : 0 < β) (ε : ℝ)
    (π : ℕ → PMF O) (h0 : π 0 = πref)
    (hstep : ∀ n, IsGRPOStep r πref β ε (successProb r (π n)) (π (n + 1))) (n : ℕ) :
    π n = grpoPolicy r πref β ε n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [(isGRPOStep_iff r πref hπref hβ ε _ _).mp (hstep n), ih]
    rfl

/-- The success-probability map `h p = 1 / (1 + (1 - p_ref) / p_ref * exp (-Ω p / β))`, where
`Ω p = 1 / √(p (1 - p) + ε)`. -/
def grpoMap (pref β ε p : ℝ) : ℝ :=
  (1 + (1 - pref) / pref * Real.exp (-(1 / Real.sqrt (p * (1 - p) + ε)) / β))⁻¹

/-- **Success-probability recursion (Mroueh, Theorem 2).** With `β > 0`, `π_ref` of full support,
and `p_ref > 0`, the success probability of each GRPO iterate is `h` of the previous one. -/
theorem successProb_grpoPolicy_succ (πref : PMF O) {β : ℝ} (hβ : 0 < β) (ε : ℝ)
    (hpref : 0 < successProb r πref) (n : ℕ) :
    successProb r (grpoPolicy r πref β ε (n + 1)) =
      grpoMap (successProb r πref) β ε (successProb r (grpoPolicy r πref β ε n)) := by
  set p := successProb r (grpoPolicy r πref β ε n)
  set pref := successProb r πref
  set a := grpoWeightPos ε p / β
  set b := -grpoWeightNeg ε p / β
  set g : O → ℝ := fun o => grpoAdvantage r ε p o / β
  have hg (o : O) :
      Real.exp (g o) = Real.exp b + (Real.exp a - Real.exp b) * if r o then 1 else 0 := by
    simp only [g, grpoAdvantage, a, b]
    split_ifs <;> simp [neg_div]
  have hZ : gibbsNormalizer πref g = pref * Real.exp a + (1 - pref) * Real.exp b := by
    simp only [gibbsNormalizer, hg]
    change expect πref (fun o => Real.exp b + (Real.exp a - Real.exp b) *
      (if r o then 1 else 0)) = _
    rw [expect_add, expect_const, expect_mul]
    simp only [pref, successProb]
    ring
  have hnum : successProb r (gibbsTilt πref g) =
      pref * Real.exp a / gibbsNormalizer πref g := by
    have (o : O) : (gibbsTilt πref g o).toReal * (if r o then 1 else 0) =
        (πref o).toReal * (if r o then 1 else 0) * Real.exp a / gibbsNormalizer πref g := by
      rw [gibbsTilt_apply]
      split_ifs with h
      · simp [g, grpoAdvantage, h, a]
      · simp
    simp only [successProb, expect, this, ← Finset.sum_div, ← Finset.sum_mul]
    rfl
  change successProb r (gibbsTilt πref g) = _
  rw [hnum, hZ, grpoMap]
  have hsum : a - b = 1 / Real.sqrt (p * (1 - p) + ε) / β := by
    simp only [a, b, grpoWeightPos, grpoWeightNeg]
    field_simp
    ring
  have hb : Real.exp b = Real.exp a * Real.exp (-(1 / Real.sqrt (p * (1 - p) + ε)) / β) := by
    rw [← Real.exp_add, neg_div, ← hsum]
    ring_nf
  rw [hb]
  have hea := Real.exp_pos a
  field_simp

/-- With `0 < p_ref < 1`, the map `h` exceeds `p_ref` wherever `p (1 - p) + ε > 0`. -/
theorem lt_grpoMap {pref β ε p : ℝ} (h0 : 0 < pref) (h1 : pref < 1) (hβ : 0 < β)
    (hu : 0 < p * (1 - p) + ε) : pref < grpoMap pref β ε p := by
  have hc : 0 < (1 - pref) / pref := div_pos (sub_pos.mpr h1) h0
  have he : Real.exp (-(1 / Real.sqrt (p * (1 - p) + ε)) / β) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos
      (one_div_pos.mpr (Real.sqrt_pos.mpr hu))) hβ)
  rw [grpoMap, lt_inv_comm₀ h0 (by positivity)]
  calc 1 + (1 - pref) / pref * Real.exp (-(1 / Real.sqrt (p * (1 - p) + ε)) / β)
      < 1 + (1 - pref) / pref := by nlinarith
    _ = pref⁻¹ := by field_simp; ring

/-- With `0 < p_ref ≤ 1`, the map `h` is positive. -/
theorem grpoMap_pos {pref β ε : ℝ} (h0 : 0 < pref) (h1 : pref ≤ 1) (p : ℝ) :
    0 < grpoMap pref β ε p := by
  have : 0 ≤ (1 - pref) / pref := div_nonneg (sub_nonneg.mpr h1) h0.le
  rw [grpoMap]
  positivity

/-- With `0 < p_ref < 1`, the map `h` is below one. -/
theorem grpoMap_lt_one {pref β ε : ℝ} (h0 : 0 < pref) (h1 : pref < 1) (p : ℝ) :
    grpoMap pref β ε p < 1 := by
  have : 0 < (1 - pref) / pref := div_pos (sub_pos.mpr h1) h0
  rw [grpoMap]
  exact inv_lt_one_of_one_lt₀ (by linarith [mul_pos this (Real.exp_pos
    (-(1 / Real.sqrt (p * (1 - p) + ε)) / β))])

/-- **Success amplification (Mroueh, Theorem 3).** With `0 < p_ref < 1`, `β > 0`, `ε > 0`, and
`π_ref` of full support, every GRPO iterate after the first succeeds with probability greater
than `p_ref`. -/
theorem successProb_grpoPolicy_gt (πref : PMF O) {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (h0 : 0 < successProb r πref) (h1 : successProb r πref < 1) (n : ℕ) :
    successProb r πref < successProb r (grpoPolicy r πref β ε (n + 1)) := by
  rw [successProb_grpoPolicy_succ r πref hβ ε h0]
  have hp := successProb_mem_Icc r (grpoPolicy r πref β ε n)
  exact lt_grpoMap h0 h1 hβ (by nlinarith [hp.1, hp.2])

/-- With `0 < p_ref ≤ 1` and `ε > 0`, the map `h` is continuous on `[0, 1]`. -/
theorem continuousOn_grpoMap {pref β ε : ℝ} (h0 : 0 < pref) (h1 : pref ≤ 1) (hε : 0 < ε) :
    ContinuousOn (grpoMap pref β ε) (Set.Icc 0 1) := by
  intro p hp
  have hu : 0 < p * (1 - p) + ε := by nlinarith [hp.1, hp.2]
  have hc : 0 ≤ (1 - pref) / pref := div_nonneg (sub_nonneg.mpr h1) h0.le
  refine ContinuousAt.continuousWithinAt ?_
  unfold grpoMap
  refine ContinuousAt.inv₀ ?_ (by positivity)
  have hs : ContinuousAt (fun p => Real.sqrt (p * (1 - p) + ε)) p := by fun_prop
  exact continuousAt_const.add (continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
    ((continuousAt_const.div hs (Real.sqrt_pos.mpr hu).ne').neg.div_const β)))

/-- **Existence of a fixed point (Mroueh, Proposition 1).** With `0 < p_ref ≤ 1` and `ε > 0`,
the map `h` has a fixed point in `[0, 1]`. -/
theorem exists_grpoMap_fixedPoint {pref β ε : ℝ} (h0 : 0 < pref) (h1 : pref ≤ 1) (hε : 0 < ε) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1, grpoMap pref β ε p = p := by
  have hcont : ContinuousOn (fun p => grpoMap pref β ε p - p) (Set.Icc 0 1) :=
    (continuousOn_grpoMap h0 h1 hε).sub continuousOn_id
  have hle1 : grpoMap pref β ε 1 ≤ 1 := by
    have : 0 ≤ (1 - pref) / pref := div_nonneg (sub_nonneg.mpr h1) h0.le
    rw [grpoMap]
    have he := Real.exp_pos (-(1 / Real.sqrt (1 * (1 - 1) + ε)) / β)
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun p => grpoMap pref β ε p - p) 1)
      ((fun p => grpoMap pref β ε p - p) 0) :=
    ⟨show grpoMap pref β ε 1 - 1 ≤ 0 by linarith,
      show 0 ≤ grpoMap pref β ε 0 - 0 by linarith [grpoMap_pos (β := β) (ε := ε) h0 h1 0]⟩
  obtain ⟨p, hp, hfix⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  exact ⟨p, hp, sub_eq_zero.mp hfix⟩

/-- Every fixed point of `h` in `[0, 1]` exceeds `p_ref`. -/
theorem lt_of_grpoMap_eq {pref β ε p : ℝ} (h0 : 0 < pref) (h1 : pref < 1) (hβ : 0 < β)
    (hε : 0 < ε) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hfix : grpoMap pref β ε p = p) : pref < p := by
  have := lt_grpoMap h0 h1 hβ (ε := ε) (p := p) (by nlinarith [hp.1, hp.2])
  rwa [hfix] at this

/-- The sigmoid is `1 / 4`-Lipschitz. -/
theorem abs_sigmoid_sub_le (u v : ℝ) :
    |Real.sigmoid u - Real.sigmoid v| ≤ |u - v| / 4 := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.sigmoid) (C := 1 / 4)
    (s := Set.univ) (fun x _ => differentiable_sigmoid x) (fun x _ => by
      rw [Real.deriv_sigmoid, Real.norm_eq_abs, abs_le]
      have := Real.sigmoid_pos x
      have := Real.sigmoid_lt_one x
      constructor <;> nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)])
    convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simp only [Real.norm_eq_abs] at h
  linarith

/-- `h` is a sigmoid: `h p = σ (log (p_ref / (1 - p_ref)) + Ω p / β)`. -/
theorem grpoMap_eq_sigmoid {pref β ε : ℝ} (h0 : 0 < pref) (h1 : pref < 1) (p : ℝ) :
    grpoMap pref β ε p = Real.sigmoid
      (Real.log (pref / (1 - pref)) + 1 / Real.sqrt (p * (1 - p) + ε) / β) := by
  rw [grpoMap, Real.sigmoid_def, neg_add, Real.exp_add, Real.exp_neg,
    Real.exp_log (div_pos h0 (sub_pos.mpr h1)), inv_div, neg_div]

/-- `Ω p = 1 / √(p (1 - p) + ε)` is `1 / (2 ε √ε)`-Lipschitz on `[0, 1]`. -/
theorem abs_inv_sqrt_sub_le {ε x y : ℝ} (hε : 0 < ε) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |1 / Real.sqrt (x * (1 - x) + ε) - 1 / Real.sqrt (y * (1 - y) + ε)| ≤
      |x - y| / (2 * ε * Real.sqrt ε) := by
  set U := x * (1 - x) + ε
  set V := y * (1 - y) + ε
  have hU : ε ≤ U := by nlinarith [hx.1, hx.2]
  have hV : ε ≤ V := by nlinarith [hy.1, hy.2]
  have hse := Real.sqrt_pos.mpr hε
  have hsU : Real.sqrt ε ≤ Real.sqrt U := Real.sqrt_le_sqrt hU
  have hsV : Real.sqrt ε ≤ Real.sqrt V := Real.sqrt_le_sqrt hV
  have hU2 := Real.sq_sqrt (hε.le.trans hU)
  have hV2 := Real.sq_sqrt (hε.le.trans hV)
  have he2 := Real.sq_sqrt hε.le
  have hUV : |U - V| ≤ |x - y| := by
    have : U - V = (x - y) * (1 - x - y) := by simp only [U, V]; ring
    rw [this, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith [hx.2, hy.2],
      by linarith [hx.1, hy.1]⟩)
  have ha : 0 < Real.sqrt U := hse.trans_le hsU
  have hb : 0 < Real.sqrt V := hse.trans_le hsV
  have hkey : 1 / Real.sqrt U - 1 / Real.sqrt V =
      (V - U) / (Real.sqrt U * Real.sqrt V * (Real.sqrt U + Real.sqrt V)) := by
    have hdiff : V - U = (Real.sqrt V - Real.sqrt U) * (Real.sqrt V + Real.sqrt U) := by
      linear_combination hU2 - hV2
    rw [hdiff]
    field_simp
    ring
  have hden : 2 * ε * Real.sqrt ε ≤ Real.sqrt U * Real.sqrt V * (Real.sqrt U + Real.sqrt V) := by
    have h1 : ε ≤ Real.sqrt U * Real.sqrt V := by
      nlinarith [mul_le_mul hsU hsV hse.le (hse.le.trans hsU)]
    nlinarith [mul_le_mul h1 (add_le_add hsU hsV) (by positivity) (by positivity)]
  have hD : 0 < Real.sqrt U * Real.sqrt V * (Real.sqrt U + Real.sqrt V) := by positivity
  rw [hkey, abs_div, abs_of_pos hD, abs_sub_comm]
  exact div_le_div₀ (abs_nonneg _) hUV (by positivity) hden

/-- **`h` is Lipschitz on `[0, 1]`** with constant `1 / (8 β ε √ε)`. -/
theorem abs_grpoMap_sub_le {pref β ε x y : ℝ} (h0 : 0 < pref) (h1 : pref < 1) (hβ : 0 < β)
    (hε : 0 < ε) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |grpoMap pref β ε x - grpoMap pref β ε y| ≤ |x - y| / (8 * β * ε * Real.sqrt ε) := by
  rw [grpoMap_eq_sigmoid h0 h1, grpoMap_eq_sigmoid h0 h1]
  refine (abs_sigmoid_sub_le _ _).trans ?_
  have h := abs_inv_sqrt_sub_le hε hx hy
  have hse := Real.sqrt_pos.mpr hε
  rw [add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_pos hβ, div_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith [abs_nonneg (x - y)]

/-- **Global convergence of the success probabilities.** With `0 < p_ref < 1`, `β > 0`, `ε > 0`,
`π_ref` of full support, and `8 β ε √ε > 1`, the map `h` has exactly one fixed point `p*` in
`[0, 1]`, `p* > p_ref`, and the success probabilities of the GRPO iterates satisfy
`|p_n - p*| ≤ k ^ n * |p_ref - p*|` with `k = 1 / (8 β ε √ε) < 1`, so they converge to `p*`.
The paper proves only local convergence; this global condition is a sufficient condition added
here. -/
theorem tendsto_successProb_grpoPolicy (πref : PMF O) {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (h0 : 0 < successProb r πref) (h1 : successProb r πref < 1)
    (hk : 1 < 8 * β * ε * Real.sqrt ε) :
    ∃ pstar ∈ Set.Icc (0 : ℝ) 1, grpoMap (successProb r πref) β ε pstar = pstar ∧
      (∀ q ∈ Set.Icc (0 : ℝ) 1, grpoMap (successProb r πref) β ε q = q → q = pstar) ∧
      successProb r πref < pstar ∧
      (∀ n, |successProb r (grpoPolicy r πref β ε n) - pstar| ≤
        (1 / (8 * β * ε * Real.sqrt ε)) ^ n * |successProb r πref - pstar|) ∧
      Filter.Tendsto (fun n => successProb r (grpoPolicy r πref β ε n)) Filter.atTop
        (nhds pstar) := by
  set pref := successProb r πref
  set k := 1 / (8 * β * ε * Real.sqrt ε)
  have hk0 : 0 ≤ k := by positivity
  have hk1 : k < 1 := by rw [div_lt_one (by positivity)]; exact hk
  have hlip (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      |grpoMap pref β ε x - grpoMap pref β ε y| ≤ k * |x - y| := by
    calc _ ≤ |x - y| / (8 * β * ε * Real.sqrt ε) := abs_grpoMap_sub_le h0 h1 hβ hε hx hy
      _ = k * |x - y| := by simp only [k]; ring
  obtain ⟨pstar, hps, hfix⟩ := exists_grpoMap_fixedPoint (β := β) h0 h1.le hε
  have hbound (n : ℕ) : |successProb r (grpoPolicy r πref β ε n) - pstar| ≤
      k ^ n * |pref - pstar| := by
    induction n with
    | zero => simp [grpoPolicy, pref]
    | succ n ih =>
      rw [successProb_grpoPolicy_succ r πref hβ ε h0]
      calc |grpoMap pref β ε (successProb r (grpoPolicy r πref β ε n)) - pstar|
          = |grpoMap pref β ε (successProb r (grpoPolicy r πref β ε n)) -
              grpoMap pref β ε pstar| := by rw [hfix]
        _ ≤ k * |successProb r (grpoPolicy r πref β ε n) - pstar| :=
            hlip _ _ (successProb_mem_Icc r _) hps
        _ ≤ k * (k ^ n * |pref - pstar|) := mul_le_mul_of_nonneg_left ih hk0
        _ = k ^ (n + 1) * |pref - pstar| := by ring
  refine ⟨pstar, hps, hfix, fun q hq hqfix => ?_, lt_of_grpoMap_eq h0 h1 hβ hε hps hfix,
    hbound, ?_⟩
  · have h := hlip q pstar hq hps
    rw [hqfix, hfix] at h
    have : |q - pstar| = 0 := by
      nlinarith [abs_nonneg (q - pstar)]
    exact sub_eq_zero.mp (abs_eq_zero.mp this)
  · have hlim : Filter.Tendsto (fun n => k ^ n * |pref - pstar|) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |pref - pstar|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]; exact hbound n) hlim

end Dynamics

end Rlib
