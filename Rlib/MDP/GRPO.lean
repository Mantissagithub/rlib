module

public import Rlib.MDP.ClippedSurrogate
public import Rlib.Probability.Empirical
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Group relative policy optimization

GRPO scores each of a group of sampled answers by its reward relative to the group, and
penalizes drift from a reference policy with the estimator `x - log x - 1` of the KL divergence.
-/

@[expose] public section

noncomputable section

namespace Rlib

variable {n : ℕ}

/-- The standard deviation of a group of rewards. -/
def groupStd (r : Fin (n + 1) → ℝ) : ℝ :=
  Real.sqrt (sampleMean fun i => (r i - sampleMean r) ^ 2)

/-- A reward's group-relative advantage: its gap from the group mean in units of the group's
standard deviation. -/
def groupAdvantage (r : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (r i - sampleMean r) / groupStd r

private theorem sum_sub_sampleMean (r : Fin (n + 1) → ℝ) : ∑ i, (r i - sampleMean r) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, sampleMean]
  push_cast
  field_simp
  ring

/-- Group-relative advantages sum to zero. -/
theorem sum_groupAdvantage (r : Fin (n + 1) → ℝ) : ∑ i, groupAdvantage r i = 0 := by
  simp only [groupAdvantage, ← Finset.sum_div, sum_sub_sampleMean, zero_div]

/-- When the rewards are not all equal, group-relative advantages have mean square one. -/
theorem sampleMean_groupAdvantage_sq (r : Fin (n + 1) → ℝ) (hσ : 0 < groupStd r) :
    sampleMean (fun i => groupAdvantage r i ^ 2) = 1 := by
  have hvar : 0 ≤ sampleMean fun i => (r i - sampleMean r) ^ 2 :=
    div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
  have hsq : groupStd r ^ 2 = sampleMean fun i => (r i - sampleMean r) ^ 2 :=
    Real.sq_sqrt hvar
  have h : (fun i => groupAdvantage r i ^ 2) =
      fun i => (groupStd r ^ 2)⁻¹ * (r i - sampleMean r) ^ 2 := by
    funext i
    simp only [groupAdvantage, div_pow]
    ring
  rw [h, sampleMean_mul, ← hsq, inv_mul_cancel₀ (pow_pos hσ 2).ne']

/-- Shifting all rewards by a constant and scaling them by a positive factor leaves the
group-relative advantages unchanged. -/
theorem groupAdvantage_affine (r : Fin (n + 1) → ℝ) {k : ℝ} (hk : 0 < k) (c : ℝ) :
    groupAdvantage (fun i => k * r i + c) = groupAdvantage r := by
  have hmean : sampleMean (fun i => k * r i + c) = k * sampleMean r + c := by
    simp only [sampleMean, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hdev (i : Fin (n + 1)) :
      k * r i + c - (k * sampleMean r + c) = k * (r i - sampleMean r) := by
    ring
  have hstd : groupStd (fun i => k * r i + c) = k * groupStd r := by
    show Real.sqrt (sampleMean fun i => (k * r i + c - sampleMean (fun i => k * r i + c)) ^ 2) =
      k * Real.sqrt (sampleMean fun i => (r i - sampleMean r) ^ 2)
    rw [hmean, show (fun i => (k * r i + c - (k * sampleMean r + c)) ^ 2) =
        fun i => k ^ 2 * (r i - sampleMean r) ^ 2 from funext fun i => by ring, sampleMean_mul,
      Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le]
  funext i
  show (k * r i + c - sampleMean (fun i => k * r i + c)) / groupStd (fun i => k * r i + c) =
    (r i - sampleMean r) / groupStd r
  rw [hstd, hmean, hdev i]
  by_cases h0 : groupStd r = 0
  · simp [h0]
  · field_simp

/-- The estimator `x - log x - 1` used for the KL penalty. -/
def klEstimator (x : ℝ) : ℝ := x - Real.log x - 1

/-- The KL estimator is nonnegative on positive ratios. -/
theorem klEstimator_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ klEstimator x := by
  have := Real.log_le_sub_one_of_pos hx
  unfold klEstimator
  linarith

/-- The KL estimator vanishes on a positive ratio exactly when the ratio is one. -/
theorem klEstimator_eq_zero_iff {x : ℝ} (hx : 0 < x) : klEstimator x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra hne
    have := Real.log_lt_sub_one_of_pos hx hne
    unfold klEstimator at h
    linarith
  · rintro rfl
    simp [klEstimator]

variable {X : Type*} [Fintype X]

/-- The KL divergence of `q` from `p` for finite distributions. -/
def kl (p q : PMF X) : ℝ :=
  ∑ x, (p x).toReal * Real.log ((p x).toReal / (q x).toReal)

/-- **Unbiasedness of the KL estimator.** When `p` and `q` give positive probability to the same
outcomes, the KL estimator applied to the ratio `q / p` has expectation `kl p q` under `p`. -/
theorem expect_klEstimator (p q : PMF X) (hsupp : ∀ x, p x = 0 ↔ q x = 0) :
    expect p (fun x => klEstimator ((q x).toReal / (p x).toReal)) = kl p q := by
  have hterm (x : X) : (p x).toReal * klEstimator ((q x).toReal / (p x).toReal) =
      (q x).toReal + (p x).toReal * Real.log ((p x).toReal / (q x).toReal) - (p x).toReal := by
    by_cases hp : p x = 0
    · simp [hp, (hsupp x).1 hp]
    · have hq : q x ≠ 0 := fun h => hp ((hsupp x).2 h)
      have hp' : 0 < (p x).toReal := ENNReal.toReal_pos hp (PMF.apply_ne_top p x)
      have hq' : 0 < (q x).toReal := ENNReal.toReal_pos hq (PMF.apply_ne_top q x)
      rw [klEstimator, Real.log_div hq'.ne' hp'.ne', Real.log_div hp'.ne' hq'.ne']
      field_simp
      ring
  unfold expect kl
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, probability_sum]
  ring

/-- **Gibbs' inequality.** When `p` and `q` give positive probability to the same outcomes, the
KL divergence is nonnegative. -/
theorem kl_nonneg (p q : PMF X) (hsupp : ∀ x, p x = 0 ↔ q x = 0) : 0 ≤ kl p q := by
  rw [← expect_klEstimator p q hsupp]
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases hp : p x = 0
  · simp [hp]
  · have hq : q x ≠ 0 := fun h => hp ((hsupp x).2 h)
    exact mul_nonneg ENNReal.toReal_nonneg (klEstimator_nonneg (div_pos
      (ENNReal.toReal_pos hq (PMF.apply_ne_top q x))
      (ENNReal.toReal_pos hp (PMF.apply_ne_top p x))))

/-- The GRPO objective for one group: the average of the clipped term with group-relative
advantages, minus `β` times the KL estimator at each answer. `ratio i` is the new-to-old
probability ratio and `refRatio i` the reference-to-new ratio of answer `i`. -/
def grpoObjective (ε β : ℝ) (ratio refRatio r : Fin (n + 1) → ℝ) : ℝ :=
  sampleMean fun i => ppoClip ε (ratio i) (groupAdvantage r i) - β * klEstimator (refRatio i)

/-- **Pessimism of GRPO.** With a nonnegative penalty weight and positive reference ratios, the
GRPO objective never exceeds the average importance-weighted group-relative advantage. -/
theorem grpoObjective_le (ε : ℝ) {β : ℝ} (hβ : 0 ≤ β) (ratio : Fin (n + 1) → ℝ)
    {refRatio : Fin (n + 1) → ℝ} (href : ∀ i, 0 < refRatio i) (r : Fin (n + 1) → ℝ) :
    grpoObjective ε β ratio refRatio r ≤ sampleMean fun i => ratio i * groupAdvantage r i := by
  unfold grpoObjective sampleMean
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun i _ => by
    have := mul_nonneg hβ (klEstimator_nonneg (href i))
    linarith [ppoClip_le ε (ratio i) (groupAdvantage r i)]

/-- At the first step, when the new, old, and reference policies coincide, the GRPO objective
is zero for any nonnegative clip range. -/
theorem grpoObjective_one {ε : ℝ} (hε : 0 ≤ ε) (β : ℝ) (r : Fin (n + 1) → ℝ) :
    grpoObjective ε β (fun _ => 1) (fun _ => 1) r = 0 := by
  unfold grpoObjective sampleMean
  have hk : klEstimator 1 = 0 := (klEstimator_eq_zero_iff one_pos).2 rfl
  simp only [ppoClip_eq_of_mem (by linarith : 1 - ε ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + ε), hk,
    one_mul, mul_zero, sub_zero, sum_groupAdvantage, zero_div]

end Rlib
