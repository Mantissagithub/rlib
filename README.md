# rlib

Reinforcement learning theory in Lean, built on [mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to give new RL proofs a shared starting point: definitions of environments and policies, probability tools, and results that Lean has already checked.

Definitions and headline theorems follow standard references as closely as the formal setting allows: the textbook by Agarwal, Jiang, Kakade, and Sun, [*Reinforcement Learning: Theory and Algorithms*](https://rltheorybook.github.io/), for the generative-model results, and the papers of Agarwal, Kakade, Lee, and Mahajan (JMLR 2021) and Mei, Xiao, Szepesvári, and Schuurmans (ICML 2020) for policy gradient. Each such theorem names the result it formalizes, for example Lemma 1.11 or Theorem 10, keeps the source's conventions (rewards in `[0, 1]`, step sizes, constants), and documents any place where the formal statement differs.

## What is proved

The Bellman and return results cover finite state and action sets:

- A fixed policy has exactly one solution to its Bellman equation.
- Value iteration converges to the Bellman optimality solution from any starting estimate.
- Choosing a greedy policy cannot lower the policy's Bellman value.
- Policy iteration eventually stops changing, using a fixed rule for choosing between tied actions.
- Expected rewards over a finite sampled trajectory equal repeated fixed-policy Bellman updates from zero and converge to the policy value.
- The infinite trajectory probability law has exactly the finite trajectory laws as its prefix distributions.
- Infinite discounted returns are absolutely summable. Finite prefix returns converge to them, and both obey the geometric reward bound.
- Infinite discounted returns are integrable under the trajectory law, and their expectations equal the policy's Bellman value.
- Empirical MDPs store observed reward means and successor frequencies. Their one-step action values equal sample means of the observed one-step targets.
- Empirical reward means and individual transition probabilities satisfy two-sided Hoeffding bounds under explicit independent-sampling assumptions.
- A tabular Q-learning update changes one state and action. The Bellman Q operator averages the target over a successor sampled with the stored mean reward and has a unique fixed point for `0 ≤ γ < 1`.
- With exact Bellman Q targets, a discount in `[0, 1)`, and a constant step size in `(0, 1]`, the error decreases geometrically after completed sweeps that each visit every state-action pair.
- A sampled Q-learning update differs from the exact Bellman update only at the visited entry, by the step size times the target gap. With a successor drawn from the model and the stored mean reward, the visited entry matches the exact update in expectation.
- Complete sweeps whose targets miss the exact Bellman target by at most `ε` approach the Bellman Q fixed point geometrically, up to an error floor of `ε / (1 - γ)`.
- A nonnegative sequence that moves a fraction `a n ∈ [0, 1]` of the way toward targets tending to zero converges to zero when the fractions are not summable. This is the deterministic step behind decaying step sizes. A sequence that averages inputs with such fractions tends to zero when the partial sums of the weighted inputs converge, even conditionally.
- Bounded noise with zero conditional mean given the past, weighted by square-summable coefficients, has almost surely convergent partial sums.
- Synchronous Q-learning, which updates every state-action pair at each step, converges to the Bellman Q fixed point when its step sizes lie in `[0, 1]` and are not summable, `0 ≤ γ < 1`, and its realized target errors tend to zero.
- The same iterations converge when target errors do not vanish but their step-weighted partial sums converge for every entry.
- With observed rewards bounded by `R`, synchronous Q-learning tables stay within `max ‖q₀‖ (R / (1 - γ))`.
- Sampled synchronous Q-learning converges almost surely to the Bellman Q fixed point when rewards are bounded, step sizes in `[0, 1]` are not summable but have summable squares, `0 ≤ γ < 1`, and each realized target error is known at the next time with zero conditional mean given the current time.
- That condition holds when each step's observations are revealed by the next time, independent of the current information, with the model's mean reward and transition law. Under this sampling model, synchronous Q-learning converges almost surely.
- Bellman Q iterations with a separate step size for each entry converge when every entry's step sizes lie in `[0, 1]` and are not summable, the iterates stay bounded, and each entry's step-weighted target errors have convergent partial sums. This covers updates that touch only some entries at each step.
- Asynchronous Q-learning updates only the visited entry from one observation. Its tables stay within `max ‖q₀‖ (R / (1 - γ))`, and it converges when every entry's visit step sizes are not summable and its visit-weighted target errors have convergent partial sums.
- Asynchronous Q-learning converges almost surely when visits are chosen from current information, each visited entry is updated from a fresh independent sample with the model's mean reward and transition law, rewards are bounded, step sizes in `[0, 1]` have summable squares, and almost surely every pair's visit step sizes are not summable.
- The Bellman Q fixed points of two models differ by at most the gap between their Bellman Q operators at one fixed point, divided by `1 - γ`.
- Hoeffding's bound holds for independent observations bounded by `c` with a common mean. At a fixed table, the empirical Bellman Q operator built from independent samples concentrates around the model's, both entrywise and uniformly in sup norm.
- **Sample complexity of model-based Q-value estimation.** With `n + 1` independent samples per state-action pair, rewards bounded by `R > 0`, and `n + 1 ≥ 2 * R ^ 2 * log (2 * |S| * |A| / δ) / (ε ^ 2 * (1 - γ) ^ 2)`, the Bellman Q fixed point of the empirical MDP is within `ε / (1 - γ)` of the model's except with probability at most `δ`.
- **Greedy policies (Agarwal, Jiang, Kakade, and Sun, Lemma 1.11).** If a table is within `ε` of the optimal Q table, its greedy policy is within `2 ε / (1 - γ)` of the optimal value at every state. So with the same number of samples, the greedy policy of the empirical Q fixed point is within `2 ε / (1 - γ) ^ 2` of optimal except with probability at most `δ`.
- **Bernstein's inequality.** For independent observations within `M` of a common mean with variance at most `σ²`, the mean of `N` observations deviates by at least `ε` with probability at most `2 exp (-N ε ^ 2 / (2 σ ^ 2 + 2 M ε / 3))`; equivalently, with probability at least `1 - δ` the deviation is below `√(2 σ ^ 2 log (2 / δ) / N) + 2 M log (2 / δ) / (3 N)`.
- **Total variance (Agarwal, Jiang, Kakade, and Sun, Lemma 2.12).** With rewards in `[0, 1]`, discounting the variance of `V^π` under the transition law along the trajectories of `π` gives at most `1 / (1 - γ) ^ 2`, and discounting its square root gives at most `√(1 / (1 - γ) ^ 3) ≤ √(2 / (1 - γ) ^ 3)`.
- A stationary policy's action values average to its state value under its own action choice, its advantages average to zero, and its action values satisfy their own Bellman equation.
- **Performance difference lemma.** The value of a new policy minus the value of an old one is the new policy's value when every reward is replaced by the old policy's advantage. A policy with nonnegative expected advantage under another at every state is at least as good everywhere.
- A policy has no action with positive advantage exactly when its value satisfies the Bellman optimality equation, and such a policy is at least as good as every stationary policy.
- Discounted state visitation is a probability distribution on states. `1 - γ` times a policy's value is the visitation average of its expected reward, and `1 - γ` times the gain of a new policy is the new policy's visitation average of its expected advantage under the old one.
- **PPO clipped surrogate.** The clipped term never exceeds the importance-weighted advantage, equals it inside the clip range, and stops growing once the ratio leaves the range in the direction the advantage favors. The clipped surrogate never exceeds the surrogate, and the surrogate is the old policy's visitation average of the new policy's expected advantage when the old policy covers the new one's support.
- **GRPO.** Group-relative advantages sum to zero, have mean square one when rewards differ, and are unchanged by shifting rewards or scaling them by a positive factor. The KL estimator `x - log x - 1` is nonnegative, vanishes only at `x = 1`, and has the KL divergence as its expectation when both distributions share their support, which gives Gibbs' inequality. The GRPO objective never exceeds the importance-weighted group-relative advantage and is zero at the first step.
- **Policy gradient theorem.** Policy values depend continuously on action probabilities. If the action probabilities of a family of policies are differentiable in a real parameter, the policy value is differentiable, with derivative `(1 - γ)⁻¹` times the discounted visitation average of the derivative of the action probabilities weighted by the advantages, or equivalently by the action values.
- **Softmax policy gradient.** Moving softmax scores in a direction `u` changes each action probability at rate `π a * (u a - ∑ b, π b * u b)` and the policy value at rate `(1 - γ)⁻¹ * ∑ s, d s * ∑ a, π a * u s a * A s a`. The partial derivative with respect to the score of `a` at `s` is `(1 - γ)⁻¹ * d s * π a * A s a`.
- **Trust-region policy improvement bound.** Switching policies moves the discounted visitation by at most `γ / (1 - γ)` times the new visitation average of the `ℓ¹` distance between the action distributions. So `1 - γ` times the gain of the new policy is at least the surrogate objective minus `γ / (1 - γ) * ε * δ`, where `ε` bounds the expected advantage and `δ` bounds the `ℓ¹` distance between the policies at every state.
- **Generalized advantage estimation.** With step weight `c = γ * λ`, the estimate is the first temporal-difference error when `λ = 0` and telescopes to the discounted return plus the discounted final value minus the start value when `λ = 1`. With the exact policy value, the expected temporal-difference error of an action is its advantage, and the expected estimate after taking an action and following the policy is that action's advantage for every `λ` and horizon.
- **Natural policy gradient (Agarwal et al. 2021, Theorem 16).** The update `θ ← θ + η / (1 - γ) * A` never lowers the value at any state. With rewards in `[0, 1]`, `θ⁽⁰⁾ = 0`, and `η > 0`, after `T` steps the gap to any policy under any start distribution `ρ` is at most `log |A| / (η T) + 1 / ((1 - γ) ^ 2 T)`.
- **Smoothness of softmax values (Mei et al. 2020, Lemma 7).** With rewards in `[0, 1]`, values lie in `[0, 1 / (1 - γ)]`, advantages are at most `1 / (1 - γ)` in absolute value, and policies within `δ` in `ℓ¹` have values within `δ / (1 - γ) ^ 2`. The weighted value satisfies `V θ' ≥ V θ + ⟪∇ V θ, θ' - θ⟫ - 4 / (1 - γ) ^ 3 * ‖θ' - θ‖ ^ 2`, the quadratic bound of an `8 / (1 - γ) ^ 3`-smooth function.
- **Gradient domination (Mei et al. 2020, Lemma 8).** If a deterministic policy `b` keeps probability at least `c` under `π` and its visitation is at most `C` times that of `π`, its value gain over `π` is at most `C / c` times the sum of the gradient entries at `b`, so its square is at most `(C / c) ^ 2 * |S|` times the squared gradient length.
- **Exact softmax policy gradient (Mei et al. 2020, Theorem 4).** With rewards in `[0, 1]`, a start distribution `μ > 0`, and step `η = (1 - γ) ^ 3 / 8`, each step raises `V (μ)` by at least `(1 - γ) ^ 3 / 16 * ‖∇‖ ^ 2`. If every iterate gives an optimal deterministic policy probability at least `c`, then `V* ρ - V θ_t ρ ≤ 16 |S| / (c ^ 2 (1 - γ) ^ 6 t) * ‖d*_μ / μ‖∞ ^ 2 * ‖1 / μ‖∞`. Lemma 9 below shows that such a `c > 0` exists when the optimal action is unique.
- **Asymptotics of exact softmax policy gradient (toward Agarwal et al. 2021, Theorem 10).** For any step size `η ≥ 0`, each step raises the value at every state, so values, action values, and advantages converge. With a step `0 < η ≤ (1 - γ) ^ 3 / 8`, the squared gradient lengths are summable, every gradient entry tends to zero, and `π_t (a | s) * A_t (s, a) → 0` wherever `μ s > 0`. If the advantage of an action at such a state stays below `-ε < 0`, its score tends to `-∞` (Lemma C.11).
- **Global convergence of softmax policy gradient (Agarwal et al. 2021, Theorem 10).** With rewards in `[0, 1]`, `μ s > 0` for every state, and a step `0 < η ≤ (1 - γ) ^ 3 / 8`, no action keeps a positive advantage in the limit, so the limit of the values satisfies the Bellman optimality equation and is at least the value of every stationary policy: the values converge to the optimal values.
- **Lemma 9 and the unconditional rate (Mei et al. 2020).** If the optimal deterministic policy's action is the unique optimal action at every state, its probability tends to one along exact softmax policy gradient, so there is `c > 0` below which it never falls. With that `c`, Theorem 4 holds with no assumption on the iterates: `V* ρ - V θ_t ρ ≤ 16 |S| / (c ^ 2 (1 - γ) ^ 6 t) * ‖d*_μ / μ‖∞ ^ 2 * ‖1 / μ‖∞`.

Empirical estimates use at least one paired reward and successor observation per state and action. Rewards may be any real numbers, and duplicate successors retain their frequencies. The empirical expectation and one-step identities require a finite state type, but no finite action type or discount bounds. These estimation identities are deterministic.

The concentration bounds apply at a fixed state and action, and at a fixed successor for transition probabilities. With `N ≥ 1` observations and `ε ≥ 0`, the probability of absolute error at least `ε` is at most `2 * exp(-2 * N * ε²)`. Reward observations must be independent, measurable, in `[0,1]` almost surely, and have the model reward as their common expectation. Successor observations must be independent, measurable, and have the model transition law, and the state type must have measurable singletons. These bounds require no finite state or action type and no discount assumptions. Rewards and successors within each observed pair may depend on each other. The results do not give simultaneous bounds across rows or justify independence for a dependent policy trajectory.

The uniqueness, convergence, policy-improvement, summability, and return-bound results assume a discount factor `0 ≤ γ < 1`. The finite-horizon return identities allow any real discount. The trajectory law and its prefix distributions do not depend on a discount. Maximizing over actions requires at least one action.

## The model and its scope

An environment specifies transition probabilities and an expected immediate reward for each state and action. Every action is available in every state. Policies can choose actions randomly, based on the current state. Policy iteration uses deterministic policies.

Trajectories record the action and next state at each step. Their returns sum the model's stored expected rewards, rather than sampled reward noise.

Policy values are defined by Bellman equations and equal both the limits of expected finite returns and the expected infinite returns under the trajectory law. The infinite expectation result assumes finite state and action types with measurable singletons and `0 ≤ γ < 1`. The definitions use exact real numbers.

See [ROADMAP.md](ROADMAP.md) for completed and planned work.

## Find the code

| File | What it contains |
| --- | --- |
| [Analysis/DecayingRecursion](Rlib/Analysis/DecayingRecursion.lean) | Recursions with non-summable step sizes toward vanishing targets |
| [Probability/Expectation](Rlib/Probability/Expectation.lean) | Finite expectation, linearity, bounds, and sequential sampling |
| [Probability/Empirical](Rlib/Probability/Empirical.lean) | Nonempty sample means, empirical distributions, frequencies, and expectation identities |
| [Probability/Concentration](Rlib/Probability/Concentration.lean) | Two-sided Hoeffding bound for independent bounded observations with a common mean |
| [Probability/Bernstein](Rlib/Probability/Bernstein.lean) | Bernstein's inequality for independent bounded observations |
| [Probability/MartingaleSeries](Rlib/Probability/MartingaleSeries.lean) | Almost sure convergence of weighted bounded martingale differences |
| [MDP/Basic](Rlib/MDP/Basic.lean) | Environments, policies, and one-step values |
| [MDP/Empirical](Rlib/MDP/Empirical.lean) | MDP estimates from paired observations and exact one-step sample identities |
| [MDP/Concentration](Rlib/MDP/Concentration.lean) | Pointwise empirical reward and transition probability bounds |
| [MDP/QConcentration](Rlib/MDP/QConcentration.lean) | Concentration of the empirical Bellman Q operator |
| [MDP/QSampleComplexity](Rlib/MDP/QSampleComplexity.lean) | Sample complexity of model-based Q-value estimation |
| [MDP/QGreedy](Rlib/MDP/QGreedy.lean) | Greedy policies of Q tables, Q-error amplification, and near-optimal policies from samples |
| [MDP/TotalVariance](Rlib/MDP/TotalVariance.lean) | Variances of values under the transition law and the total variance bounds |
| [MDP/OneStep](Rlib/MDP/OneStep.lean) | Ordering and error bounds for one-step updates |
| [MDP/PolicyEvaluation](Rlib/MDP/PolicyEvaluation.lean) | A policy's unique Bellman value |
| [MDP/Advantage](Rlib/MDP/Advantage.lean) | Action values and advantages of a stationary policy |
| [MDP/GAE](Rlib/MDP/GAE.lean) | Temporal-difference errors and generalized advantage estimation |
| [MDP/NaturalPolicyGradient](Rlib/MDP/NaturalPolicyGradient.lean) | Natural policy gradient for softmax policies and its `1 / T` convergence rate |
| [MDP/SoftmaxSmoothness](Rlib/MDP/SoftmaxSmoothness.lean) | Lipschitz bounds in the policy and the ascent lemma for softmax policy values |
| [MDP/GradientDomination](Rlib/MDP/GradientDomination.lean) | The softmax policy gradient and the gradient-domination inequality |
| [MDP/SoftmaxPolicyGradient](Rlib/MDP/SoftmaxPolicyGradient.lean) | Exact softmax policy gradient and its `1 / T` rate |
| [MDP/SoftmaxPGAsymptotic](Rlib/MDP/SoftmaxPGAsymptotic.lean) | Monotone improvement, value convergence, and vanishing gradients of exact softmax policy gradient |
| [MDP/SoftmaxPGConvergence](Rlib/MDP/SoftmaxPGConvergence.lean) | Global convergence of exact softmax policy gradient to optimal values |
| [MDP/PerformanceDifference](Rlib/MDP/PerformanceDifference.lean) | The performance difference lemma and improvement from advantages |
| [MDP/Visitation](Rlib/MDP/Visitation.lean) | Discounted state visitation and the visitation form of the performance difference lemma |
| [MDP/ClippedSurrogate](Rlib/MDP/ClippedSurrogate.lean) | The PPO clipped surrogate objective and its pessimism |
| [MDP/GRPO](Rlib/MDP/GRPO.lean) | Group-relative advantages, the KL estimator, and the GRPO objective |
| [MDP/PolicyGradient](Rlib/MDP/PolicyGradient.lean) | Continuity of policy values and the policy gradient theorem |
| [MDP/Softmax](Rlib/MDP/Softmax.lean) | Softmax policies and their gradient |
| [MDP/TrustRegion](Rlib/MDP/TrustRegion.lean) | Visitation stability and the trust-region policy improvement bound |
| [MDP/Optimality](Rlib/MDP/Optimality.lean) | The Bellman operator that takes the best action |
| [MDP/QLearning](Rlib/MDP/QLearning.lean) | Sampled Q updates, expected and empirical targets, and Bellman Q contraction |
| [MDP/QSimulation](Rlib/MDP/QSimulation.lean) | Comparing Bellman Q fixed points of two models |
| [MDP/QBellmanSweep](Rlib/MDP/QBellmanSweep.lean) | Ordered Bellman Q updates and convergence of complete sweeps |
| [MDP/QSampling](Rlib/MDP/QSampling.lean) | Error and expectation of a sampled update against the exact Bellman update |
| [MDP/QPerturbedSweep](Rlib/MDP/QPerturbedSweep.lean) | Sweeps with bounded target errors and their geometric error floor |
| [MDP/QSynchronous](Rlib/MDP/QSynchronous.lean) | Synchronous Q-learning with decaying step sizes and vanishing target errors |
| [MDP/QLearningConvergence](Rlib/MDP/QLearningConvergence.lean) | Almost sure convergence of sampled synchronous Q-learning |
| [MDP/QLearningSampling](Rlib/MDP/QLearningSampling.lean) | Unbiased targets and almost sure convergence of synchronous and asynchronous Q-learning from fresh samples |
| [MDP/QAsynchronous](Rlib/MDP/QAsynchronous.lean) | Bellman Q iterations with per-entry step sizes |
| [MDP/QLearningAsync](Rlib/MDP/QLearningAsync.lean) | Asynchronous Q-learning, bounded tables, and convergence with averaged errors |
| [MDP/ValueIteration](Rlib/MDP/ValueIteration.lean) | Repeated value updates, convergence, and error bounds |
| [MDP/PolicyImprovement](Rlib/MDP/PolicyImprovement.lean) | Greedy policy existence and improvement |
| [MDP/PolicyIteration](Rlib/MDP/PolicyIteration.lean) | Policy updates, stabilization, and terminal Bellman optimality |
| [MDP/FiniteHorizon](Rlib/MDP/FiniteHorizon.lean) | Sampled trajectories and expected finite returns |
| [MDP/TrajectoryMeasure](Rlib/MDP/TrajectoryMeasure.lean) | Infinite trajectory probability law and exact finite-prefix distributions |
| [MDP/InfiniteHorizon](Rlib/MDP/InfiniteHorizon.lean) | Infinite returns, geometric bounds, and limits of finite returns |
| [MDP/InfiniteExpectation](Rlib/MDP/InfiniteExpectation.lean) | Integrability and expected infinite returns equal to policy values |

Import the library with:

```lean
import Rlib
```

## Build and check

Install [elan](https://github.com/leanprover/elan), then run these commands in the repository. Lean and mathlib are pinned to version `4.35.0`.

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get \
  Mathlib.Probability.ProbabilityMassFunction.Constructions \
  Mathlib.Probability.ProbabilityMassFunction.Integrals \
  Mathlib.Data.Fin.Tuple.Basic \
  Mathlib.Probability.Kernel.IonescuTulcea.Traj \
  Mathlib.Analysis.SpecificLimits.Normed \
  Mathlib.MeasureTheory.Integral.DominatedConvergence \
  Mathlib.Analysis.Normed.Group.Constructions \
  Mathlib.Analysis.Normed.Field.Basic \
  Mathlib.Topology.MetricSpace.Contracting \
  Mathlib.Data.Finset.Lattice.Fold \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Topology.Order.OrderClosed \
  Mathlib.Data.Fintype.Pigeonhole \
  Mathlib.Probability.Moments.SubGaussian
lake build
python3 scripts/check_axioms.py
lake env lean -DwarningAsError=true RlibTest/Optimality.lean
lake env lean -DwarningAsError=true RlibTest/ValueIteration.lean
lake env lean -DwarningAsError=true RlibTest/PolicyImprovement.lean
lake env lean -DwarningAsError=true RlibTest/PolicyIteration.lean
lake env lean -DwarningAsError=true RlibTest/FiniteHorizon.lean
lake env lean -DwarningAsError=true RlibTest/InfiniteHorizon.lean
lake env lean -DwarningAsError=true RlibTest/TrajectoryMeasure.lean
lake env lean -DwarningAsError=true RlibTest/InfiniteExpectation.lean
lake env lean -DwarningAsError=true RlibTest/Empirical.lean
lake env lean -DwarningAsError=true RlibTest/Concentration.lean
lake env lean -DwarningAsError=true RlibTest/QLearning.lean
lake env lean -DwarningAsError=true RlibTest/QBellmanSweep.lean
lake env lean -DwarningAsError=true RlibTest/QSampling.lean
lake env lean -DwarningAsError=true RlibTest/QPerturbedSweep.lean
lake env lean -DwarningAsError=true RlibTest/DecayingRecursion.lean
lake env lean -DwarningAsError=true RlibTest/QSynchronous.lean
lake env lean -DwarningAsError=true RlibTest/MartingaleSeries.lean
lake env lean -DwarningAsError=true RlibTest/QNoiseAveraging.lean
lake env lean -DwarningAsError=true RlibTest/QLearningConvergence.lean
lake env lean -DwarningAsError=true RlibTest/QLearningSampling.lean
lake env lean -DwarningAsError=true RlibTest/QAsynchronous.lean
lake env lean -DwarningAsError=true RlibTest/QLearningAsync.lean
lake env lean -DwarningAsError=true RlibTest/QLearningAsyncSampling.lean
lake env lean -DwarningAsError=true RlibTest/QSimulation.lean
lake env lean -DwarningAsError=true RlibTest/QConcentration.lean
lake env lean -DwarningAsError=true RlibTest/QSampleComplexity.lean
lake env lean -DwarningAsError=true RlibTest/Advantage.lean
lake env lean -DwarningAsError=true RlibTest/PerformanceDifference.lean
lake env lean -DwarningAsError=true RlibTest/Visitation.lean
lake env lean -DwarningAsError=true RlibTest/ClippedSurrogate.lean
lake env lean -DwarningAsError=true RlibTest/GRPO.lean
lake env lean -DwarningAsError=true RlibTest/PolicyGradient.lean
lake env lean -DwarningAsError=true RlibTest/Softmax.lean
lake env lean -DwarningAsError=true RlibTest/TrustRegion.lean
lake env lean -DwarningAsError=true RlibTest/GAE.lean
lake env lean -DwarningAsError=true RlibTest/NaturalPolicyGradient.lean
lake env lean -DwarningAsError=true RlibTest/SoftmaxSmoothness.lean
lake env lean -DwarningAsError=true RlibTest/GradientDomination.lean
lake env lean -DwarningAsError=true RlibTest/SoftmaxPolicyGradient.lean
lake env lean -DwarningAsError=true RlibTest/SoftmaxPGAsymptotic.lean
lake env lean -DwarningAsError=true RlibTest/SoftmaxPGConvergence.lean
lake env lean -DwarningAsError=true RlibTest/QGreedy.lean
lake env lean -DwarningAsError=true RlibTest/Bernstein.lean
lake env lean -DwarningAsError=true RlibTest/TotalVariance.lean
```

CI builds the library, audits the public theorems, and compiles the examples. These include stochastic transitions, negative rewards, tied actions, and concentration for four independent fair Bool observations on a product probability space.

The [axiom audit](scripts/check_axioms.py) rejects unfinished proofs and unexpected axioms. It allows only `propext`, `Classical.choice`, and `Quot.sound`.

## Related work

Several earlier projects formalize parts of this material.

- [CertRL](https://arxiv.org/abs/2009.11403) (Coq, CPP 2021) proves convergence of value iteration and policy iteration for finite MDPs.
- The Isabelle/HOL work of [Schäffeler and Abdulaziz](https://ojs.aaai.org/index.php/AAAI/article/view/26759) verifies value iteration, policy iteration, modified policy iteration, and later approximate policy iteration for factored MDPs. [Chevallier et al.](https://arxiv.org/abs/2112.05996) formalize the foundations of discrete reinforcement learning in Isabelle/HOL.
- [markovgames](https://github.com/gabrielhrs/markovgames) ports Bellman operators, value iteration, and policy iteration to Lean 4 and Mathlib, and extends them to concurrent stochastic games.
- [rl-theory-in-lean](https://reservoir.lean-lang.org/@ShangtongZhang/RL-Theory) by Shangtong Zhang ([paper](https://arxiv.org/abs/2511.03618)) proves almost sure convergence of Q-learning and linear TD with Markovian samples in Lean 4 and Mathlib, using the Robbins-Siegmund theorem.

The value iteration, policy iteration, and Q-learning convergence results here overlap with that work. This library's Q-learning results use fresh independent samples rather than a single Markovian trajectory, and they cover synchronous and asynchronous updates with visits chosen from current information.

We did not find earlier machine-checked versions of the performance difference lemma, discounted visitation, the policy gradient theorem and the softmax gradient, the PPO clipped surrogate, GRPO's group-relative advantages and KL estimator, the trust-region policy improvement bound, generalized advantage estimation, the convergence rates of natural and exact softmax policy gradient, the global convergence of exact softmax policy gradient, or the sample complexity of model-based Q-value estimation. This comes from a web search, not an exhaustive survey. Please open an issue if you know of related work we missed.
