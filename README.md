# rlib

Reinforcement learning theory in Lean, built on [mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to give new RL proofs a shared starting point: definitions of environments and policies, probability tools, and results that Lean has already checked.

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
| [Probability/MartingaleSeries](Rlib/Probability/MartingaleSeries.lean) | Almost sure convergence of weighted bounded martingale differences |
| [MDP/Basic](Rlib/MDP/Basic.lean) | Environments, policies, and one-step values |
| [MDP/Empirical](Rlib/MDP/Empirical.lean) | MDP estimates from paired observations and exact one-step sample identities |
| [MDP/Concentration](Rlib/MDP/Concentration.lean) | Pointwise empirical reward and transition probability bounds |
| [MDP/OneStep](Rlib/MDP/OneStep.lean) | Ordering and error bounds for one-step updates |
| [MDP/PolicyEvaluation](Rlib/MDP/PolicyEvaluation.lean) | A policy's unique Bellman value |
| [MDP/Optimality](Rlib/MDP/Optimality.lean) | The Bellman operator that takes the best action |
| [MDP/QLearning](Rlib/MDP/QLearning.lean) | Sampled Q updates, expected and empirical targets, and Bellman Q contraction |
| [MDP/QBellmanSweep](Rlib/MDP/QBellmanSweep.lean) | Ordered Bellman Q updates and convergence of complete sweeps |
| [MDP/QSampling](Rlib/MDP/QSampling.lean) | Error and expectation of a sampled update against the exact Bellman update |
| [MDP/QPerturbedSweep](Rlib/MDP/QPerturbedSweep.lean) | Sweeps with bounded target errors and their geometric error floor |
| [MDP/QSynchronous](Rlib/MDP/QSynchronous.lean) | Synchronous Q-learning with decaying step sizes and vanishing target errors |
| [MDP/QLearningConvergence](Rlib/MDP/QLearningConvergence.lean) | Almost sure convergence of sampled synchronous Q-learning |
| [MDP/QLearningSampling](Rlib/MDP/QLearningSampling.lean) | Unbiased targets and almost sure convergence from independent fresh samples |
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
```

CI builds the library, audits the public theorems, and compiles the examples. These include stochastic transitions, negative rewards, tied actions, and concentration for four independent fair Bool observations on a product probability space.

The [axiom audit](scripts/check_axioms.py) rejects unfinished proofs and unexpected axioms. It allows only `propext`, `Classical.choice`, and `Quot.sound`.
