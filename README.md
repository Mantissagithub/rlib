# rlib

Reinforcement learning theory in Lean 4, built on [mathlib](https://github.com/leanprover-community/mathlib4). It gives new RL proofs a shared base: environments, policies, probability tools, and checked results.

Headline theorems follow their sources as closely as the formal setting allows. The main source is the textbook by Agarwal, Jiang, Kakade, and Sun, [*Reinforcement Learning: Theory and Algorithms*](https://rltheorybook.github.io/). Policy gradient results follow Agarwal, Kakade, Lee, and Mahajan (JMLR 2021) and Mei, Xiao, Szepesvári, and Schuurmans (ICML 2020). Each theorem names the result it formalizes, keeps the source's conventions (rewards in `[0, 1]`, step sizes, constants), and documents where the formal statement differs.

Import everything with `import Rlib`. [ROADMAP.md](ROADMAP.md) lists completed and planned work in detail.

## What is proved

States and actions are finite unless a file says otherwise. Discounted results assume `0 ≤ γ < 1`. Every action is available in every state.

### Bellman equations and planning

- A policy's Bellman equation has a unique solution ([PolicyEvaluation](Rlib/MDP/PolicyEvaluation.lean)).
- Value iteration converges to the optimal values ([ValueIteration](Rlib/MDP/ValueIteration.lean), [Optimality](Rlib/MDP/Optimality.lean)).
- Greedy improvement never lowers a value, and policy iteration stops at a Bellman-optimal policy ([PolicyImprovement](Rlib/MDP/PolicyImprovement.lean), [PolicyIteration](Rlib/MDP/PolicyIteration.lean)).
- Expected finite returns converge to the policy value, and the expected infinite return under the trajectory law equals it ([FiniteHorizon](Rlib/MDP/FiniteHorizon.lean), [TrajectoryMeasure](Rlib/MDP/TrajectoryMeasure.lean), [InfiniteHorizon](Rlib/MDP/InfiniteHorizon.lean), [InfiniteExpectation](Rlib/MDP/InfiniteExpectation.lean)).

### Generative model

- Hoeffding and Bernstein inequalities for independent bounded observations ([Concentration](Rlib/Probability/Concentration.lean), [Bernstein](Rlib/Probability/Bernstein.lean)).
- With `n + 1 ≥ 2 R² log (2 |S| |A| / δ) / (ε² (1 - γ)²)` samples per pair, the empirical Q fixed point is within `ε / (1 - γ)` of the true one with probability at least `1 - δ` ([QSampleComplexity](Rlib/MDP/QSampleComplexity.lean)).
- Lemma 1.11: a table within `ε` of `Q*` has a greedy policy within `2 ε / (1 - γ)` of optimal ([QGreedy](Rlib/MDP/QGreedy.lean)).
- Lemmas 2.5, 2.10, and 2.12 and Theorem 2.6: the minimax `1 / (1 - γ)³` bound on `‖Q* - Q̂*‖∞`, with the constant `c = 12` ([TotalVariance](Rlib/MDP/TotalVariance.lean), [MinimaxEstimation](Rlib/MDP/MinimaxEstimation.lean), [MinimaxSampleComplexity](Rlib/MDP/MinimaxSampleComplexity.lean)).

### Q-learning

- Exact and perturbed Bellman Q sweeps converge geometrically, up to an error floor of `ε / (1 - γ)` ([QBellmanSweep](Rlib/MDP/QBellmanSweep.lean), [QPerturbedSweep](Rlib/MDP/QPerturbedSweep.lean)).
- Synchronous Q-learning converges almost surely with fresh independent samples, step sizes that are not summable, and square-summable step sizes ([QSynchronous](Rlib/MDP/QSynchronous.lean), [QLearningConvergence](Rlib/MDP/QLearningConvergence.lean), [QLearningSampling](Rlib/MDP/QLearningSampling.lean)).
- Asynchronous Q-learning converges almost surely when visits depend only on current information and every pair's visit step sizes are not summable ([QAsynchronous](Rlib/MDP/QAsynchronous.lean), [QLearningAsync](Rlib/MDP/QLearningAsync.lean)).

### Regret in episodic MDPs (Chapter 7)

- Lemma 7.4 and Equation 0.4: optimism of UCB-VI and the truncated simulation inequality ([Basic](Rlib/Episodic/Basic.lean)).
- Lemma 7.5: `∑ 1 / √N ≤ 2 H √(|S| |A| K)` ([Counting](Rlib/Episodic/Counting.lean)).
- Theorem 7.1: with `L = log (2 H |S| |A| K / δ)`, the expected regret of UCB-VI is at most `20 H² |S| √(|A| K L) + 2 H² |S| |A| + 2 δ K H` ([UCBVIRegret](Rlib/Episodic/UCBVIRegret.lean)). The extra terms cover first visits, where the book's bonus is undefined, and the failure event.
- Theorem 7.6: with `L' = log (2 H |S|² |A| K / δ)`, the expected regret is at most `e (8 H² √L √(|S| |A| K) + 2 H² |S| |A| + 3 H³ |S|² |A| L' (1 + log K)) + 2 δ K H` ([UCBVIRefined](Rlib/Episodic/UCBVIRefined.lean)).

The learner reads successors from a table drawn in advance, which gives the same trajectory law as sampling on the fly ([UCBVI](Rlib/Episodic/UCBVI.lean), [UCBVILaw](Rlib/Episodic/UCBVILaw.lean)).

### Policy gradient

- The performance difference lemma, discounted visitation, and the policy gradient theorem ([PerformanceDifference](Rlib/MDP/PerformanceDifference.lean), [Visitation](Rlib/MDP/Visitation.lean), [PolicyGradient](Rlib/MDP/PolicyGradient.lean)).
- Natural policy gradient converges at rate `log |A| / (η T) + 1 / ((1 - γ)² T)` (Agarwal et al., Theorem 16; [NaturalPolicyGradient](Rlib/MDP/NaturalPolicyGradient.lean)).
- Exact softmax policy gradient with `η = (1 - γ)³ / 8` converges to the optimal values (Agarwal et al., Theorem 10) at rate `O(1 / t)` when the optimal action is unique (Mei et al., Lemmas 7–9 and Theorem 4; [SoftmaxSmoothness](Rlib/MDP/SoftmaxSmoothness.lean), [GradientDomination](Rlib/MDP/GradientDomination.lean), [SoftmaxPolicyGradient](Rlib/MDP/SoftmaxPolicyGradient.lean), [SoftmaxPGConvergence](Rlib/MDP/SoftmaxPGConvergence.lean)).
- Conservative policy iteration (Section 14.1): mixing in a greedy policy improves the value by at least `𝔸² (1 - γ) / (8 γ)` (Theorem 14.2), and CPI stops within `8 γ / (ε² (1 - γ)²)` steps at a locally optimal policy (Theorem 14.3) that is near-optimal when `μ` covers the optimal visitation (Theorem 14.4) ([ConservativePolicyIteration](Rlib/MDP/ConservativePolicyIteration.lean)).
- Exact PPO with a KL penalty (Liu et al. 2019) takes the natural policy gradient step, so it converges at the same `1 / T` rate ([KLPenaltyPPO](Rlib/MDP/KLPenaltyPPO.lean)).
- GRPO with 0/1 rewards (Mroueh, ICML 2026): each iteration has a closed-form solution, the success probability follows a fixed recursion, and it rises above the reference policy's. When `8 β ε √ε > 1` it converges geometrically to the unique fixed point ([GRPODynamics](Rlib/MDP/GRPODynamics.lean)).
- The trust-region improvement bound, the PPO clipped surrogate, GRPO's group-relative advantages and KL estimator, and generalized advantage estimation ([TrustRegion](Rlib/MDP/TrustRegion.lean), [ClippedSurrogate](Rlib/MDP/ClippedSurrogate.lean), [GRPO](Rlib/MDP/GRPO.lean), [GAE](Rlib/MDP/GAE.lean)).

## Build and check

Install [elan](https://github.com/leanprover/elan). Lean and mathlib are pinned to `4.35.0`. Run these commands in the repository:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get
lake build
python3 scripts/check_axioms.py
for f in RlibTest/*.lean; do lake env lean -DwarningAsError=true "$f"; done
```

The [axiom audit](scripts/check_axioms.py) rejects unfinished proofs. It allows only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Related work

- [CertRL](https://arxiv.org/abs/2009.11403) (Coq) proves convergence of value iteration and policy iteration.
- [Schäffeler and Abdulaziz](https://ojs.aaai.org/index.php/AAAI/article/view/26759) and [Chevallier et al.](https://arxiv.org/abs/2112.05996) formalize MDP algorithms and discrete RL in Isabelle/HOL.
- [markovgames](https://github.com/gabrielhrs/markovgames) ports Bellman operators to Lean 4 and extends them to stochastic games.
- [rl-theory-in-lean](https://reservoir.lean-lang.org/@ShangtongZhang/RL-Theory) ([paper](https://arxiv.org/abs/2511.03618)) proves Q-learning and linear TD convergence with Markovian samples in Lean 4. The Q-learning results here use fresh independent samples instead.

A web search found no earlier machine-checked versions of the regret bounds, the minimax bound, or the policy gradient results above. If you know of one, open an issue.
