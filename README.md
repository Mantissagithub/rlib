# rlib

Reinforcement learning theory in Lean, built on [mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to give new RL proofs a shared starting point: definitions of environments and policies, probability tools, and results that Lean has already checked.

## What is proved

The current results cover finite state and action sets:

- A fixed policy has exactly one solution to its Bellman equation.
- Value iteration converges to the Bellman optimality solution from any starting estimate.
- Choosing a greedy policy cannot lower the policy's Bellman value.
- Policy iteration eventually stops changing, using a fixed rule for choosing between tied actions.
- Expected rewards over a finite sampled trajectory equal repeated fixed-policy Bellman updates from zero and converge to the policy value.
- The infinite trajectory probability law has exactly the finite trajectory laws as its prefix distributions.
- Infinite discounted returns are absolutely summable. Finite prefix returns converge to them, and both obey the geometric reward bound.
- Infinite discounted returns are integrable under the trajectory law, and their expectations equal the policy's Bellman value.

The uniqueness, convergence, policy-improvement, summability, and return-bound results assume a discount factor `0 ≤ γ < 1`. The finite-horizon return identities allow any real discount. The trajectory law and its prefix distributions do not depend on a discount. Maximizing over actions requires at least one action.

## The model and its scope

An environment specifies transition probabilities and an expected immediate reward for each state and action. Every action is available in every state. Policies can choose actions randomly, based on the current state. Policy iteration uses deterministic policies.

Trajectories record the action and next state at each step. Their returns sum the model's stored expected rewards, rather than sampled reward noise.

Policy values are defined by Bellman equations and equal both the limits of expected finite returns and the expected infinite returns under the trajectory law. The infinite expectation result assumes finite state and action types with measurable singletons and `0 ≤ γ < 1`. The definitions use exact real numbers.

See [ROADMAP.md](ROADMAP.md) for completed and planned work.

## Find the code

| File | What it contains |
| --- | --- |
| [Probability/Expectation](Rlib/Probability/Expectation.lean) | Finite expectation, linearity, bounds, and sequential sampling |
| [MDP/Basic](Rlib/MDP/Basic.lean) | Environments, policies, and one-step values |
| [MDP/OneStep](Rlib/MDP/OneStep.lean) | Ordering and error bounds for one-step updates |
| [MDP/PolicyEvaluation](Rlib/MDP/PolicyEvaluation.lean) | A policy's unique Bellman value |
| [MDP/Optimality](Rlib/MDP/Optimality.lean) | The Bellman operator that takes the best action |
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
  Mathlib.Data.Fintype.Pigeonhole
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
```

CI builds the library, audits the public theorems, and compiles the examples. These include stochastic transitions, negative rewards, and tied actions.

The [axiom audit](scripts/check_axioms.py) rejects unfinished proofs and unexpected axioms. It allows only `propext`, `Classical.choice`, and `Quot.sound`.
