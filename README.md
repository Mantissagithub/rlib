# rlib

A Lean library for reinforcement learning mathematics, built on mathlib.
The first four milestones cover finite real expectation, the data of an MDP, one-step operator bounds, policy evaluation, and Bellman optimality.
The algorithms milestone is partially complete with value iteration convergence and policy improvement.

`Rlib.Probability.Expectation` defines `expect` for mathlib's `PMF` on a finite type.
It proves normalization, constant and zero expectation, linearity, monotonicity, and evaluation under a point mass.
The difference between two expectations is at most the sup-norm distance between their input functions.

`Rlib.MDP.Basic` defines transitions, expected immediate rewards, and stationary randomized policies.
All actions are available in every state. State and action types need finite instances only for the expectation operations.
One-step values take an explicit real discount parameter. They do not yet require discount bounds.
The one-state example checks a concrete discounted value.

`Rlib.MDP.OneStep` proves monotonicity of action and policy values for `0 ≤ γ`.
For any real `γ`, their error bounds use `‖γ‖ * ‖v - w‖`.
The policy bound uses the sup norm over all states.

`Rlib.MDP.PolicyEvaluation` fixes a stationary randomized policy on finite state and action types.
For a real discount with `0 ≤ γ < 1`, the policy operator is a contraction with factor `γ` in the sup norm.
There is exactly one function `v : S → ℝ` satisfying the Bellman equation `m.oneStepValue π γ v = v`.
These results require no nonempty-type assumptions on the state or action types.

`Rlib.MDP.Optimality` takes the maximum one-step value over all actions on finite state and action types, with a nonempty action type.
Its monotonicity requires `0 ≤ γ`, and its sup-norm error bound uses `‖γ‖ * ‖v - w‖` for any real `γ`.
For `0 ≤ γ < 1`, it is a contraction with factor `γ` and has exactly one solution of `m.optimalityOperator γ v = v`.
No nonempty state assumption is needed. This fixed-point result does not establish the existence of an optimal policy or identify the fixed point with infinite discounted returns.
The compiled test in `RlibTest/Optimality.lean` checks that rewards `-2` and `-1` produce a maximum of `-1` when the discount is zero.

`Rlib.MDP.ValueIteration` repeatedly applies the Bellman optimality operator to an initial value function.
For any real `γ`, the error after `n` steps to any supplied Bellman fixed point `v` is at most `‖γ‖ ^ n * ‖v₀ - v‖`.
For `0 ≤ γ < 1`, every initial value function converges to the unique Bellman optimality fixed point.
These results use finite state and action types and a nonempty action type, without a nonempty state assumption.
The compiled test in `RlibTest/ValueIteration.lean` checks that two iterations from zero give value `3` in the one-state example with reward `2` and discount `1 / 2`.

`Rlib.MDP.PolicyImprovement` bounds every policy's one-step value by the Bellman optimality operator and proves that a deterministic greedy policy exists for any real discount.
For `0 ≤ γ < 1`, a policy greedy with respect to an old policy's Bellman value has a nondecreasing Bellman value.
Every policy Bellman value therefore admits a greedy policy and a new Bellman value at least as large at every state.
These results use finite state and action types and a nonempty action type, without a nonempty state assumption.
The compiled test in `RlibTest/PolicyImprovement.lean` applies policy improvement to a one-state model with rewards `-2` and `-1` and discount `1 / 2`, comparing the old Bellman value `-4` with the new Bellman value `-2`.

The library does not yet formalize the full policy iteration algorithm or its termination, trajectories, infinite returns, or an optimal policy theorem.
Value iteration convergence concerns the Bellman fixed point only and does not identify it with infinite discounted returns.
See [ROADMAP.md](ROADMAP.md) for the proposed sequence.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run these commands in the repository.

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Probability.ProbabilityMassFunction.Monad Mathlib.Analysis.Normed.Group.Constructions Mathlib.Analysis.Normed.Field.Basic Mathlib.Topology.MetricSpace.Contracting Mathlib.Data.Finset.Lattice.Fold Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Topology.Order.OrderClosed
lake build
python3 scripts/check_axioms.py
lake env lean -DwarningAsError=true RlibTest/Optimality.lean
lake env lean -DwarningAsError=true RlibTest/ValueIteration.lean
lake env lean -DwarningAsError=true RlibTest/PolicyImprovement.lean
```

`lean-toolchain` pins Lean 4.35.0. The Lake dependency pins mathlib v4.35.0.
The axiom audit checks every public theorem in this milestone and rejects axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
It rejects `sorryAx` and custom axioms, including those inherited through dependencies.
CI runs the build, axiom audit, and all three compiled examples.

Import the library with `import Rlib`.
