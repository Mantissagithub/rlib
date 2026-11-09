# rlib

A Lean library for reinforcement learning mathematics, built on mathlib.
The first three milestones cover finite real expectation, the data of an MDP, one-step operator bounds, and policy evaluation.

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

The library does not yet formalize trajectories, infinite returns, Bellman convergence, or an optimal policy theorem.
See [ROADMAP.md](ROADMAP.md) for the proposed sequence.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run these commands in the repository.

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Probability.ProbabilityMassFunction.Monad Mathlib.Analysis.Normed.Group.Constructions Mathlib.Analysis.Normed.Field.Basic Mathlib.Topology.MetricSpace.Contracting Mathlib.Tactic.NormNum
lake build
python3 scripts/check_axioms.py
```

`lean-toolchain` pins Lean 4.35.0. The Lake dependency pins mathlib v4.35.0.
The axiom audit checks every public theorem in this milestone and rejects axioms outside `propext`, `Classical.choice`, and `Quot.sound`.
It rejects `sorryAx` and custom axioms, including those inherited through dependencies.
CI runs the build and audit.

Import the library with `import Rlib`.
