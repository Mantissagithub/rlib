# Roadmap

Complete and verify one milestone before starting the next.
The first two milestones are implemented and verified. Later items remain proposals.

1. Finite foundations, complete. Real expectation laws, MDP data, stationary randomized policies, and a checked one-state example.
2. One-step operators, complete. Monotonicity for `0 ≤ γ` and sup-norm error bounds with factor `‖γ‖` for any real `γ`.
3. Policy evaluation. Prove contraction for a fixed policy with `0 ≤ γ < 1`, then existence and uniqueness of its value.
4. Optimality. Define the finite-action Bellman optimality operator and prove its contraction and fixed-point theorem.
5. Algorithms. Formalize value iteration and policy iteration with their precise convergence assumptions.
6. Returns. Relate the operator definitions to finite trajectories, then justify infinite discounted returns.
7. Learning from samples. Define empirical transitions and rewards, then prove concentration bounds under explicit sampling assumptions.
8. Q-learning. Formalize stochastic approximation and prove convergence under the required visitation and step-size assumptions.
9. Learning guarantees. Prove sample-complexity or regret bounds for named algorithms under stated MDP assumptions.

## Probability representation

Use mathlib's `PMF` for transitions and policies. Its normalization and probability operations already have proofs.
A custom `FiniteDist` would duplicate those facts and require conversion lemmas before using measure-theoretic results.
Keep real finite expectation in `Rlib.Probability.Expectation` so MDP proofs do not repeat conversions from `ℝ≥0∞` to `ℝ`.

The MDP stores transitions and expected rewards without finite-type assumptions or a discount parameter.
Each operator requests the finite instances it uses. Theorems request discount bounds only when their conclusions need them.
Rewards depending on the sampled next state and unavailable actions need separate design decisions before introduction.
