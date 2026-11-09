# Roadmap

Complete and verify one milestone before starting the next.
The first five milestones are implemented and verified.
Later items remain proposals.

1. Finite foundations, complete. Real expectation laws, MDP data, stationary randomized policies, and a checked one-state example.
2. One-step operators, complete. Monotonicity for `0 ≤ γ` and sup-norm error bounds with factor `‖γ‖` for any real `γ`.
3. Policy evaluation, complete. Contraction for a fixed policy with `0 ≤ γ < 1` and a unique solution of its Bellman equation on finite state and action types.
4. Optimality, complete. The finite-action Bellman optimality operator is monotone for `0 ≤ γ`, has a sup-norm error bound for any real `γ`, and has a unique fixed point for `0 ≤ γ < 1`. State and action types are finite, and the action type is nonempty.
5. Algorithms, complete. Value iteration converges from every initial value function to the unique Bellman optimality fixed point for `0 ≤ γ < 1`, on finite state and action types with a nonempty action type. Its error to any supplied fixed point is bounded by `‖γ‖ ^ n * ‖v₀ - v‖` for any real `γ`. A deterministic greedy policy exists for any real discount. For `0 ≤ γ < 1`, a greedy policy has a nondecreasing Bellman value relative to the old policy. Concrete policy iteration uses canonical policy evaluation and a fixed greedy choice depending only on the value function. Its values are nondecreasing, and its policies eventually stabilize at a policy whose value satisfies the Bellman optimality equation. These statements do not require a nonempty state type and do not yet identify Bellman values with trajectory returns.
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
