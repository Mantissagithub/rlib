# Roadmap

Complete and verify one milestone before starting the next.
The first seven milestones are implemented and verified.
Later milestones remain proposals.

1. Finite foundations, complete. Real expectation laws, MDP data, stationary randomized policies, and a checked one-state example.
2. One-step operators, complete. Monotonicity for `0 ≤ γ` and sup-norm error bounds with factor `‖γ‖` for any real `γ`.
3. Policy evaluation, complete. Contraction for a fixed policy with `0 ≤ γ < 1` and a unique solution of its Bellman equation on finite state and action types.
4. Optimality, complete. The finite-action Bellman optimality operator is monotone for `0 ≤ γ`, has a sup-norm error bound for any real `γ`, and has a unique fixed point for `0 ≤ γ < 1`. State and action types are finite, and the action type is nonempty.
5. Algorithms, complete. Value iteration converges from every initial value function to the unique Bellman optimality fixed point for `0 ≤ γ < 1`, on finite state and action types with a nonempty action type. Its error to any supplied fixed point is bounded by `‖γ‖ ^ n * ‖v₀ - v‖` for any real `γ`. A deterministic greedy policy exists for any real discount. For `0 ≤ γ < 1`, a greedy policy has a nondecreasing Bellman value relative to the old policy. Concrete policy iteration uses canonical policy evaluation and a fixed greedy choice depending only on the value function. Its values are nondecreasing, and its policies eventually stabilize at a policy whose value satisfies the Bellman optimality equation. These statements do not require a nonempty state type.
6. Returns, complete. Finite trajectories sample actions and successor states under a stationary randomized policy. Expected discounted sums of stored expected rewards satisfy the fixed-policy Bellman recursion and equal its iterates from zero. The finite expectation requires finite state and action types, with no discount bounds or nonempty-type assumptions. Infinite trajectories have absolutely summable discounted rewards for `0 ≤ γ < 1` on finite state and action types. Finite prefix returns converge to their infinite sum. Finite and infinite return norms are bounded by `‖m.reward‖ / (1 - γ)`. Expected finite returns converge as value functions to the canonical policy value, with no nonempty-type assumptions. A canonical infinite trajectory probability law is constructed, and each finite prefix has exactly the finite trajectory law. The construction requires a finite state type with measurable singletons; the prefix identity additionally requires a finite action type with measurable singletons. No discount bounds or nonempty-type assumptions are needed for these laws. For finite state and action types with measurable singletons and `0 ≤ γ < 1`, infinite returns are integrable under the canonical law, and their integrals equal the policy's Bellman value. This result also needs no nonempty-type assumptions.
7. Learning from samples, complete. Nonempty paired reward and successor observations define an empirical MDP with arbitrary real reward means and observed successor frequencies. Empirical expectation and one-step action values equal their sample means. A two-sided Hoeffding bound applies to independent measurable observations in `[0,1]` with a common expectation, without requiring identical distributions. The empirical reward bound assumes normalized rewards in `[0,1]` and the correct common mean. The empirical transition bound assumes independent measurable successors with the model transition law and measurable singletons. Both bounds are pointwise, require no finite state or action type or discount assumptions, and are instantiated on four independent fair Bool coordinates. A reward and successor within one observation may depend on each other. These results provide no simultaneous row bound, data-dependent continuation guarantee, or independence assertion for samples from a policy trajectory.
8. Q-learning. Formalize stochastic approximation and prove convergence under the required visitation and step-size assumptions.
9. Learning guarantees. Prove sample-complexity or regret bounds for named algorithms under stated MDP assumptions.

## Probability representation

Use mathlib's `PMF` for transitions and policies. Its normalization and probability operations already have proofs.
A custom `FiniteDist` would duplicate those facts and require conversion lemmas before using measure-theoretic results.
Keep real finite expectation in `Rlib.Probability.Expectation` so MDP proofs do not repeat conversions from `ℝ≥0∞` to `ℝ`.

The MDP stores transitions and expected rewards without finite-type assumptions or a discount parameter.
Each operator requests the finite instances it uses. Theorems request discount bounds only when their conclusions need them.
Rewards depending on the sampled next state and unavailable actions need separate design decisions before introduction.
