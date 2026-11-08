# Working on rlib

- Reuse mathlib definitions and theorems before adding local alternatives. Search the pinned source first.
- Keep public declarations in `Rlib`. Follow mathlib naming and documentation conventions.
- Use mathlib's `PMF` for discrete probability. Keep finite real expectation conversions in `Rlib/Probability/Expectation.lean`.
- State only the assumptions the definition or theorem needs. Document the reward convention and action availability when extending the MDP model.
- Do not use `sorry`, `admit`, `sorryAx`, custom axioms, or unchecked proof shortcuts.
- Add every public theorem to `RlibTest/Axioms.lean`. Keep the audit whitelist limited to `propext`, `Classical.choice`, and `Quot.sound`.
- Work on one small milestone at a time. Run `lake build` and `python3 scripts/check_axioms.py` before calling it complete.
- Keep future work in `ROADMAP.md`. Do not add placeholder declarations or claim unproved results.
- Keep changes surgical. Do not change pins or add dependencies without a concrete need.
