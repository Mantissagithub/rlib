module

import Rlib

open Rlib

/-- The first GRPO iterate is the reference policy. -/
example (r : Bool → Bool) (πref : PMF Bool) (β ε : ℝ) : grpoPolicy r πref β ε 0 = πref :=
  rfl

/-- With `p_ref = 1 / 2`, the success-probability map exceeds `1 / 2` everywhere on `[0, 1]`. -/
example (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : 1 / 2 < grpoMap (1 / 2) 1 1 p :=
  lt_grpoMap (by norm_num) (by norm_num) one_pos (by nlinarith [hp.1, hp.2])
