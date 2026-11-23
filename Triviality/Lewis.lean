/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Probability

/-!
# Lewis 1976

Lewis's triviality result (R1) and its Thesis-free core (K1).

## Main results

* `Triviality.lewis_1976`: R1, positivity, the Thesis and the Resilient Equation under `Q` and
  `¬Q` give `Pr (Q | P) = Pr Q`.
* `Triviality.lewis_implies_c3`: K1, positivity and the two Resilient instances already give
  `Pr (P → Q) = Pr Q`, without the Thesis.

## References

* Lewis, "Probabilities of conditionals and conditional probabilities", Phil. Review 1976.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- K1 (Lewis's pair, C3): positivity and the Resilient Equation under `Q` and under `¬Q`
give `Pr(P → Q) = Pr(Q)`, without the Thesis. -/
theorem lewis_implies_c3 (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) (h1 : Resilient c imp P Q Q) (h2 : Resilient c imp P Q Qᶜ) :
    c.pr (imp P Q) = c.pr Q := by
  obtain ⟨hp1, hp2⟩ := hpos
  have e1 : c.cond (imp P Q) Q = 1 := by
    rw [h1 hp1]
    exact cond_eq_one_of_subset c hp1 Finset.inter_subset_right
  have e0 : c.cond (imp P Q) Qᶜ = 0 := by
    rw [h2 hp2]
    apply cond_eq_zero_of_disjoint
    ext x; simp
  exact pr_eq_of_cond c Q _ e1 e0

/-- R1 (Lewis 1976): if `Pr(P ∧ Q) > 0`, `Pr(P ∧ ¬Q) > 0`, the Thesis holds for `P → Q`
and the Resilient Equation holds for `P → Q` under both `Q` and `¬Q`, then `Pr(Q | P) = Pr(Q)`. -/
theorem lewis_1976 (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) (hT : Thesis c imp P Q)
    (h1 : Resilient c imp P Q Q) (h2 : Resilient c imp P Q Qᶜ) :
    c.cond Q P = c.pr Q := by
  have hP : 0 < c.pr P := lt_of_lt_of_le hpos.1 (pr_mono c Finset.inter_subset_left)
  rw [← hT hP]
  exact lewis_implies_c3 c imp P Q hpos h1 h2

end Triviality
