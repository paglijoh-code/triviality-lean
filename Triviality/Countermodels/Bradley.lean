/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Basic

/-!
# Countermodel for Bradley's Preservation argument

Negative control for `Triviality.bradley_preservation` (R6): without Preservation there is a
non-trivial conditional.

## Main results

* `Triviality.bradley_drop_preservation`: R6 control.

## References

* Bradley, "A preservation condition for conditionals", Mind 2000, as discussed in Mandelkern
  and Khoo, Mind 2019, pp. 425-426.
-/

open Finset

namespace Triviality

/-- R6 (control): without Preservation there is a non-trivial conditional. On `Fin 2`, with
`A = {0}`, `C = ∅` and `A → C := univ`, we have `A ⊄ C` and `A → C ⊄ C`, and the uniform credence
violates Preservation (`Pr A = 1/2 > 0`, `Pr C = 0`, `Pr (A → C) = 1`). -/
theorem bradley_drop_preservation :
    ∃ (imp : Conditional (Fin 2)) (A C : Finset (Fin 2)) (c : Credence (Fin 2)),
      ¬ (A ⊆ C ∨ imp A C ⊆ C) ∧ ¬ Preservation c imp A C := by
  let c : Credence (Fin 2) :=
    { w := fun _ => 1 / 2
      nonneg := fun _ => by norm_num
      sum_one := by simp }
  refine ⟨fun _ _ => Finset.univ, {0}, ∅, c, ?_, ?_⟩
  · decide
  · intro hP
    have := hP (by simp [Credence.pr, c]) (by simp [Credence.pr])
    simp [Credence.pr, c] at this

end Triviality
