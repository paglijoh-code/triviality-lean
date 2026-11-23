/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Mathlib

/-!
# The setting and the premises of the triviality results

* S1 worlds: a finite type `Ω`; propositions are `Finset Ω`.
* S2 credence: a probability mass function on `Ω`.
* S3 the conditional is a proposition: an arbitrary binary operation `imp` on propositions.
  Nothing else is assumed about it.
* S4 a single credence function (no closure under conditioning).

## Main definitions

* `Triviality.Credence`, `Triviality.Credence.pr`, `Triviality.Credence.cond`: S2.
* `Triviality.Conditional`: S3.
* `Triviality.Thesis` (P1), `Triviality.Resilient` (P2[X]), `Triviality.PIE`,
  `Triviality.Preservation`, `Triviality.Positive`: the premises.
* `Triviality.C4`: Fitelson's conclusion.

## References

* Lewis, "Probabilities of conditionals and conditional probabilities", Phil. Review 1976.
* Milne, "The simplest Lewis-style triviality proof yet?", Mind 2003.
* Fitelson, "The strongest possible Lewisian triviality result", Thought 2015.
* Khoo and Mandelkern, "Triviality results and the relationship between logical and natural
  languages", Mind 2019.
* Bradley, "A preservation condition for conditionals", Mind 2000, as cited by Mandelkern and
  Khoo.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- S2: a credence function, given by nonnegative weights summing to one. -/
structure Credence (Ω : Type*) [Fintype Ω] where
  /-- The weight of each world. -/
  w : Ω → ℝ
  /-- Weights are nonnegative. -/
  nonneg : ∀ ω, 0 ≤ w ω
  /-- Weights sum to one. -/
  sum_one : ∑ ω, w ω = 1

/-- `Pr A`, the credence of the proposition `A` (S2). -/
def Credence.pr (c : Credence Ω) (A : Finset Ω) : ℝ := ∑ ω ∈ A, c.w ω

/-- `Pr (B | A) = Pr (A ∧ B) / Pr A` (Lean's `x / 0 = 0`; every use is guarded by `0 < Pr A`). -/
noncomputable def Credence.cond (c : Credence Ω) (B A : Finset Ω) : ℝ := c.pr (A ∩ B) / c.pr A

/-- S3: a conditional operator. `imp A B` is the proposition "if A, B". -/
abbrev Conditional (Ω : Type*) := Finset Ω → Finset Ω → Finset Ω

/-- P1, the Equation (Stalnaker's Thesis), for one antecedent–consequent pair:
`Pr (A → B) = Pr (B | A)`, guarded by `0 < Pr A`. -/
def Thesis (c : Credence Ω) (imp : Conditional Ω) (A B : Finset Ω) : Prop :=
  0 < c.pr A → c.pr (imp A B) = c.cond B A

/-- P2[X], the Resilient Equation for `P → Q` under learning `X`:
`Pr (P → Q | X) = Pr (Q | P ∧ X)`, guarded by `0 < Pr (P ∧ X)`. -/
def Resilient (c : Credence Ω) (imp : Conditional Ω) (P Q X : Finset Ω) : Prop :=
  0 < c.pr (P ∩ X) → c.cond (imp P Q) X = c.cond Q (P ∩ X)

/-- PIE, Probabilistic Import-Export, for one triple:
`Pr (A → (B → C)) = Pr ((A ∧ B) → C)`. -/
def PIE (c : Credence Ω) (imp : Conditional Ω) (A B C : Finset Ω) : Prop :=
  c.pr (imp A (imp B C)) = c.pr (imp (A ∩ B) C)

/-- Preservation (Bradley): if `A` is possible and `C` is impossible, then `A → C` is impossible. -/
def Preservation (c : Credence Ω) (imp : Conditional Ω) (A C : Finset Ω) : Prop :=
  0 < c.pr A → c.pr C = 0 → c.pr (imp A C) = 0

/-- Positivity: `Pr (P ∧ Q) > 0` and `Pr (P ∧ ¬Q) > 0`. -/
def Positive (c : Credence Ω) (P Q : Finset Ω) : Prop :=
  0 < c.pr (P ∩ Q) ∧ 0 < c.pr (P ∩ Qᶜ)

/-- C4 (Fitelson): `Pr (P ∧ (Q ↔ (P → Q))) = 1`. It says that `P` is almost sure and that `Q`
and `P → Q` agree almost surely. -/
def C4 (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω) : Prop :=
  c.pr (P ∩ ((Q ∩ imp P Q) ∪ (Qᶜ ∩ (imp P Q)ᶜ))) = 1

end Triviality
