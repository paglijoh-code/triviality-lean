/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Lewis

/-!
# Route: Goldstein and Santorio, probability over paths

Goldstein and Santorio (2021, "Probability for Epistemic Modalities") move the conditional from
worlds to paths. A path is an ordering of the worlds. A descriptive sentence is true at a path iff
it is true at the first world of the path, and "if A, B" (A, B descriptive) is true at a path iff B
holds at the first A-world of the path. The credence on paths is lifted from a credence on worlds:
`C (a, b, c) = Pr a * Pr b / (Pr b + Pr c)`.

The model here has three worlds with `Pr = (1/2, 1/3, 1/6)`. The six paths form `Fin 6`, with an
explicit table of paths and weights. The conditional `gsImp` is a total operator on propositions
over paths (it reads a proposition as the set of first worlds it contains), and it agrees with
Goldstein and Santorio on the descriptive (lifted) contents used below.

## Main results

* `Triviality.Routes.gs_pr_liftW`: the lift preserves the credence of the worlds.
* `Triviality.Routes.gs_thesis`: the Thesis holds for `P = w1 or w2` and `Q = w1`.
* `Triviality.Routes.gs_resilient_Q` and `Triviality.Routes.gs_resilient_notQ_fails`: the
  Resilient Equation holds at `Q` and fails at `¬Q`.
* `Triviality.Routes.gs_verdict`: `Pr (Q | P) = 3/5 ≠ 1/2 = Pr Q` with the Thesis and P2[Q].
* `Triviality.Routes.gs_hc_is_lift`: after Hyperconditionalization on `¬w1`, the credence on
  paths is the lift of the conditioned world credence (instance of their Theorem 3).
* `Triviality.Routes.gs_cond_not_lift`: ordinary conditioning on `¬w1` is not the lift.

## Verdict

The route keeps S1 to S4: the path space is finite and there is one fixed conditional. Lewis 1976
needs the Resilient Equation at `Q` and at `¬Q`; here P2[`¬Q`] fails (`gs_resilient_notQ_fails`),
so the denied premise is P2[X] for `X = ¬Q` under conditionalization. Goldstein and Santorio
replace conditionalization by Hyperconditionalization, under which the Thesis survives updating
(instance in `gs_hc_is_lift`).

Caveats: this is one 3-world model and one antecedent-consequent pair. Their general Theorems 1 and
3 are not formalized. The source is the 30 March 2021 preprint from the author's site.

## References

* Goldstein and Santorio, "Probability for Epistemic Modalities", Philosophers' Imprint 2021
  (preprint of 30 March 2021).
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace Routes

/-- Route Goldstein–Santorio: the weights of the six paths, in the order
`123, 132, 213, 231, 312, 321`. -/
noncomputable def gsWeight : Fin 6 → ℝ := ![1/3, 1/6, 1/4, 1/12, 1/10, 1/15]

theorem gsW0 : gsWeight 0 = 1/3 := by first | rfl | simp [gsWeight]
theorem gsW1 : gsWeight 1 = 1/6 := by first | rfl | simp [gsWeight]
theorem gsW2 : gsWeight 2 = 1/4 := by first | rfl | simp [gsWeight]
theorem gsW3 : gsWeight 3 = 1/12 := by first | rfl | simp [gsWeight]
theorem gsW4 : gsWeight 4 = 1/10 := by first | rfl | simp [gsWeight]
theorem gsW5 : gsWeight 5 = 1/15 := by first | rfl | simp [gsWeight]

theorem gsWeight_nonneg (p : Fin 6) : 0 ≤ gsWeight p := by
  fin_cases p <;>
    first
    | (norm_num [gsWeight]; done)
    | (simp [gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]; done)

theorem gsWeight_sum : ∑ p, gsWeight p = 1 := by
  norm_num [Fin.sum_univ_six, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

/-- Route Goldstein–Santorio: the lifted credence on the six paths. -/
noncomputable def gsCred : Credence (Fin 6) where
  w := gsWeight
  nonneg := gsWeight_nonneg
  sum_one := gsWeight_sum

/-- Route Goldstein–Santorio: the six paths, as orderings of the worlds `w1, w2, w3 = 0, 1, 2`. -/
def gsPath : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- Route Goldstein–Santorio: the descriptive content `A`, as the set of paths whose first world
is in `A`. -/
def liftW (A : Finset (Fin 3)) : Finset (Fin 6) :=
  univ.filter (fun p => gsPath p 0 ∈ A)

/-- Route Goldstein–Santorio: "if `A`, `B`" on descriptive `A`, `B`: the paths where `B` holds at
the first `A`-world of the path (all paths with no `A`-world). -/
def gsIf (A B : Finset (Fin 3)) : Finset (Fin 6) :=
  univ.filter (fun p =>
    (gsPath p 0 ∈ A ∧ gsPath p 0 ∈ B) ∨
    (gsPath p 0 ∉ A ∧ gsPath p 1 ∈ A ∧ gsPath p 1 ∈ B) ∨
    (gsPath p 0 ∉ A ∧ gsPath p 1 ∉ A ∧ gsPath p 2 ∈ A ∧ gsPath p 2 ∈ B) ∨
    (gsPath p 0 ∉ A ∧ gsPath p 1 ∉ A ∧ gsPath p 2 ∉ A))

/-- Route Goldstein–Santorio: the set of first worlds of a set of paths. -/
def gsUnlift (X : Finset (Fin 6)) : Finset (Fin 3) :=
  X.image (fun p => gsPath p 0)

/-- Route Goldstein–Santorio: the conditional as a total operator on propositions over paths. It
reads each proposition by its first worlds, so it agrees with `gsIf` on lifted contents. -/
def gsImp : Conditional (Fin 6) := fun X Y => gsIf (gsUnlift X) (gsUnlift Y)

/-- Route Goldstein–Santorio: `gsPr` of a set is the sum of its path weights. -/
theorem gs_pr_eq (S : Finset (Fin 6)) : gsCred.pr S = ∑ p ∈ S, gsWeight p := rfl

theorem gs_liftW_0 : liftW {0} = ({0, 1} : Finset (Fin 6)) := by decide
theorem gs_liftW_1 : liftW {1} = ({2, 3} : Finset (Fin 6)) := by decide
theorem gs_liftW_2 : liftW {2} = ({4, 5} : Finset (Fin 6)) := by decide
theorem gs_liftW_01 : liftW {0, 1} = ({0, 1, 2, 3} : Finset (Fin 6)) := by decide
theorem gs_liftW_12 : liftW {1, 2} = ({2, 3, 4, 5} : Finset (Fin 6)) := by decide

/-- Route Goldstein–Santorio: reading a lifted content back recovers the world set. -/
theorem gs_unlift_liftW :
    gsUnlift (liftW {0}) = {0} ∧ gsUnlift (liftW {1}) = {1} ∧ gsUnlift (liftW {2}) = {2} ∧
    gsUnlift (liftW {0, 1}) = {0, 1} ∧ gsUnlift (liftW {1, 2}) = {1, 2} := by
  decide

/-- Route Goldstein–Santorio: the conditional "if `w1 or w2`, `w1`" is the path set `{0, 1, 4}`
(paths `123`, `132`, `312`). -/
theorem gs_imp_val : gsImp (liftW {0, 1}) (liftW {0}) = ({0, 1, 4} : Finset (Fin 6)) := by
  decide

theorem gs_pr_01 : gsCred.pr ({0, 1} : Finset (Fin 6)) = 1 / 2 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_23 : gsCred.pr ({2, 3} : Finset (Fin 6)) = 1 / 3 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_45 : gsCred.pr ({4, 5} : Finset (Fin 6)) = 1 / 6 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_0123 : gsCred.pr ({0, 1, 2, 3} : Finset (Fin 6)) = 5 / 6 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_014 : gsCred.pr ({0, 1, 4} : Finset (Fin 6)) = 3 / 5 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_4 : gsCred.pr ({4} : Finset (Fin 6)) = 1 / 10 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_2 : gsCred.pr ({2} : Finset (Fin 6)) = 1 / 4 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_2345 : gsCred.pr ({2, 3, 4, 5} : Finset (Fin 6)) = 1 / 2 := by
  rw [gs_pr_eq]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_pr_empty : gsCred.pr (∅ : Finset (Fin 6)) = 0 := by
  rw [gs_pr_eq]
  exact Finset.sum_empty

/-- Route Goldstein–Santorio: the lift preserves the credence of the worlds,
`Pr = (1/2, 1/3, 1/6)` on `w1, w2, w3`. -/
theorem gs_pr_liftW :
    gsCred.pr (liftW {0}) = 1 / 2 ∧ gsCred.pr (liftW {1}) = 1 / 3 ∧
    gsCred.pr (liftW {2}) = 1 / 6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gs_liftW_0, gs_pr_01]
  · rw [gs_liftW_1, gs_pr_23]
  · rw [gs_liftW_2, gs_pr_45]

theorem gs_PQ : liftW {0, 1} ∩ liftW {0} = ({0, 1} : Finset (Fin 6)) := by decide

theorem gs_compl_Q : (liftW {0})ᶜ = ({2, 3, 4, 5} : Finset (Fin 6)) := by decide

theorem gs_PnQ : liftW {0, 1} ∩ (liftW {0})ᶜ = ({2, 3} : Finset (Fin 6)) := by decide

/-- Route Goldstein–Santorio: the Thesis holds for `P = w1 or w2` and `Q = w1`:
`Pr (P → Q) = 3/5 = Pr (Q | P)`. -/
theorem gs_thesis : Thesis gsCred gsImp (liftW {0, 1}) (liftW {0}) := by
  unfold Thesis
  intro _
  unfold Credence.cond
  rw [gs_imp_val, gs_PQ, gs_liftW_01, gs_pr_014, gs_pr_01, gs_pr_0123]
  norm_num

/-- Route Goldstein–Santorio: the Resilient Equation holds at `Q`: both sides equal `1`. -/
theorem gs_resilient_Q :
    Resilient gsCred gsImp (liftW {0, 1}) (liftW {0}) (liftW {0}) := by
  unfold Resilient
  intro _
  rw [gs_imp_val, gs_liftW_0, gs_liftW_01]
  unfold Credence.cond
  have a : ({0, 1, 2, 3} : Finset (Fin 6)) ∩ {0, 1} = {0, 1} := by decide
  have b : ({0, 1} : Finset (Fin 6)) ∩ {0, 1, 4} = {0, 1} := by decide
  have c : ({0, 1} : Finset (Fin 6)) ∩ {0, 1} = {0, 1} := by decide
  simp only [a, b, c]

/-- Route Goldstein–Santorio: the Resilient Equation fails at `¬Q`. Here
`Pr (P → Q | ¬Q) = (1/10) / (1/2) = 1/5`, while `Pr (Q | P ∧ ¬Q) = 0`. -/
theorem gs_resilient_notQ_fails :
    ¬ Resilient gsCred gsImp (liftW {0, 1}) (liftW {0}) (liftW {0})ᶜ := by
  intro h
  have hpos : 0 < gsCred.pr (liftW {0, 1} ∩ (liftW {0})ᶜ) := by
    rw [gs_PnQ, gs_pr_23]
    norm_num
  have h2 := h hpos
  rw [gs_PnQ, gs_imp_val, gs_compl_Q, gs_liftW_0] at h2
  unfold Credence.cond at h2
  have d1 : ({2, 3, 4, 5} : Finset (Fin 6)) ∩ {0, 1, 4} = {4} := by decide
  have d2 : ({2, 3} : Finset (Fin 6)) ∩ {0, 1} = ∅ := by decide
  rw [d1, d2, gs_pr_4, gs_pr_2345, gs_pr_empty, gs_pr_23] at h2
  norm_num at h2

theorem gs_positive : Positive gsCred (liftW {0, 1}) (liftW {0}) := by
  unfold Positive
  refine ⟨?_, ?_⟩
  · rw [gs_PQ, gs_pr_01]
    norm_num
  · rw [gs_PnQ, gs_pr_23]
    norm_num

theorem gs_cond_ne : gsCred.cond (liftW {0}) (liftW {0, 1}) ≠ gsCred.pr (liftW {0}) := by
  intro h
  unfold Credence.cond at h
  rw [gs_PQ, gs_liftW_01, gs_liftW_0, gs_pr_01, gs_pr_0123] at h
  norm_num at h

/-- Route Goldstein–Santorio: verdict. With `P = w1 or w2` and `Q = w1`, the pair is positive, the
Thesis holds, P2[`Q`] holds, P2[`¬Q`] fails, and `Pr (Q | P) = 3/5 ≠ 1/2 = Pr Q`. So the
conclusion of Lewis 1976 fails here; since `lewis_1976` needs the Resilient Equation at `Q` and at
`¬Q`, the premise denied is P2[`¬Q`]. S1 to S4 are kept (finite path space, one fixed
conditional). -/
theorem gs_verdict :
    Positive gsCred (liftW {0, 1}) (liftW {0}) ∧
    Thesis gsCred gsImp (liftW {0, 1}) (liftW {0}) ∧
    Resilient gsCred gsImp (liftW {0, 1}) (liftW {0}) (liftW {0}) ∧
    ¬ Resilient gsCred gsImp (liftW {0, 1}) (liftW {0}) (liftW {0})ᶜ ∧
    gsCred.cond (liftW {0}) (liftW {0, 1}) ≠ gsCred.pr (liftW {0}) :=
  ⟨gs_positive, gs_thesis, gs_resilient_Q, gs_resilient_notQ_fails, gs_cond_ne⟩

/-- Route Goldstein–Santorio: each path sent to its subsequence without `w1`; index `0` is
`(w2, w3)` and index `1` is `(w3, w2)`. -/
def gsPlus : Fin 6 → Fin 2 := ![0, 1, 0, 0, 1, 1]

/-- Route Goldstein–Santorio: the weight of a path of the updated space, the total weight of the
old paths that restrict to it. -/
noncomputable def gsHCw (q : Fin 2) : ℝ :=
  ∑ p ∈ univ.filter (fun p => gsPlus p = q), gsWeight p

theorem gs_hcw_0 : gsHCw 0 = 2 / 3 := by
  have hf : (univ.filter (fun p : Fin 6 => gsPlus p = 0)) = ({0, 2, 3} : Finset (Fin 6)) := by
    decide
  unfold gsHCw
  rw [hf]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

theorem gs_hcw_1 : gsHCw 1 = 1 / 3 := by
  have hf : (univ.filter (fun p : Fin 6 => gsPlus p = 1)) = ({1, 4, 5} : Finset (Fin 6)) := by
    decide
  unfold gsHCw
  rw [hf]
  norm_num [Finset.sum_insert, gsW0, gsW1, gsW2, gsW3, gsW4, gsW5]

/-- Route Goldstein–Santorio: the Hyperconditionalized credence on `¬w1`, on the two paths
`(w2, w3)` and `(w3, w2)`. -/
noncomputable def gsHC : Credence (Fin 2) where
  w := gsHCw
  nonneg := fun _ => Finset.sum_nonneg (fun p _ => gsWeight_nonneg p)
  sum_one := by
    norm_num [Fin.sum_univ_two, gs_hcw_0, gs_hcw_1]

/-- Route Goldstein–Santorio: Hyperconditionalization on `¬w1` gives the path weights `2/3` and
`1/3`, which are `Pr (w2 | ¬w1)` and `Pr (w3 | ¬w1)`: the lift of the conditioned world credence
(an instance of their Theorem 3). -/
theorem gs_hc_is_lift : gsHC.w 0 = 2 / 3 ∧ gsHC.w 1 = 1 / 3 :=
  ⟨gs_hcw_0, gs_hcw_1⟩

/-- Route Goldstein–Santorio: ordinary conditioning on `¬w1 = w2 or w3` (`liftW {1, 2}`, the paths
`213, 231, 312, 321`) gives path `213` credence `1/2` and the paths starting with `w1` credence
`0`, so conditionalization keeps mass on paths that still contain the ruled-out `w1`; it is not
the lift of the conditioned world credence (which puts `(1/2) * (1/3) / (1/2)`-style weights on
the paths of the shorter space). -/
theorem gs_cond_not_lift :
    liftW {1, 2} = ({2, 3, 4, 5} : Finset (Fin 6)) ∧
    gsCred.pr ({2} ∩ liftW {1, 2}) / gsCred.pr (liftW {1, 2}) = 1 / 2 := by
  refine ⟨gs_liftW_12, ?_⟩
  have e : ({2} : Finset (Fin 6)) ∩ {2, 3, 4, 5} = {2} := by decide
  rw [gs_liftW_12, e, gs_pr_2, gs_pr_2345]
  norm_num

end Routes

end Triviality
