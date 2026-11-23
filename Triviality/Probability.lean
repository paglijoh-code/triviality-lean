/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Basic

/-!
# Lemmas for `pr` and `cond`

Elementary facts about credence and conditional credence (S2), used by every result.

## Main results

* `Triviality.pr_nonneg`, `Triviality.pr_mono`, `Triviality.pr_union_of_disjoint`,
  `Triviality.pr_total`, `Triviality.pr_univ`, `Triviality.pr_add_pr_compl`: basic probability.
* `Triviality.cond_mul_pr`, `Triviality.cond_eq_one_of_subset`,
  `Triviality.cond_eq_zero_of_disjoint`, `Triviality.pr_eq_of_cond`: conditional probability.
* `Triviality.pr_inter_of_pr_one`: probability-one sets can be intersected away.
* `Triviality.thesis_iff_resilient_univ`: the Thesis is the Resilient Equation under `⊤`.
* `Triviality.pr_eq_one_of_c4`: C4 forces `Pr P = 1`.
-/

open Finset

namespace Triviality

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Probabilities are nonnegative (S2). -/
theorem pr_nonneg (c : Credence Ω) (A : Finset Ω) : 0 ≤ c.pr A :=
  Finset.sum_nonneg fun ω _ => c.nonneg ω

/-- Probability is monotone under inclusion (S2). -/
theorem pr_mono (c : Credence Ω) {A B : Finset Ω} (h : A ⊆ B) : c.pr A ≤ c.pr B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => c.nonneg ω

/-- Probability of a disjoint union adds. -/
theorem pr_union_of_disjoint (c : Credence Ω) {A B : Finset Ω} (h : Disjoint A B) :
    c.pr (A ∪ B) = c.pr A + c.pr B :=
  Finset.sum_union h

/-- Total probability over `Q` and `Qᶜ`: `Pr A = Pr (Q ∩ A) + Pr (Qᶜ ∩ A)`. -/
theorem pr_total (c : Credence Ω) (Q A : Finset Ω) :
    c.pr A = c.pr (Q ∩ A) + c.pr (Qᶜ ∩ A) := by
  unfold Credence.pr
  have h := Finset.sum_inter_add_sum_sdiff A Q c.w
  rw [Finset.inter_comm Q A, Finset.inter_comm Qᶜ A, ← Finset.sdiff_eq_inter_compl]
  exact h.symm

/-- Multiplying a conditional probability back by its condition. No positivity is needed: if
`Pr A = 0` both sides are zero. -/
theorem cond_mul_pr (c : Credence Ω) (B A : Finset Ω) :
    c.cond B A * c.pr A = c.pr (A ∩ B) := by
  unfold Credence.cond
  by_cases h : c.pr A = 0
  · have h0 : c.pr (A ∩ B) = 0 :=
      le_antisymm (h ▸ pr_mono c Finset.inter_subset_left) (pr_nonneg c _)
    rw [h, h0]; simp
  · field_simp

/-- Conditioning on a set containing the event gives 1. -/
theorem cond_eq_one_of_subset (c : Credence Ω) {A B : Finset Ω} (h : 0 < c.pr A)
    (hs : A ⊆ B) : c.cond B A = 1 := by
  unfold Credence.cond
  rw [Finset.inter_eq_left.mpr hs]
  exact div_self h.ne'

/-- Conditioning on a set disjoint from the event gives 0. -/
theorem cond_eq_zero_of_disjoint (c : Credence Ω) {A B : Finset Ω}
    (hd : A ∩ B = ∅) : c.cond B A = 0 := by
  unfold Credence.cond
  simp [hd, Credence.pr]

/-- Total probability via conditionals: if `Pr(X | Q) = 1` and `Pr(X | Qᶜ) = 0`, then
`Pr X = Pr Q`. No positivity is needed. -/
theorem pr_eq_of_cond (c : Credence Ω) (Q X : Finset Ω)
    (h1 : c.cond X Q = 1) (h0 : c.cond X Qᶜ = 0) :
    c.pr X = c.pr Q := by
  have e1 := cond_mul_pr c X Q
  have e0 := cond_mul_pr c X Qᶜ
  rw [h1] at e1
  rw [h0] at e0
  rw [pr_total c Q X, ← e1, ← e0]
  simp

/-- `Pr univ = 1`. -/
theorem pr_univ (c : Credence Ω) : c.pr Finset.univ = 1 := c.sum_one

/-- `Pr Q + Pr Qᶜ = 1`. -/
theorem pr_add_pr_compl (c : Credence Ω) (Q : Finset Ω) : c.pr Q + c.pr Qᶜ = 1 := by
  have := pr_total c Q Finset.univ
  simpa [pr_univ] using this.symm

/-- Probability-one sets: intersecting with them does not change probabilities. -/
theorem pr_inter_of_pr_one (c : Credence Ω) (S A : Finset Ω) (h : c.pr S = 1) :
    c.pr (S ∩ A) = c.pr A := by
  have h1 := pr_total c S A
  have h2 := pr_add_pr_compl c S
  have h3 : c.pr (Sᶜ ∩ A) ≤ c.pr Sᶜ := pr_mono c Finset.inter_subset_left
  have h4 := pr_nonneg c (Sᶜ ∩ A)
  linarith

/-- P1 is the Resilient Equation under the trivial learning `X = ⊤` (P1 versus P2[⊤]). -/
theorem thesis_iff_resilient_univ (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω) :
    Thesis c imp P Q ↔ Resilient c imp P Q Finset.univ := by
  unfold Thesis Resilient
  simp only [Finset.inter_univ, Finset.univ_inter, Credence.cond, pr_univ, div_one]

/-- C4 forces `Pr P = 1` (the first conjunct of Fitelson's conclusion). -/
theorem pr_eq_one_of_c4 {c : Credence Ω} {imp : Conditional Ω} {P Q : Finset Ω}
    (h : C4 c imp P Q) : c.pr P = 1 := by
  have h1 := pr_mono c (Finset.inter_subset_left :
    P ∩ ((Q ∩ imp P Q) ∪ (Qᶜ ∩ (imp P Q)ᶜ)) ⊆ P)
  have h2 : c.pr P ≤ 1 := by
    have := pr_mono c (Finset.subset_univ P); rwa [pr_univ] at this
  unfold C4 at h
  linarith

end Triviality
