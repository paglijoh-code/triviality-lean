/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Probability

/-!
# Bradley's Preservation argument

If Preservation holds for every credence function, the conditional is trivial: for all `A`, `C`
either `A ⊆ C` or `A → C ⊆ C`. The converse also holds.

## Main results

* `Triviality.bradley_preservation`: R6, the forward direction.
* `Triviality.trivial_preservation`: R6, the converse.
* `Triviality.bradley_preservation_iff`: R6, the equivalence.

## References

* Bradley, "A preservation condition for conditionals", Mind 2000, as discussed in Mandelkern
  and Khoo, "Triviality results and the relationship between logical and natural languages",
  Mind 2019, pp. 425-426.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- R6 (forward direction, Mandelkern and Khoo 2019): if `Preservation` holds for every credence
function, then for all `A`, `C` either
`A ⊆ C` or `A → C ⊆ C`: there is no non-trivial conditional. Take a world `a ∈ A \ C` and a
world `b ∈ (A → C) \ C`, and put weight `1/2` on each. -/
theorem bradley_preservation (imp : Conditional Ω)
    (h : ∀ c : Credence Ω, ∀ A C, Preservation c imp A C) :
    ∀ A C, A ⊆ C ∨ imp A C ⊆ C := by
  intro A C
  by_contra hn
  push Not at hn
  obtain ⟨hA, hB⟩ := hn
  rw [Finset.not_subset] at hA hB
  obtain ⟨a, haA, haC⟩ := hA
  obtain ⟨b, hbB, hbC⟩ := hB
  let c : Credence Ω :=
    { w := fun ω => (if ω = a then 1 / 2 else 0) + (if ω = b then 1 / 2 else 0)
      nonneg := fun ω => by
        have h1 : (0 : ℝ) ≤ if ω = a then 1 / 2 else 0 := by split_ifs <;> norm_num
        have h2 : (0 : ℝ) ≤ if ω = b then 1 / 2 else 0 := by split_ifs <;> norm_num
        exact add_nonneg h1 h2
      sum_one := by
        rw [Finset.sum_add_distrib]
        simp
        norm_num }
  have hwa : (1 / 2 : ℝ) ≤ c.w a := by
    show (1 / 2 : ℝ) ≤ (if a = a then 1 / 2 else 0) + (if a = b then 1 / 2 else 0)
    have : (0 : ℝ) ≤ if a = b then 1 / 2 else 0 := by split_ifs <;> norm_num
    simp only [ite_true]; linarith
  have hwb : (1 / 2 : ℝ) ≤ c.w b := by
    show (1 / 2 : ℝ) ≤ (if b = a then 1 / 2 else 0) + (if b = b then 1 / 2 else 0)
    have : (0 : ℝ) ≤ if b = a then 1 / 2 else 0 := by split_ifs <;> norm_num
    simp only [ite_true]; linarith
  have hprA : 0 < c.pr A := by
    have : c.w a ≤ c.pr A :=
      Finset.single_le_sum (f := c.w) (fun ω _ => c.nonneg ω) haA
    linarith
  have hprC : c.pr C = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    have h1 : ω ≠ a := fun e => haC (e ▸ hω)
    have h2 : ω ≠ b := fun e => hbC (e ▸ hω)
    show (if ω = a then (1 / 2 : ℝ) else 0) + (if ω = b then 1 / 2 else 0) = 0
    simp [h1, h2]
  have h0 := h c A C hprA hprC
  have : c.w b ≤ c.pr (imp A C) :=
    Finset.single_le_sum (f := c.w) (fun ω _ => c.nonneg ω) hbB
  linarith

/-- R6 (converse): if for all `A`, `C` either `A ⊆ C` or `A → C ⊆ C`, then Preservation holds
for every credence function. -/
theorem trivial_preservation (imp : Conditional Ω)
    (h : ∀ A C, A ⊆ C ∨ imp A C ⊆ C) :
    ∀ (c : Credence Ω) (A C : Finset Ω), Preservation c imp A C := by
  intro c A C hA hC
  rcases h A C with hs | hs
  · have := pr_mono c hs
    linarith
  · exact le_antisymm (hC ▸ pr_mono c hs) (pr_nonneg c _)

/-- R6 (iff): Preservation holds for every credence function exactly when the conditional is
trivial, that is, for all `A`, `C` either `A ⊆ C` or `A → C ⊆ C`. -/
theorem bradley_preservation_iff (imp : Conditional Ω) :
    (∀ (c : Credence Ω) (A C : Finset Ω), Preservation c imp A C) ↔
      ∀ A C, A ⊆ C ∨ imp A C ⊆ C :=
  ⟨bradley_preservation imp, trivial_preservation imp⟩

end Triviality
