/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Probability

/-!
# Milne and Fitelson: triviality with the Resilient Equation

With `I = imp P Q`, the condition `C4` says that `P` is almost sure and that `Q` and `I` agree
almost surely: `Pr (P ∧ ((Q ∧ I) ∨ (¬Q ∧ ¬I))) = 1`.

## Main results

* `Triviality.milne_collapse`: positivity, the Thesis and the Resilient Equation under `P ⊃ Q`
  give C4 (Milne 2003, in Fitelson's C4 form).
* `Triviality.fitelson_three_instances`: R3, Fitelson's statement as published.
* `Triviality.fitelson_triviality`: R2, given positivity the Resilient Equation holds under every
  `X` iff C4.
* `Triviality.fitelson_maximality`: R4, the pair `{⊤, P ⊃ Q}` is maximal.
* `Triviality.fitelson_ie_iff_resilient`: R5, PIE and the Resilient Equation are equivalent under
  the Thesis.
* `Triviality.pie_iff_resilient`: the same for one instance, from two instances of the Thesis.

## References

* Milne, "The simplest Lewis-style triviality proof yet?", Mind 2003.
* Fitelson, "The strongest possible Lewisian triviality result", Thought 2015.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Implementation detail: the algebra of R3 over the cells of `P`, `Q`, `I`. Only the Thesis for
`P → Q` and
the Resilient Equation under `¬P ∨ Q` are used. -/
theorem fitelson_core (c : Credence Ω) (P Q I : Finset Ω)
    (hp1 : 0 < c.pr (P ∩ Q)) (hp2 : 0 < c.pr (P ∩ Qᶜ))
    (hT : c.pr I = c.cond Q P) (hX : c.cond I (Pᶜ ∪ Q) = 1) :
    c.pr (P ∩ ((Q ∩ I) ∪ (Qᶜ ∩ Iᶜ))) = 1 := by
  have hsub : P ∩ Q ⊆ Pᶜ ∪ Q := fun x hx => by simp at hx ⊢; tauto
  have hXpos : 0 < c.pr (Pᶜ ∪ Q) := lt_of_lt_of_le hp1 (pr_mono c hsub)
  -- `Pr (X ∧ ¬I) = 0` for `X = ¬P ∨ Q`
  have h0 : c.pr ((Pᶜ ∪ Q) ∩ Iᶜ) = 0 := by
    unfold Credence.cond at hX
    have h1 := (div_eq_one_iff_eq hXpos.ne').1 hX
    have h2 := pr_total c I (Pᶜ ∪ Q)
    have h3 : c.pr (I ∩ (Pᶜ ∪ Q)) = c.pr ((Pᶜ ∪ Q) ∩ I) := by rw [Finset.inter_comm]
    have h4 : c.pr (Iᶜ ∩ (Pᶜ ∪ Q)) = c.pr ((Pᶜ ∪ Q) ∩ Iᶜ) := by rw [Finset.inter_comm]
    linarith
  -- `P ∧ Q ∧ ¬I` is null, so `Pr (P ∧ Q ∧ I) = Pr (P ∧ Q)`
  have hz : c.pr (Iᶜ ∩ (P ∩ Q)) = 0 := by
    refine le_antisymm ?_ (pr_nonneg c _)
    rw [← h0]
    exact pr_mono c (by intro x hx; simp at hx ⊢; tauto)
  have hu : c.pr (I ∩ (P ∩ Q)) = c.pr (P ∩ Q) := by
    have := pr_total c I (P ∩ Q); linarith
  -- `Pr ¬I = Pr (P ∧ ¬Q ∧ ¬I)`
  have e : (Pᶜ ∪ Q)ᶜ ∩ Iᶜ = P ∩ Qᶜ ∩ Iᶜ := by ext x; simp
  have hIc : c.pr Iᶜ = c.pr (P ∩ Qᶜ ∩ Iᶜ) := by
    have := pr_total c (Pᶜ ∪ Q) Iᶜ
    rw [e] at this; linarith
  have hI := pr_add_pr_compl c I
  have hPtot : c.pr P = c.pr (P ∩ Q) + c.pr (P ∩ Qᶜ) := by
    have := pr_total c Q P
    rwa [Finset.inter_comm Q P, Finset.inter_comm Qᶜ P] at this
  have hle : c.pr P ≤ 1 := by
    have := pr_mono c (Finset.subset_univ P); rwa [pr_univ] at this
  have hx4 : c.pr (P ∩ Qᶜ ∩ Iᶜ) ≤ c.pr (P ∩ Qᶜ) := pr_mono c Finset.inter_subset_left
  have hx4' : 0 ≤ c.pr (P ∩ Qᶜ ∩ Iᶜ) := pr_nonneg c _
  have hTI : c.pr I * c.pr P = c.pr (P ∩ Q) := by
    rw [hT]; exact cond_mul_pr c Q P
  have eg : P ∩ ((Q ∩ I) ∪ (Qᶜ ∩ Iᶜ)) = (I ∩ (P ∩ Q)) ∪ (P ∩ Qᶜ ∩ Iᶜ) := by
    ext x; simp; tauto
  have dj : Disjoint (I ∩ (P ∩ Q)) (P ∩ Qᶜ ∩ Iᶜ) := by
    rw [Finset.disjoint_left]; intro x; simp; tauto
  rw [eg, pr_union_of_disjoint c dj, hu]
  generalize c.pr (P ∩ Q) = u at *
  generalize c.pr (P ∩ Qᶜ) = v at *
  generalize c.pr (P ∩ Qᶜ ∩ Iᶜ) = x at *
  have hpI : c.pr I = 1 - x := by linarith
  rw [hpI, hPtot] at hTI
  have h1 : v = x * (u + v) := by linarith
  have h2 : v ≤ x := by
    rw [hPtot] at hle
    nlinarith [mul_nonneg hx4' (sub_nonneg.2 hle)]
  have h3 : v = x := le_antisymm h2 hx4 |>.symm ▸ rfl
  have hxpos : 0 < x := h3 ▸ hp2
  have h4 : u + v = 1 := by
    have : x * (u + v) = x * 1 := by rw [← h1, h3, mul_one]
    exact mul_left_cancel₀ hxpos.ne' this
  linarith

/-- Milne 2003, in Fitelson's C4 form (R3 without the `¬Q` instance): positivity, the Thesis for
`P → Q` and the Resilient Equation under `P ⊃ Q` give C4. This is the simplest form of the
Resilient triviality result; `fitelson_three_instances` is the same result with the redundant
`¬Q` instance kept. -/
theorem milne_collapse (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) (hT : Thesis c imp P Q)
    (hX : Resilient c imp P Q (Pᶜ ∪ Q)) : C4 c imp P Q := by
  obtain ⟨hp1, hp2⟩ := hpos
  have hPpos : 0 < c.pr P := lt_of_lt_of_le hp1 (pr_mono c Finset.inter_subset_left)
  have e : P ∩ (Pᶜ ∪ Q) = P ∩ Q := by ext x; simp; tauto
  have hg : 0 < c.pr (P ∩ (Pᶜ ∪ Q)) := by rwa [e]
  refine fitelson_core c P Q (imp P Q) hp1 hp2 (hT hPpos) ?_
  rw [hX hg, e]
  exact cond_eq_one_of_subset c hp1 Finset.inter_subset_right

@[deprecated (since := "2026-11-22")] alias fitelson_without_res_notq := milne_collapse

/-- R3 (Fitelson 2015, three instances), kept as published: `Pr(P ∧ Q) > 0`, `Pr(P ∧ ¬Q) > 0`,
the Thesis for `P → Q`, and the Resilient Equation under `¬Q` and under `P ⊃ Q` give C4. The
`¬Q` instance is redundant, see `milne_collapse`. -/
theorem fitelson_three_instances (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) (hT : Thesis c imp P Q)
    (_hRQ : Resilient c imp P Q Qᶜ) (hX : Resilient c imp P Q (Pᶜ ∪ Q)) :
    C4 c imp P Q :=
  milne_collapse c imp P Q hpos hT hX

/-- R2 (Fitelson 2015): given positivity, the Resilient Equation holds under every `X`
iff C4 holds. -/
theorem fitelson_triviality (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) :
    (∀ X, Resilient c imp P Q X) ↔ C4 c imp P Q := by
  constructor
  · intro h
    obtain ⟨hp1, hp2⟩ := hpos
    have hPpos : 0 < c.pr P := lt_of_lt_of_le hp1 (pr_mono c Finset.inter_subset_left)
    have hT : Thesis c imp P Q := by
      intro hP
      have := h Finset.univ (by simpa using hP)
      simpa [Credence.cond, pr_univ] using this
    exact milne_collapse c imp P Q ⟨hp1, hp2⟩ hT (h _)
  · intro h X hg
    unfold C4 at h
    have key : ∀ (S A B : Finset Ω), c.pr S = 1 → S ∩ A = S ∩ B → c.pr A = c.pr B :=
      fun S A B hS hAB => by
        rw [← pr_inter_of_pr_one c S A hS, ← pr_inter_of_pr_one c S B hS, hAB]
    generalize imp P Q = I at *
    generalize hS : P ∩ ((Q ∩ I) ∪ (Qᶜ ∩ Iᶜ)) = S at h
    have hmem : ∀ x, x ∈ S ↔ x ∈ P ∧ ((x ∈ Q ∧ x ∈ I) ∨ (x ∉ Q ∧ x ∉ I)) := by
      intro x; rw [← hS]; simp
    have n1 : c.pr (X ∩ I) = c.pr (X ∩ Q) :=
      key S _ _ h (by ext x; have := hmem x; simp; tauto)
    have n2 : c.pr (P ∩ X ∩ Q) = c.pr (X ∩ Q) :=
      key S _ _ h (by ext x; have := hmem x; simp; tauto)
    have n3 : c.pr (P ∩ X) = c.pr X :=
      key S _ _ h (by ext x; have := hmem x; simp; tauto)
    unfold Credence.cond
    rw [n1, n2, n3]

/-- R4 (maximality of Fitelson's pair): positivity, the Thesis and the Resilient Equation under
`P ⊃ Q` give the Resilient Equation under every `X`. -/
theorem fitelson_maximality (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) (hT : Thesis c imp P Q)
    (hX : Resilient c imp P Q (Pᶜ ∪ Q)) : ∀ X, Resilient c imp P Q X :=
  (fitelson_triviality c imp P Q hpos).2 (milne_collapse c imp P Q hpos hT hX)

/-- R5 (Fitelson 2015): given the Thesis for all antecedents and consequents, for fixed `P`, `Q`,
PIE for every `(X, P, Q)` with `0 < Pr (X ∧ P)` is equivalent to the Resilient Equation for
`P → Q` under every `X`. -/
theorem fitelson_ie_iff_resilient (c : Credence Ω) (imp : Conditional Ω)
    (hT : ∀ A B, Thesis c imp A B) (P Q : Finset Ω) :
    (∀ X, 0 < c.pr (X ∩ P) → PIE c imp X P Q) ↔ (∀ X, Resilient c imp P Q X) := by
  constructor
  · intro h X hg
    rw [Finset.inter_comm] at hg
    have hX : 0 < c.pr X := lt_of_lt_of_le hg (pr_mono c Finset.inter_subset_left)
    have e1 := hT X (imp P Q) hX
    have e2 := hT (X ∩ P) Q hg
    have e3 := h X hg
    unfold PIE at e3
    rw [Finset.inter_comm P X, ← e1, ← e2, e3]
  · intro h X hg
    have hX : 0 < c.pr X := lt_of_lt_of_le hg (pr_mono c Finset.inter_subset_left)
    have e1 := hT X (imp P Q) hX
    have e2 := hT (X ∩ P) Q hg
    have e3 := h X (by rwa [Finset.inter_comm])
    unfold PIE
    rw [e1, e2, Finset.inter_comm X P]
    rw [e3]

/-- The per-instance form of R5 (the step is Fitelson 2015's): if `0 < Pr (X ∧ P)` and the Thesis
holds for `(X, P → Q)` and for `(X ∧ P, Q)`, then PIE for `(X, P, Q)` is equivalent to the
Resilient Equation for `P → Q` under `X`. -/
theorem pie_iff_resilient (c : Credence Ω) (imp : Conditional Ω) (P Q X : Finset Ω)
    (hg : 0 < c.pr (X ∩ P)) (h1 : Thesis c imp X (imp P Q)) (h2 : Thesis c imp (X ∩ P) Q) :
    PIE c imp X P Q ↔ Resilient c imp P Q X := by
  have hX : 0 < c.pr X := lt_of_lt_of_le hg (pr_mono c Finset.inter_subset_left)
  have e1 := h1 hX
  have e2 := h2 hg
  constructor
  · intro h _
    unfold PIE at h
    rw [Finset.inter_comm P X, ← e1, ← e2, h]
  · intro h
    have e3 := h (by rwa [Finset.inter_comm])
    unfold PIE
    rw [e1, e2, e3, Finset.inter_comm P X]

end Triviality
