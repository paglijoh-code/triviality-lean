/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Countermodels.Fin4

/-!
# Countermodels for Fitelson's triviality results

Negative controls for `Triviality.milne_collapse` and `Triviality.fitelson_three_instances` (R3),
`Triviality.fitelson_triviality` (R2) and `Triviality.fitelson_ie_iff_resilient` (R5).

## Main results

* `Triviality.fitelson3_drop_pos1`, `fitelson3_drop_pos2`, `fitelson3_drop_thesis`,
  `fitelson3_drop_res_matimp`: R3 controls.
* `Triviality.fitelson_triviality_drop_pos1`, `fitelson_triviality_drop_pos2`: R2 controls.
* `Triviality.fitelson_ie_drop_thesis`: R5 control.

## References

* Fitelson, "The strongest possible Lewisian triviality result", Thought 2015.
-/

open Finset

namespace Triviality

/-- R3 control: dropping `Pr(P ∧ Q) > 0`. `P → Q := ∅`. -/
theorem fitelson3_drop_pos1 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      0 < c.pr (P ∩ Qᶜ) ∧ Thesis c imp P Q ∧ Resilient c imp P Q Qᶜ ∧
      Resilient c imp P Q (Pᶜ ∪ Q) ∧ ¬ C4 c imp P Q := by
  refine ⟨F1, fun _ _ => ∅, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pr_fin4, F1, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, F1, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, F1, mk4]
  · rw [fin4_pc_q]; norm_num [Resilient, pr_fin4, Credence.cond, F1, mk4]
  · norm_num [C4, pr_fin4, F1, mk4]

/-- R3 control: dropping `Pr(P ∧ ¬Q) > 0`. `P → Q := univ`. -/
theorem fitelson3_drop_pos2 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      0 < c.pr (P ∩ Q) ∧ Thesis c imp P Q ∧ Resilient c imp P Q Qᶜ ∧
      Resilient c imp P Q (Pᶜ ∪ Q) ∧ ¬ C4 c imp P Q := by
  refine ⟨L2, fun _ _ => Finset.univ, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pr_fin4, L2, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, L2, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L2, mk4]
  · rw [fin4_pc_q]; norm_num [Resilient, pr_fin4, Credence.cond, L2, mk4]
  · norm_num [C4, pr_fin4, L2, mk4]

/-- R3 control: dropping the Thesis. `P → Q := Q`. -/
theorem fitelson3_drop_thesis :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      Positive c P Q ∧ Resilient c imp P Q Qᶜ ∧
      Resilient c imp P Q (Pᶜ ∪ Q) ∧ ¬ C4 c imp P Q := by
  refine ⟨L1, fun _ _ => {0, 2}, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, L1, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L1, mk4]
  · rw [fin4_pc_q]; norm_num [Resilient, pr_fin4, Credence.cond, L1, mk4]
  · norm_num [C4, pr_fin4, L1, mk4]

/-- R3 control: dropping the Resilient Equation under `P ⊃ Q`. `P → Q := {2}`. -/
theorem fitelson3_drop_res_matimp :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      Positive c P Q ∧ Thesis c imp P Q ∧ Resilient c imp P Q Qᶜ ∧ ¬ C4 c imp P Q := by
  refine ⟨L3, fun _ _ => {2}, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, L3, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, L3, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L3, mk4]
  · norm_num [C4, pr_fin4, L3, mk4]

/-- R2 control: dropping `Pr(P ∧ Q) > 0`. The Resilient Equation holds under every `X` but C4
fails (`P → Q := ∅`, weights `(0, 1/2, 1/2, 0)`). -/
theorem fitelson_triviality_drop_pos1 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      0 < c.pr (P ∩ Qᶜ) ∧ (∀ X, Resilient c imp P Q X) ∧ ¬ C4 c imp P Q := by
  refine ⟨F1, fun _ _ => ∅, {0, 1}, {0, 2}, ?_, ?_, ?_⟩
  · norm_num [pr_fin4, F1, mk4]
  · intro X _
    have key : ∀ ω : Fin 4, ω ∈ ({0, 1} : Finset (Fin 4)) → ω ∈ ({0, 2} : Finset (Fin 4)) →
        ω = 0 := by decide
    have hz : F1.pr ({0, 1} ∩ X ∩ {0, 2}) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      rw [Finset.mem_inter, Finset.mem_inter] at hω
      rw [key ω hω.1.1 hω.2]
      simp [F1, mk4]
    unfold Credence.cond
    rw [hz]
    simp [Credence.pr]
  · norm_num [C4, pr_fin4, F1, mk4]

/-- R2 control: dropping `Pr(P ∧ ¬Q) > 0`. The Resilient Equation holds under every `X` but C4
fails (`P → Q := univ`, weights `(1/2, 0, 1/2, 0)`). -/
theorem fitelson_triviality_drop_pos2 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      0 < c.pr (P ∩ Q) ∧ (∀ X, Resilient c imp P Q X) ∧ ¬ C4 c imp P Q := by
  refine ⟨L2, fun _ _ => Finset.univ, {0, 1}, {0, 2}, ?_, ?_, ?_⟩
  · norm_num [pr_fin4, L2, mk4]
  · intro X hg
    have hX : 0 < L2.pr X := lt_of_lt_of_le hg (pr_mono L2 Finset.inter_subset_right)
    have key : ∀ ω : Fin 4, ω ∈ ({0, 1} : Finset (Fin 4)) → ω ∉ ({0, 2} : Finset (Fin 4)) →
        ω = 1 := by decide
    have hz : L2.pr ({0, 2}ᶜ ∩ ({0, 1} ∩ X)) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_compl] at hω
      rw [key ω hω.2.1 hω.1]
      simp [L2, mk4]
    have h1 := pr_total L2 {0, 2} ({0, 1} ∩ X)
    rw [hz, add_zero] at h1
    have h2 : {0, 2} ∩ ({0, 1} ∩ X) = {0, 1} ∩ X ∩ {0, 2} := by
      rw [Finset.inter_comm]
    unfold Credence.cond
    rw [Finset.inter_univ, ← h2, ← h1, div_self hX.ne', div_self hg.ne']
  · norm_num [C4, pr_fin4, L2, mk4]

/-- R5 control: without the Thesis, PIE for all `(X, P, Q)` does not give the Resilient
Equation. `imp` is constantly `∅`, which satisfies PIE trivially. -/
theorem fitelson_ie_drop_thesis :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      (∀ X, 0 < c.pr (X ∩ P) → PIE c imp X P Q) ∧ ¬ ∀ X, Resilient c imp P Q X := by
  refine ⟨L1, fun _ _ => ∅, {0}, {0}, ?_, ?_⟩
  · intro X _
    simp [PIE, Credence.pr]
  · intro h
    have := h Finset.univ (by norm_num [pr_fin4, L1, mk4])
    norm_num [Credence.cond, pr_fin4, L1, mk4] at this

end Triviality
