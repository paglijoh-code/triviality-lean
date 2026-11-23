/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Countermodels.Fin4

/-!
# Countermodels for Lewis's triviality result

Negative controls for `Triviality.lewis_1976` (R1): dropping any one hypothesis admits a model in
which `Pr (Q | P) ≠ Pr Q`.

## Main results

* `Triviality.lewis_drop_pos1`, `lewis_drop_pos2`: R1 needs both positivity hypotheses.
* `Triviality.lewis_drop_thesis`, `lewis_drop_res_q`, `lewis_drop_res_notq`: R1 needs the Thesis
  and both Resilient instances.

## References

* Lewis, "Probabilities of conditionals and conditional probabilities", Phil. Review 1976.
-/

open Finset

namespace Triviality

/-- Lewis control (R1 baseline): dropping `Pr(P ∧ Q) > 0` admits a countermodel, even with both
Resilient premises. -/
theorem lewis_drop_pos1 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      0 < c.pr (P ∩ Qᶜ) ∧ Thesis c imp P Q ∧ Resilient c imp P Q Q ∧
      Resilient c imp P Q Qᶜ ∧ c.cond Q P ≠ c.pr Q := by
  refine ⟨L1, fun _ _ => ∅, {0}, {1}, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pr_fin4, L1, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, L1, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L1, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L1, mk4]
  · norm_num [pr_fin4, Credence.cond, L1, mk4]

/-- Lewis control (R1 baseline): dropping `Pr(P ∧ ¬Q) > 0` admits a countermodel. The Resilient
Equation for `¬Q` holds vacuously, because its guard `0 < Pr(P ∧ ¬Q)` fails. -/
theorem lewis_drop_pos2 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      0 < c.pr (P ∩ Q) ∧ c.pr (P ∩ Qᶜ) = 0 ∧ Thesis c imp P Q ∧ Resilient c imp P Q Q ∧
      Resilient c imp P Q Qᶜ ∧ c.cond Q P ≠ c.pr Q := by
  refine ⟨L2, fun _ _ => Finset.univ, {0}, {0}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pr_fin4, L2, mk4]
  · norm_num [pr_fin4, L2, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, L2, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L2, mk4]
  · intro h
    norm_num [pr_fin4, L2, mk4] at h
  · norm_num [pr_fin4, Credence.cond, L2, mk4]

/-- Lewis control (R1 baseline): dropping the Thesis admits a countermodel (`P → Q := Q`). -/
theorem lewis_drop_thesis :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      Positive c P Q ∧ Resilient c imp P Q Q ∧ Resilient c imp P Q Qᶜ ∧
      c.cond Q P ≠ c.pr Q := by
  refine ⟨L1, fun _ _ => {0, 2}, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, L1, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L1, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L1, mk4]
  · norm_num [pr_fin4, Credence.cond, L1, mk4]

/-- Lewis control (R1 baseline): dropping the Resilient Equation under `Q` admits a
countermodel (`P → Q := {2}`). -/
theorem lewis_drop_res_q :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      Positive c P Q ∧ Thesis c imp P Q ∧ Resilient c imp P Q Qᶜ ∧ c.cond Q P ≠ c.pr Q := by
  refine ⟨L3, fun _ _ => {2}, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, L3, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, L3, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L3, mk4]
  · norm_num [pr_fin4, Credence.cond, L3, mk4]

/-- Lewis control (R1 baseline): dropping the Resilient Equation under `¬Q` admits a
countermodel (`P → Q := {0,1,2}`). -/
theorem lewis_drop_res_notq :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (P Q : Finset (Fin 4)),
      Positive c P Q ∧ Thesis c imp P Q ∧ Resilient c imp P Q Q ∧ c.cond Q P ≠ c.pr Q := by
  refine ⟨L4, fun _ _ => {0, 1, 2}, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, L4, mk4]
  · norm_num [Thesis, pr_fin4, Credence.cond, L4, mk4]
  · norm_num [Resilient, pr_fin4, Credence.cond, L4, mk4]
  · norm_num [pr_fin4, Credence.cond, L4, mk4]

end Triviality
