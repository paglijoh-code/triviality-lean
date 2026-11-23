/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Countermodels.Fin4

/-!
# Countermodels for Khoo and Mandelkern's triviality result

Negative controls for `Triviality.km_probabilistic_triviality` (R7): dropping either positivity
hypothesis (`km_drop_pos1`, `km_drop_pos2`) or any single one of the seven premises
(`km_tight_drop_*`, K5) admits a model.

## Main results

* `Triviality.km_drop_pos1`, `Triviality.km_drop_pos2`: R7 needs both positivity hypotheses.
* `Triviality.km_tight_drop_a`, `_pie1`, `_pie2`, `_bi`, `_bii`, `_ci`, `_cii`: K5, each premise
  of R7 is needed.

## References

* Khoo and Mandelkern, "Triviality results and the relationship between logical and natural
  languages", Mind 2019.
-/

open Finset

namespace Triviality

/-- K5 (drop a): without the Thesis for `p > q`, a countermodel exists. Here `p > q := q`. -/
theorem km_tight_drop_a :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp q p q ∧ PIE c imp qᶜ p q ∧
      Thesis c imp (q ∩ p) q ∧ Thesis c imp (qᶜ ∩ p) q ∧
      Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨M1, tbl {0, 2} Finset.univ ∅ Finset.univ ∅, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
  · unfold Positive; norm_num [pr_fin4, M1, mk4]
  · norm_num [pr_fin4, Credence.cond, M1, mk4]
  · refine (pie1_iff ..).2 ?_; norm_num [pr_fin4, M1, mk4]
  · refine (pie2_iff ..).2 ?_; norm_num [pr_fin4, M1, mk4]
  · refine (thesis_bi_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M1, mk4]
  · refine (thesis_bii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M1, mk4]
  · refine (thesis_ci_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M1, mk4]
  · refine (thesis_cii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M1, mk4]

/-- K5 (drop PIE for `(q, p, q)`): a countermodel exists. -/
theorem km_tight_drop_pie1 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp qᶜ p q ∧
      Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧ Thesis c imp (qᶜ ∩ p) q ∧
      Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨M2, tbl {2} Finset.univ ∅ {1, 2} ∅, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, M2, mk4]
  · norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (pie2_iff ..).2 ?_; norm_num [pr_fin4, M2, mk4]
  · refine (thesis_a_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_bi_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_bii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_ci_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_cii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]

/-- K5 (drop PIE for `(¬q, p, q)`): a countermodel exists. -/
theorem km_tight_drop_pie2 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp q p q ∧
      Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧ Thesis c imp (qᶜ ∩ p) q ∧
      Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨M3, tbl {0, 1, 2} Finset.univ ∅ Finset.univ {0}, {0, 1}, {0, 2},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, M3, mk4]
  · norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (pie1_iff ..).2 ?_; norm_num [pr_fin4, M3, mk4]
  · refine (thesis_a_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_bi_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_bii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_ci_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_cii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]

/-- K5 (drop Thesis for `(q ∧ p) > q`): a countermodel exists. -/
theorem km_tight_drop_bi :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp q p q ∧ PIE c imp qᶜ p q ∧
      Thesis c imp p q ∧ Thesis c imp (qᶜ ∩ p) q ∧
      Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨M2, tbl {2} {1, 2} ∅ {1, 2} ∅, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, M2, mk4]
  · norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (pie1_iff ..).2 ?_; norm_num [pr_fin4, M2, mk4]
  · refine (pie2_iff ..).2 ?_; norm_num [pr_fin4, M2, mk4]
  · refine (thesis_a_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_bii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_ci_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_cii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]

/-- K5 (drop Thesis for `(¬q ∧ p) > q`): a countermodel exists. -/
theorem km_tight_drop_bii :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp q p q ∧ PIE c imp qᶜ p q ∧
      Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧
      Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨M3, tbl {0, 1, 2} Finset.univ {0} Finset.univ {0}, {0, 1}, {0, 2},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, M3, mk4]
  · norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (pie1_iff ..).2 ?_; norm_num [pr_fin4, M3, mk4]
  · refine (pie2_iff ..).2 ?_; norm_num [pr_fin4, M3, mk4]
  · refine (thesis_a_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_bi_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_ci_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_cii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]

/-- K5 (drop Thesis for `q > (p > q)`): a countermodel exists. -/
theorem km_tight_drop_ci :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp q p q ∧ PIE c imp qᶜ p q ∧
      Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧ Thesis c imp (qᶜ ∩ p) q ∧
      Thesis c imp qᶜ (imp p q) := by
  refine ⟨M2, tbl {2} Finset.univ ∅ Finset.univ ∅, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, M2, mk4]
  · norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (pie1_iff ..).2 ?_; norm_num [pr_fin4, M2, mk4]
  · refine (pie2_iff ..).2 ?_; norm_num [pr_fin4, M2, mk4]
  · refine (thesis_a_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_bi_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_bii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]
  · refine (thesis_cii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M2, mk4]

/-- K5 (drop Thesis for `¬q > (p > q)`): a countermodel exists. -/
theorem km_tight_drop_cii :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      Positive c p q ∧ c.cond q p ≠ c.pr q ∧ PIE c imp q p q ∧ PIE c imp qᶜ p q ∧
      Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧ Thesis c imp (qᶜ ∩ p) q ∧
      Thesis c imp q (imp p q) := by
  refine ⟨M3, tbl {0, 1, 2} Finset.univ ∅ Finset.univ ∅, {0, 1}, {0, 2},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Positive; norm_num [pr_fin4, M3, mk4]
  · norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (pie1_iff ..).2 ?_; norm_num [pr_fin4, M3, mk4]
  · refine (pie2_iff ..).2 ?_; norm_num [pr_fin4, M3, mk4]
  · refine (thesis_a_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_bi_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_bii_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]
  · refine (thesis_ci_iff ..).2 fun _ => ?_; norm_num [pr_fin4, Credence.cond, M3, mk4]

/-- K5 control (R7): dropping `Pr(p ∧ q) > 0`, with `Pr(p ∧ ¬q) > 0`, `Pr(q | p) ≠ Pr(q)` and all
seven other premises, does not give a contradiction. Weights `(0, 1/2, 1/2, 0)`, `p > q := ∅`. -/
theorem km_drop_pos1 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      c.pr (p ∩ q) = 0 ∧ 0 < c.pr (p ∩ qᶜ) ∧ c.cond q p ≠ c.pr q ∧
      PIE c imp q p q ∧ PIE c imp qᶜ p q ∧ Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧
      Thesis c imp (qᶜ ∩ p) q ∧ Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨F1, fun _ _ => ∅, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [PIE, Thesis, Credence.cond, pr_fin4, F1, mk4]

/-- K5 control (R7): dropping `Pr(p ∧ ¬q) > 0`, with `Pr(p ∧ q) > 0`, `Pr(q | p) ≠ Pr(q)` and all
seven other premises, does not give a contradiction. Weights `(1/2, 0, 1/4, 1/4)`, `p > q := ⊤`. -/
theorem km_drop_pos2 :
    ∃ (c : Credence (Fin 4)) (imp : Conditional (Fin 4)) (p q : Finset (Fin 4)),
      0 < c.pr (p ∩ q) ∧ c.pr (p ∩ qᶜ) = 0 ∧ c.cond q p ≠ c.pr q ∧
      PIE c imp q p q ∧ PIE c imp qᶜ p q ∧ Thesis c imp p q ∧ Thesis c imp (q ∩ p) q ∧
      Thesis c imp (qᶜ ∩ p) q ∧ Thesis c imp q (imp p q) ∧ Thesis c imp qᶜ (imp p q) := by
  refine ⟨D4, fun _ _ => Finset.univ, {0, 1}, {0, 2}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [PIE, Thesis, Credence.cond, pr_fin4, D4, mk4]

end Triviality
