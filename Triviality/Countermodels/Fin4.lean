/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Probability

/-!
# Models on `Fin 4`

Implementation details shared by the countermodel files: the credence constructor `mk4`, the
expansion `pr_fin4`, the lookup conditional `tbl` keyed on the antecedent, and the fixed weight
vectors used by the negative controls.

Worlds are `0 = p∧q`, `1 = p∧¬q`, `2 = ¬p∧q`, `3 = ¬p∧¬q`; `p = {0,1}`, `q = {0,2}`.

## Main definitions

* `Triviality.mk4`: a credence on `Fin 4` from four weights.
* `Triviality.tbl`: the lookup conditional keyed on the antecedent.
* `Triviality.F1`, `L1`…`L4`, `M1`…`M3`, `D4`: weight vectors.

## References

* Khoo and Mandelkern, "Triviality results and the relationship between logical and natural
  languages", Mind 2019.
-/

open Finset

namespace Triviality

/-! ## Concrete models on `Fin 4`

Worlds `0 = p∧q`, `1 = p∧¬q`, `2 = ¬p∧q`, `3 = ¬p∧¬q`; `p = {0,1}`, `q = {0,2}`.
The conditional only looks at its antecedent, which is enough since the five antecedents
`p`, `q ∩ p = {0}`, `qᶜ ∩ p = {1}`, `q`, `qᶜ` are pairwise distinct. -/

/-- A credence on `Fin 4` from four weights. -/
def mk4 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : a + b + c + d = 1) : Credence (Fin 4) where
  w := ![a, b, c, d]
  nonneg := by intro ω; fin_cases ω <;> simpa
  sum_one := by simpa [Fin.sum_univ_four] using hs

/-- `pr` as a sum of indicator-weighted terms over `Fin 4`. -/
theorem pr_fin4 (c : Credence (Fin 4)) (A : Finset (Fin 4)) :
    c.pr A = (if (0 : Fin 4) ∈ A then c.w 0 else 0) + (if (1 : Fin 4) ∈ A then c.w 1 else 0)
      + (if (2 : Fin 4) ∈ A then c.w 2 else 0) + (if (3 : Fin 4) ∈ A then c.w 3 else 0) := by
  have h : ∑ ω, (if ω ∈ A then c.w ω else 0) = ∑ ω ∈ A, c.w ω := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  unfold Credence.pr
  rw [← h, Fin.sum_univ_four]

/-- The lookup conditional keyed on the antecedent. -/
def tbl (X Y0 Y1 Z W : Finset (Fin 4)) : Conditional (Fin 4) := fun A _ =>
  if A = {0, 1} then X else if A = {0} then Y0 else if A = {1} then Y1
  else if A = {0, 2} then Z else if A = {1, 3} then W else ∅

section tbl_lemmas

variable (X Y0 Y1 Z W B : Finset (Fin 4))

theorem tbl_p : tbl X Y0 Y1 Z W {0, 1} B = X := by
  dsimp only [tbl]; rw [if_pos rfl]

theorem tbl_0 : tbl X Y0 Y1 Z W {0} B = Y0 := by
  dsimp only [tbl]; rw [if_neg (by decide), if_pos rfl]

theorem tbl_1 : tbl X Y0 Y1 Z W {1} B = Y1 := by
  dsimp only [tbl]; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem tbl_q : tbl X Y0 Y1 Z W {0, 2} B = Z := by
  dsimp only [tbl]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem tbl_qc : tbl X Y0 Y1 Z W {1, 3} B = W := by
  dsimp only [tbl]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

theorem fin4_qc : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
theorem fin4_qp : ({0, 2} : Finset (Fin 4)) ∩ {0, 1} = {0} := by decide
theorem fin4_qcp' : ({1, 3} : Finset (Fin 4)) ∩ {0, 1} = {1} := by decide
theorem fin4_qcp : ({0, 2} : Finset (Fin 4))ᶜ ∩ {0, 1} = {1} := by decide

variable (c : Credence (Fin 4))

theorem pie1_iff : PIE c (tbl X Y0 Y1 Z W) {0, 2} {0, 1} {0, 2} ↔ c.pr Z = c.pr Y0 := by
  simp only [PIE, tbl_p, tbl_q, fin4_qp, tbl_0]

theorem pie2_iff :
    PIE c (tbl X Y0 Y1 Z W) ({0, 2} : Finset (Fin 4))ᶜ {0, 1} {0, 2} ↔ c.pr W = c.pr Y1 := by
  simp only [PIE, tbl_p, fin4_qc, fin4_qcp', tbl_qc, tbl_1]

theorem thesis_a_iff :
    Thesis c (tbl X Y0 Y1 Z W) {0, 1} {0, 2} ↔
    (0 < c.pr {0, 1} → c.pr X = c.cond {0, 2} {0, 1}) := by
  simp only [Thesis, tbl_p]

theorem thesis_bi_iff : Thesis c (tbl X Y0 Y1 Z W) ({0, 2} ∩ {0, 1}) {0, 2} ↔
    (0 < c.pr ({0, 2} ∩ {0, 1}) → c.pr Y0 = c.cond {0, 2} ({0, 2} ∩ {0, 1})) := by
  simp only [Thesis, fin4_qp, tbl_0]

theorem thesis_bii_iff : Thesis c (tbl X Y0 Y1 Z W) (({0, 2} : Finset (Fin 4))ᶜ ∩ {0, 1}) {0, 2} ↔
    (0 < c.pr (({0, 2} : Finset (Fin 4))ᶜ ∩ {0, 1}) →
      c.pr Y1 = c.cond {0, 2} (({0, 2} : Finset (Fin 4))ᶜ ∩ {0, 1})) := by
  simp only [Thesis, fin4_qcp, tbl_1]

theorem thesis_ci_iff :
    Thesis c (tbl X Y0 Y1 Z W) {0, 2} (tbl X Y0 Y1 Z W {0, 1} {0, 2}) ↔
    (0 < c.pr {0, 2} → c.pr Z = c.cond X {0, 2}) := by
  simp only [Thesis, tbl_p, tbl_q]

theorem thesis_cii_iff :
    Thesis c (tbl X Y0 Y1 Z W) ({0, 2} : Finset (Fin 4))ᶜ (tbl X Y0 Y1 Z W {0, 1} {0, 2}) ↔
    (0 < c.pr ({0, 2} : Finset (Fin 4))ᶜ → c.pr W = c.cond X ({0, 2} : Finset (Fin 4))ᶜ) := by
  simp only [Thesis, tbl_p, fin4_qc, tbl_qc]

end tbl_lemmas

/-- Weights `(2, 1, 1, 4) / 8`: `Pr(q | p) = 2/3`, `Pr q = 3/8`. -/
noncomputable def M1 : Credence (Fin 4) :=
  mk4 (2 / 8) (1 / 8) (1 / 8) (4 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(1, 2, 2, 1) / 6`: `Pr(q | p) = 1/3`, `Pr q = 1/2`. -/
noncomputable def M2 : Credence (Fin 4) :=
  mk4 (1 / 6) (2 / 6) (2 / 6) (1 / 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(2, 1, 1, 2) / 6`: `Pr(q | p) = 2/3`, `Pr q = 1/2`. -/
noncomputable def M3 : Credence (Fin 4) :=
  mk4 (2 / 6) (1 / 6) (1 / 6) (2 / 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(1/3, 1/3, 1/3, 0)`, used for the Lewis control with `Pr(P ∧ Q) = 0`. -/
noncomputable def L1 : Credence (Fin 4) :=
  mk4 (1 / 3) (1 / 3) (1 / 3) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(1/2, 0, 1/2, 0)`, used for the Lewis control with `Pr(P ∧ ¬Q) = 0`. -/
noncomputable def L2 : Credence (Fin 4) :=
  mk4 (1 / 2) 0 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(1/4, 1/4, 1/2, 0)`. -/
noncomputable def L3 : Credence (Fin 4) :=
  mk4 (1 / 4) (1 / 4) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(1/2, 1/6, 1/12, 1/4)`. -/
noncomputable def L4 : Credence (Fin 4) :=
  mk4 (1 / 2) (1 / 6) (1 / 12) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Weights `(0, 1/2, 1/2, 0)`. -/
noncomputable def F1 : Credence (Fin 4) :=
  mk4 0 (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- A credence on `Fin 4` with weights `(1/2, 0, 1/4, 1/4)`. -/
noncomputable def D4 : Credence (Fin 4) :=
  mk4 (1 / 2) 0 (1 / 4) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Implementation detail: `({0, 1}ᶜ ∪ {0, 2}) = {0, 2, 3}` on `Fin 4`. -/
theorem fin4_pc_q : (({0, 1} : Finset (Fin 4))ᶜ ∪ {0, 2}) = {0, 2, 3} := by decide

end Triviality
