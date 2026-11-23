/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Fitelson

/-!
# The collapsing pairs: a general theorem (`pair_collapse`)

Over `P`, `Q` and `C = P → Q` there are eight cells, indexed `i = p + 2q + 4c`:
`0 = ¬P¬Q¬C`, `1 = P¬Q¬C`, `2 = ¬PQ¬C`, `3 = PQ¬C`, `4 = ¬P¬QC`, `5 = P¬QC`, `6 = ¬PQC`,
`7 = PQC`. With `w i` the weight of cell `i` and `x i` the weight of cell `i` inside `X`, the
Resilient Equation under `X` is `(x4+x5+x6+x7)(x1+x5) = (x3+x7)(x0+x1+x2+x3)`: the odds of `C`
inside `X` equal the odds of `Q` inside `P ∧ X`. C4 says `w0 = w2 = w3 = w4 = w5 = w6 = 0`.

## Main results

* `Triviality.pair_collapse`: the general theorem; it covers the 135 collapsing pairs of
  learning propositions `{X, Y}`.
* `Triviality.equation_matimp_collapse`: the simplest instance, `{⊤, P ⊃ Q}`.

Everything else in this file (the cell algebra, `kill_core`, `pair_num`, `pair_collapse_aux`) is
an implementation detail.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Implementation detail: `Pr S` as a sum over all worlds of an indicator (helper for the cell
lemmas). -/
theorem pr_eq_sum_ite (c : Credence Ω) (S : Finset Ω) :
    c.pr S = ∑ ω, if ω ∈ S then c.w ω else 0 := by
  unfold Credence.pr
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Implementation detail: cell 0 of the eight cells over `P`, `Q`, `C` (`¬P ∧ ¬Q ∧ ¬C`). -/
abbrev cell0 (P Q C : Finset Ω) : Finset Ω := Pᶜ ∩ Qᶜ ∩ Cᶜ
/-- Implementation detail: cell 1 (`P ∧ ¬Q ∧ ¬C`). -/
abbrev cell1 (P Q C : Finset Ω) : Finset Ω := P ∩ Qᶜ ∩ Cᶜ
/-- Implementation detail: cell 2 (`¬P ∧ Q ∧ ¬C`). -/
abbrev cell2 (P Q C : Finset Ω) : Finset Ω := Pᶜ ∩ Q ∩ Cᶜ
/-- Implementation detail: cell 3 (`P ∧ Q ∧ ¬C`). -/
abbrev cell3 (P Q C : Finset Ω) : Finset Ω := P ∩ Q ∩ Cᶜ
/-- Implementation detail: cell 4 (`¬P ∧ ¬Q ∧ C`). -/
abbrev cell4 (P Q C : Finset Ω) : Finset Ω := Pᶜ ∩ Qᶜ ∩ C
/-- Implementation detail: cell 5 (`P ∧ ¬Q ∧ C`). -/
abbrev cell5 (P Q C : Finset Ω) : Finset Ω := P ∩ Qᶜ ∩ C
/-- Implementation detail: cell 6 (`¬P ∧ Q ∧ C`). -/
abbrev cell6 (P Q C : Finset Ω) : Finset Ω := Pᶜ ∩ Q ∩ C
/-- Implementation detail: cell 7 (`P ∧ Q ∧ C`). -/
abbrev cell7 (P Q C : Finset Ω) : Finset Ω := P ∩ Q ∩ C

/-- Implementation detail: the probability of `A` is the sum of its weights in the eight cells. -/
theorem pr_cells (c : Credence Ω) (P Q C A : Finset Ω) :
    c.pr A = c.pr (cell0 P Q C ∩ A) + c.pr (cell1 P Q C ∩ A) + c.pr (cell2 P Q C ∩ A)
      + c.pr (cell3 P Q C ∩ A) + c.pr (cell4 P Q C ∩ A) + c.pr (cell5 P Q C ∩ A)
      + c.pr (cell6 P Q C ∩ A) + c.pr (cell7 P Q C ∩ A) := by
  simp only [pr_eq_sum_ite, cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hP : ω ∈ P <;> by_cases hQ : ω ∈ Q <;> by_cases hC : ω ∈ C <;>
    by_cases hA : ω ∈ A <;> simp [hP, hQ, hC, hA]

/-- Implementation detail: the weight of `A ∧ C` is the sum of its weights in cells 4 to 7 (helper
for `pair_collapse`). -/
theorem pr_inter_C (c : Credence Ω) (P Q C A : Finset Ω) :
    c.pr (A ∩ C) = c.pr (cell4 P Q C ∩ A) + c.pr (cell5 P Q C ∩ A) + c.pr (cell6 P Q C ∩ A)
      + c.pr (cell7 P Q C ∩ A) := by
  simp only [pr_eq_sum_ite, cell4, cell5, cell6, cell7]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hP : ω ∈ P <;> by_cases hQ : ω ∈ Q <;> by_cases hC : ω ∈ C <;>
    by_cases hA : ω ∈ A <;> simp [hP, hQ, hC, hA]

/-- Implementation detail: the weight of `P ∧ A` is the sum of its weights in the cells 1, 3, 5, 7
(helper for `pair_collapse`). -/
theorem pr_P_inter (c : Credence Ω) (P Q C A : Finset Ω) :
    c.pr (P ∩ A) = c.pr (cell1 P Q C ∩ A) + c.pr (cell3 P Q C ∩ A) + c.pr (cell5 P Q C ∩ A)
      + c.pr (cell7 P Q C ∩ A) := by
  simp only [pr_eq_sum_ite, cell1, cell3, cell5, cell7]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hP : ω ∈ P <;> by_cases hQ : ω ∈ Q <;> by_cases hC : ω ∈ C <;>
    by_cases hA : ω ∈ A <;> simp [hP, hQ, hC, hA]

/-- Implementation detail: the weight of `P ∧ A ∧ Q` is the sum of its weights in cells 3 and 7
(helper for `pair_collapse`). -/
theorem pr_PA_Q (c : Credence Ω) (P Q C A : Finset Ω) :
    c.pr (P ∩ A ∩ Q) = c.pr (cell3 P Q C ∩ A) + c.pr (cell7 P Q C ∩ A) := by
  simp only [pr_eq_sum_ite, cell3, cell7]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hP : ω ∈ P <;> by_cases hQ : ω ∈ Q <;> by_cases hC : ω ∈ C <;>
    by_cases hA : ω ∈ A <;> simp [hP, hQ, hC, hA]

/-- Implementation detail: the weight of `P ∧ A ∧ ¬Q` is the sum of its weights in cells 1 and 5
(helper for `pair_collapse`). -/
theorem pr_PA_nQ (c : Credence Ω) (P Q C A : Finset Ω) :
    c.pr (P ∩ A ∩ Qᶜ) = c.pr (cell1 P Q C ∩ A) + c.pr (cell5 P Q C ∩ A) := by
  simp only [pr_eq_sum_ite, cell1, cell5]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hP : ω ∈ P <;> by_cases hQ : ω ∈ Q <;> by_cases hC : ω ∈ C <;>
    by_cases hA : ω ∈ A <;> simp [hP, hQ, hC, hA]

/-- Implementation detail: the Resilient Equation under `X`, cross-multiplied. -/
theorem res_cross (c : Credence Ω) (imp : Conditional Ω) (P Q X : Finset Ω)
    (h : Resilient c imp P Q X) :
    c.pr (X ∩ imp P Q) * c.pr (P ∩ X) = c.pr (P ∩ X ∩ Q) * c.pr X := by
  by_cases hg : 0 < c.pr (P ∩ X)
  · have hX : 0 < c.pr X := lt_of_lt_of_le hg (pr_mono c Finset.inter_subset_right)
    have := h hg
    unfold Credence.cond at this
    exact (div_eq_div_iff hX.ne' hg.ne').1 this
  · have h0 : c.pr (P ∩ X) = 0 := le_antisymm (not_lt.1 hg) (pr_nonneg c _)
    have h1 : c.pr (P ∩ X ∩ Q) = 0 :=
      le_antisymm (h0 ▸ pr_mono c Finset.inter_subset_left) (pr_nonneg c _)
    rw [h0, h1]; ring

/-- Implementation detail: a set inside a null intersection has weight zero inside `X` (helper for
`pair_collapse`). -/
theorem pr_cell_zero (c : Credence Ω) {S T : Finset Ω} (X : Finset Ω) (hS : S ⊆ T)
    (h : X ∩ T = ∅) : c.pr (S ∩ X) = 0 := by
  have : S ∩ X = ∅ := Finset.subset_empty.1 fun x hx => by
    have h1 : x ∈ X ∩ T :=
      Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).2, hS (Finset.mem_inter.1 hx).1⟩
    rwa [h] at h1
  rw [this]; simp [Credence.pr]

/-- Implementation detail: numeric core, part 1: an `X` whose equation has no negative cross term
(`x3 = 0` and either
`x7 = 0` or `x0 = x2 = 0`), with `x1 + x5 > 0`, has `x4 + x5 + x6 = 0`. -/
theorem kill_core {x0 x1 x2 x3 x4 x5 x6 x7 : ℝ} (h0 : 0 ≤ x0) (h2 : 0 ≤ x2)
    (h4 : 0 ≤ x4) (h5 : 0 ≤ x5) (h6 : 0 ≤ x6) (h7 : 0 ≤ x7) (hn : 0 < x1 + x5)
    (EX : (x4 + x5 + x6 + x7) * (x1 + x3 + x5 + x7)
      = (x3 + x7) * (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7))
    (hk : (x3 = 0 ∧ x7 = 0) ∨ (x3 = 0 ∧ x0 = 0 ∧ x2 = 0)) : x4 + x5 + x6 = 0 := by
  have hs : 0 ≤ x4 + x5 + x6 := by linarith
  rcases hk with ⟨e3, e7⟩ | ⟨e3, e0, e2⟩
  · subst e3; subst e7
    have : (x4 + x5 + x6) * (x1 + x5) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hn.ne'
  · subst e3; subst e0; subst e2
    have key : (x4 + x5 + x6) * (x1 + x5) + x7 * x5 = 0 := by linarith
    have a1 : 0 ≤ (x4 + x5 + x6) * (x1 + x5) := mul_nonneg hs hn.le
    have a2 : 0 ≤ x7 * x5 := mul_nonneg h7 h5
    have : (x4 + x5 + x6) * (x1 + x5) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hn.ne'

/-- Implementation detail: numeric core, part 2: a `Y` with `y5 = 0` and either `y1 = 0` or `y4 =
y6 = 0`, with
`y3 + y7 > 0`, has `y0 + y2 + y3 = 0`. -/
theorem kill_core2 {y0 y1 y2 y3 y4 y5 y6 y7 : ℝ} (h0 : 0 ≤ y0) (h1 : 0 ≤ y1) (h2 : 0 ≤ y2)
    (h3 : 0 ≤ y3) (hm : 0 < y3 + y7)
    (EY : (y4 + y5 + y6 + y7) * (y1 + y3 + y5 + y7)
      = (y3 + y7) * (y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7))
    (hk : y5 = 0 ∧ (y1 = 0 ∨ (y4 = 0 ∧ y6 = 0))) : y0 + y2 + y3 = 0 := by
  obtain ⟨e5, hk⟩ := hk
  subst e5
  rcases hk with e1 | ⟨e4, e6⟩
  · subst e1
    have : (y3 + y7) * (y0 + y2 + y3) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hm.ne'
  · subst e4; subst e6
    have key : (y3 + y7) * (y0 + y2 + y3) + y3 * y1 = 0 := by linarith
    have a1 : 0 ≤ (y3 + y7) * (y0 + y2 + y3) := mul_nonneg hm.le (by linarith)
    have a2 : 0 ≤ y3 * y1 := mul_nonneg h3 h1
    have : (y3 + y7) * (y0 + y2 + y3) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hm.ne'

/-- Implementation detail: the numeric content of `pair_collapse`, over the eight cell weights `w`,
the weights `x` of
the cells inside `X` that are not forced equal to `w`, and likewise `y` for `Y`. -/
theorem pair_num {w0 w1 w2 w3 w4 w5 w6 w7 x0 x2 x3 x7 y1 y4 y5 y6 : ℝ}
    (nW0 : 0 ≤ w0) (nW2 : 0 ≤ w2) (nW3 : 0 ≤ w3) (nW4 : 0 ≤ w4)
    (nW5 : 0 ≤ w5) (nW6 : 0 ≤ w6)
    (nX0 : 0 ≤ x0) (nX2 : 0 ≤ x2) (nX3 : 0 ≤ x3) (nX7 : 0 ≤ x7)
    (nY1 : 0 ≤ y1) (nY4 : 0 ≤ y4) (nY5 : 0 ≤ y5) (nY6 : 0 ≤ y6)
    (lX0 : x0 ≤ w0) (lX2 : x2 ≤ w2) (lX3 : x3 ≤ w3)
    (lY4 : y4 ≤ w4) (lY5 : y5 ≤ w5) (lY6 : y6 ≤ w6)
    (hp1 : 0 < w3 + w7) (hp2 : 0 < w1 + w5)
    (EX : (w4 + w5 + w6 + x7) * (w1 + x3 + w5 + x7)
      = (x3 + x7) * (x0 + w1 + x2 + x3 + w4 + w5 + w6 + x7))
    (EY : (y4 + y5 + y6 + w7) * (y1 + w3 + y5 + w7)
      = (w3 + w7) * (w0 + y1 + w2 + w3 + y4 + y5 + y6 + w7))
    (hk : (x3 = 0 ∧ (x7 = 0 ∨ (x0 = 0 ∧ x2 = 0))) ∨
      (y5 = 0 ∧ (y1 = 0 ∨ (y4 = 0 ∧ y6 = 0)))) :
    w0 = 0 ∧ w2 = 0 ∧ w3 = 0 ∧ w4 = 0 ∧ w5 = 0 ∧ w6 = 0 := by
  have keyX : (x3 = 0 ∧ x7 = 0) ∨ (x3 = 0 ∧ x0 = 0 ∧ x2 = 0) → w4 = 0 ∧ w5 = 0 ∧ w6 = 0 := by
    intro h
    have := kill_core nX0 nX2 nW4 nW5 nW6 nX7 hp2 EX h
    refine ⟨by linarith, by linarith, by linarith⟩
  have keyY : y5 = 0 ∧ (y1 = 0 ∨ (y4 = 0 ∧ y6 = 0)) → w0 = 0 ∧ w2 = 0 ∧ w3 = 0 := by
    intro h
    have := kill_core2 nW0 nY1 nW2 nW3 hp1 EY h
    refine ⟨by linarith, by linarith, by linarith⟩
  rcases hk with ⟨k3, k7 | ⟨k0, k2⟩⟩ | ⟨k5, k1 | ⟨k4, k6⟩⟩
  · obtain ⟨h4, h5, h6⟩ := keyX (Or.inl ⟨k3, k7⟩)
    obtain ⟨h0, h2, h3⟩ := keyY ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
    exact ⟨h0, h2, h3, h4, h5, h6⟩
  · obtain ⟨h4, h5, h6⟩ := keyX (Or.inr ⟨k3, k0, k2⟩)
    obtain ⟨h0, h2, h3⟩ := keyY ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
    exact ⟨h0, h2, h3, h4, h5, h6⟩
  · obtain ⟨h0, h2, h3⟩ := keyY ⟨k5, Or.inl k1⟩
    obtain ⟨h4, h5, h6⟩ := keyX (Or.inr ⟨by linarith, by linarith, by linarith⟩)
    exact ⟨h0, h2, h3, h4, h5, h6⟩
  · obtain ⟨h0, h2, h3⟩ := keyY ⟨k5, Or.inr ⟨k4, k6⟩⟩
    obtain ⟨h4, h5, h6⟩ := keyX (Or.inr ⟨by linarith, by linarith, by linarith⟩)
    exact ⟨h0, h2, h3, h4, h5, h6⟩

/-- Implementation detail: the set-level form of `pair_collapse`, with the conditional abstracted
to a proposition `C`. -/
theorem pair_collapse_aux (c : Credence Ω) (P Q C X Y : Finset Ω)
    (hp1 : 0 < c.pr (P ∩ Q)) (hp2 : 0 < c.pr (P ∩ Qᶜ))
    (hEX : c.pr (X ∩ C) * c.pr (P ∩ X) = c.pr (P ∩ X ∩ Q) * c.pr X)
    (hEY : c.pr (Y ∩ C) * c.pr (P ∩ Y) = c.pr (P ∩ Y ∩ Q) * c.pr Y)
    (hX1 : P ∩ Qᶜ ⊆ X) (hX2 : Pᶜ ∩ C ⊆ X) (hY1 : P ∩ Q ⊆ Y) (hY2 : Pᶜ ∩ Cᶜ ⊆ Y)
    (hk : (X ∩ (P ∩ Q ∩ Cᶜ) = ∅ ∧ (X ∩ (P ∩ Q ∩ C) = ∅ ∨ X ∩ (Pᶜ ∩ Cᶜ) = ∅)) ∨
      (Y ∩ (P ∩ Qᶜ ∩ C) = ∅ ∧ (Y ∩ (P ∩ Qᶜ ∩ Cᶜ) = ∅ ∨ Y ∩ (Pᶜ ∩ C) = ∅))) :
    c.pr (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ))) = 1 := by
  -- cells contained in X or Y
  have sX1 : cell1 P Q C ⊆ X := fun x hx => hX1 (by simp only [mem_inter] at hx ⊢; tauto)
  have sX5 : cell5 P Q C ⊆ X := fun x hx => hX1 (by simp only [mem_inter, mem_compl] at hx ⊢; tauto)
  have sX4 : cell4 P Q C ⊆ X := fun x hx => hX2 (by simp only [mem_inter, mem_compl] at hx ⊢; tauto)
  have sX6 : cell6 P Q C ⊆ X := fun x hx => hX2 (by simp only [mem_inter, mem_compl] at hx ⊢; tauto)
  have sY3 : cell3 P Q C ⊆ Y := fun x hx => hY1 (by simp only [mem_inter, mem_compl] at hx ⊢; tauto)
  have sY7 : cell7 P Q C ⊆ Y := fun x hx => hY1 (by simp only [mem_inter] at hx ⊢; tauto)
  have sY0 : cell0 P Q C ⊆ Y := fun x hx => hY2 (by simp only [mem_inter, mem_compl] at hx ⊢; tauto)
  have sY2 : cell2 P Q C ⊆ Y := fun x hx => hY2 (by simp only [mem_inter, mem_compl] at hx ⊢; tauto)
  have eX1 : c.pr (cell1 P Q C ∩ X) = c.pr (cell1 P Q C) := by rw [Finset.inter_eq_left.2 sX1]
  have eX5 : c.pr (cell5 P Q C ∩ X) = c.pr (cell5 P Q C) := by rw [Finset.inter_eq_left.2 sX5]
  have eX4 : c.pr (cell4 P Q C ∩ X) = c.pr (cell4 P Q C) := by rw [Finset.inter_eq_left.2 sX4]
  have eX6 : c.pr (cell6 P Q C ∩ X) = c.pr (cell6 P Q C) := by rw [Finset.inter_eq_left.2 sX6]
  have eY3 : c.pr (cell3 P Q C ∩ Y) = c.pr (cell3 P Q C) := by rw [Finset.inter_eq_left.2 sY3]
  have eY7 : c.pr (cell7 P Q C ∩ Y) = c.pr (cell7 P Q C) := by rw [Finset.inter_eq_left.2 sY7]
  have eY0 : c.pr (cell0 P Q C ∩ Y) = c.pr (cell0 P Q C) := by rw [Finset.inter_eq_left.2 sY0]
  have eY2 : c.pr (cell2 P Q C ∩ Y) = c.pr (cell2 P Q C) := by rw [Finset.inter_eq_left.2 sY2]
  -- the cell weights
  have hsum := pr_cells c P Q C Finset.univ
  simp only [Finset.inter_univ, pr_univ] at hsum
  have hP1 := pr_PA_Q c P Q C Finset.univ
  have hP2 := pr_PA_nQ c P Q C Finset.univ
  simp only [Finset.inter_univ] at hP1 hP2
  rw [hP1] at hp1
  rw [hP2] at hp2
  have EX := hEX
  rw [pr_inter_C c P Q C X, pr_P_inter c P Q C X, pr_PA_Q c P Q C X, pr_cells c P Q C X] at EX
  have EY := hEY
  rw [pr_inter_C c P Q C Y, pr_P_inter c P Q C Y, pr_PA_Q c P Q C Y, pr_cells c P Q C Y] at EY
  rw [eX1, eX5, eX4, eX6] at EX
  rw [eY3, eY7, eY0, eY2] at EY
  have lX : ∀ k : Finset Ω, c.pr (k ∩ X) ≤ c.pr k := fun k => pr_mono c Finset.inter_subset_left
  have lY : ∀ k : Finset Ω, c.pr (k ∩ Y) ≤ c.pr k := fun k => pr_mono c Finset.inter_subset_left
  have nX : ∀ k : Finset Ω, 0 ≤ c.pr (k ∩ X) := fun k => pr_nonneg c _
  have nY : ∀ k : Finset Ω, 0 ≤ c.pr (k ∩ Y) := fun k => pr_nonneg c _
  have nW : ∀ k : Finset Ω, 0 ≤ c.pr k := fun k => pr_nonneg c _
  -- the conclusion from the six zero cells
  have hfin : c.pr (cell0 P Q C) = 0 → c.pr (cell2 P Q C) = 0 → c.pr (cell3 P Q C) = 0 →
      c.pr (cell4 P Q C) = 0 → c.pr (cell5 P Q C) = 0 → c.pr (cell6 P Q C) = 0 →
      c.pr (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ))) = 1 := by
    intro h0 h2 h3 h4 h5 h6
    have h := pr_cells c P Q C (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ)))
    have s1 : cell1 P Q C ⊆ P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ)) := fun x hx => by
      simp only [mem_inter, mem_compl, mem_union] at hx ⊢; tauto
    have s7 : cell7 P Q C ⊆ P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ)) := fun x hx => by
      simp only [mem_inter, mem_compl, mem_union] at hx ⊢; tauto
    have e1 : c.pr (cell1 P Q C ∩ (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ)))) = c.pr (cell1 P Q C) := by
      rw [Finset.inter_eq_left.2 s1]
    have e7 : c.pr (cell7 P Q C ∩ (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ)))) = c.pr (cell7 P Q C) := by
      rw [Finset.inter_eq_left.2 s7]
    have z : ∀ k : Finset Ω, c.pr k = 0 → c.pr (k ∩ (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ)))) = 0 :=
      fun k hk => le_antisymm (by
        have := pr_mono c (Finset.inter_subset_left : k ∩ (P ∩ ((Q ∩ C) ∪ (Qᶜ ∩ Cᶜ))) ⊆ k)
        linarith) (pr_nonneg c _)
    rw [h, e1, e7, z _ h0, z _ h2, z _ h3, z _ h4, z _ h5, z _ h6]
    linarith
  have lX0 := lX (cell0 P Q C)
  have lX2 := lX (cell2 P Q C)
  have lX3 := lX (cell3 P Q C)
  have lY4 := lY (cell4 P Q C)
  have lY5 := lY (cell5 P Q C)
  have lY6 := lY (cell6 P Q C)
  have hnum := pair_num (nW (cell0 P Q C)) (nW (cell2 P Q C))
    (nW (cell3 P Q C)) (nW (cell4 P Q C)) (nW (cell5 P Q C)) (nW (cell6 P Q C))
    (nX (cell0 P Q C)) (nX (cell2 P Q C)) (nX (cell3 P Q C))
    (nX (cell7 P Q C)) (nY (cell1 P Q C)) (nY (cell4 P Q C)) (nY (cell5 P Q C))
    (nY (cell6 P Q C)) lX0 lX2 lX3 lY4 lY5 lY6 hp1 hp2 EX EY
    (by
      rcases hk with ⟨k3, k7 | k02⟩ | ⟨k5, k1 | k46⟩
      · exact Or.inl ⟨pr_cell_zero c X (subset_refl _) k3,
          Or.inl (pr_cell_zero c X (subset_refl _) k7)⟩
      · exact Or.inl ⟨pr_cell_zero c X (subset_refl _) k3, Or.inr
          ⟨pr_cell_zero c X (fun x hx => by simp only [mem_inter, mem_compl] at hx ⊢; tauto) k02,
           pr_cell_zero c X (fun x hx => by simp only [mem_inter, mem_compl] at hx ⊢; tauto) k02⟩⟩
      · exact Or.inr ⟨pr_cell_zero c Y (subset_refl _) k5,
          Or.inl (pr_cell_zero c Y (subset_refl _) k1)⟩
      · exact Or.inr ⟨pr_cell_zero c Y (subset_refl _) k5, Or.inr
          ⟨pr_cell_zero c Y (fun x hx => by simp only [mem_inter, mem_compl] at hx ⊢; tauto) k46,
           pr_cell_zero c Y (fun x hx => by simp only [mem_inter, mem_compl] at hx ⊢; tauto) k46⟩⟩)
  exact hfin hnum.1 hnum.2.1 hnum.2.2.1 hnum.2.2.2.1 hnum.2.2.2.2.1 hnum.2.2.2.2.2

/-- The general pair theorem (the 135 collapsing pairs). Write `C = P → Q`. Suppose `X` contains
every `P ∧ ¬Q` world and every `¬P ∧ C` world, and `Y` contains every `P ∧ Q` world and every
`¬P ∧ ¬C` world. Suppose also that one of them is "clean": either `X` misses `P ∧ Q ∧ ¬C` and
(misses `P ∧ Q ∧ C` or misses `¬P ∧ ¬C`), or `Y` misses `P ∧ ¬Q ∧ C` and (misses
`P ∧ ¬Q ∧ ¬C` or misses `¬P ∧ C`). Then positivity and the Resilient Equation under `X` and
under `Y` give C4. -/
theorem pair_collapse (c : Credence Ω) (imp : Conditional Ω) (P Q X Y : Finset Ω)
    (hpos : Positive c P Q) (hX : Resilient c imp P Q X) (hY : Resilient c imp P Q Y)
    (hX1 : P ∩ Qᶜ ⊆ X) (hX2 : Pᶜ ∩ imp P Q ⊆ X)
    (hY1 : P ∩ Q ⊆ Y) (hY2 : Pᶜ ∩ (imp P Q)ᶜ ⊆ Y)
    (hk : (X ∩ (P ∩ Q ∩ (imp P Q)ᶜ) = ∅ ∧
        (X ∩ (P ∩ Q ∩ imp P Q) = ∅ ∨ X ∩ (Pᶜ ∩ (imp P Q)ᶜ) = ∅)) ∨
      (Y ∩ (P ∩ Qᶜ ∩ imp P Q) = ∅ ∧
        (Y ∩ (P ∩ Qᶜ ∩ (imp P Q)ᶜ) = ∅ ∨ Y ∩ (Pᶜ ∩ imp P Q) = ∅))) :
    C4 c imp P Q :=
  pair_collapse_aux c P Q (imp P Q) X Y hpos.1 hpos.2 (res_cross c imp P Q X hX)
    (res_cross c imp P Q Y hY) hX1 hX2 hY1 hY2 hk

/-- R3/K3 instance: the pair `{⊤, P ⊃ Q}` is the simplest instance of `pair_collapse`, so
positivity and the Resilient Equation under `⊤` and under `P ⊃ Q` give C4. By
`thesis_iff_resilient_univ` the first hypothesis is the Thesis, so this is equivalent to
`milne_collapse`. -/
theorem equation_matimp_collapse (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q) (hT : Resilient c imp P Q Finset.univ)
    (hX : Resilient c imp P Q (Pᶜ ∪ Q)) : C4 c imp P Q := by
  refine pair_collapse c imp P Q Finset.univ (Pᶜ ∪ Q) hpos hT hX (Finset.subset_univ _)
    (Finset.subset_univ _) ?_ ?_ (Or.inr ⟨?_, Or.inl ?_⟩)
  · intro x hx; simp only [mem_inter, mem_union, mem_compl] at hx ⊢; tauto
  · intro x hx; simp only [mem_inter, mem_union, mem_compl] at hx ⊢; tauto
  · exact Finset.subset_empty.1 fun x hx => by
      simp only [mem_inter, mem_union, mem_compl] at hx; tauto
  · exact Finset.subset_empty.1 fun x hx => by
      simp only [mem_inter, mem_union, mem_compl] at hx; tauto

end Triviality
