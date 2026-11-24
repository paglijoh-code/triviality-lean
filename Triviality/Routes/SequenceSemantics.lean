/-
Copyright (c) 2026 Johnny Paglino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnny Paglino
-/
import Triviality.TwoWays

/-!
# Sorting sequence semantics

A conditional is *centred* at `P, Q` when, inside `P`, it agrees with `Q` (Modus Ponens and
And-to-If; every order model). In a product-measure sequence model the rate of `P → Q` off `P`
is the constant `Pr (Q | P)` on Boolean propositions; that is the hypothesis `hrate` below.
-/

open Finset

namespace Triviality.SequenceSemantics

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Inside the antecedent, the conditional agrees with the consequent. -/
def Centred (imp : Conditional Ω) (P Q : Finset Ω) : Prop := imp P Q ∩ P = P ∩ Q

theorem mem_centred {imp : Conditional Ω} {P Q : Finset Ω} (h : Centred imp P Q) (x : Ω) :
    (x ∈ imp P Q ∧ x ∈ P) ↔ (x ∈ P ∧ x ∈ Q) := by
  have hx := Finset.ext_iff.mp h x
  simpa only [Finset.mem_inter] using hx

/-- The credence of a centred conditional on `X`, split by the antecedent. -/
theorem pr_split (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (X : Finset Ω) :
    c.pr (imp P Q ∩ X) = c.pr (P ∩ Q ∩ X) + c.pr (imp P Q ∩ Pᶜ ∩ X) := by
  have e1 : P ∩ (imp P Q ∩ X) = P ∩ Q ∩ X := by
    ext x
    have hx := mem_centred h x
    simp only [Finset.mem_inter]
    tauto
  have e2 : Pᶜ ∩ (imp P Q ∩ X) = imp P Q ∩ Pᶜ ∩ X := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  have ht := pr_total c P (imp P Q ∩ X)
  rw [e1, e2] at ht
  exact ht

/-- For a centred conditional, resilience under `X` compares the rate off `P` with the rate
on `P`. -/
theorem resilient_centred (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (X : Finset Ω) :
    Resilient c imp P Q X ↔
      c.pr (imp P Q ∩ Pᶜ ∩ X) * c.pr (P ∩ X) = c.pr (P ∩ Q ∩ X) * c.pr (Pᶜ ∩ X) := by
  rw [resilient_iff_mul, pr_split c h X]
  have ht := pr_total c P X
  constructor
  · intro e
    rw [ht] at e
    linear_combination e
  · intro e
    rw [ht]
    linear_combination e

/-- Boolean blocks of a sequence model: resilient iff the block lies in `P` almost surely, or it
leaves the rate of `Q` given `P` unchanged. -/
theorem resilient_of_rate (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) {X : Finset Ω} {μ : ℝ}
    (hrate : c.pr (imp P Q ∩ Pᶜ ∩ X) = μ * c.pr (Pᶜ ∩ X)) :
    Resilient c imp P Q X ↔ c.pr (Pᶜ ∩ X) = 0 ∨ c.pr (P ∩ Q ∩ X) = μ * c.pr (P ∩ X) := by
  rw [resilient_centred c h X, hrate]
  constructor
  · intro e
    have e' : c.pr (Pᶜ ∩ X) * (c.pr (P ∩ Q ∩ X) - μ * c.pr (P ∩ X)) = 0 := by
      linear_combination -e
    rcases mul_eq_zero.mp e' with e' | e'
    · exact Or.inl e'
    · exact Or.inr (by linarith)
  · rintro (e | e)
    · rw [e]; ring
    · rw [e]; ring

/-- A nondegenerate pair of a sequence model is never resilient under both `Q` and `¬Q`. -/
theorem not_both_resilient (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (hpos : Positive c P Q) (hP : c.pr P < 1) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hQ : c.pr (imp P Q ∩ Pᶜ ∩ Q) = μ * c.pr (Pᶜ ∩ Q))
    (hQc : c.pr (imp P Q ∩ Pᶜ ∩ Qᶜ) = μ * c.pr (Pᶜ ∩ Qᶜ)) :
    ¬ (Resilient c imp P Q Q ∧ Resilient c imp P Q Qᶜ) := by
  rintro ⟨h1, h2⟩
  have n1 : c.pr (Pᶜ ∩ Q) = 0 := by
    rcases (resilient_of_rate c h hQ).mp h1 with e | e
    · exact e
    · exfalso
      have es : P ∩ Q ∩ Q = P ∩ Q := by rw [Finset.inter_assoc, Finset.inter_self]
      rw [es] at e
      have := hpos.1
      nlinarith
  have n2 : c.pr (Pᶜ ∩ Qᶜ) = 0 := by
    rcases (resilient_of_rate c h hQc).mp h2 with e | e
    · exact e
    · exfalso
      have es : P ∩ Q ∩ Qᶜ = ∅ := by
        ext x
        simp
      have e0 : c.pr (∅ : Finset Ω) = 0 := Finset.sum_empty
      rw [es, e0] at e
      have := mul_pos hμ0 hpos.2
      linarith
  have ht := pr_total c Q Pᶜ
  rw [Finset.inter_comm Q, Finset.inter_comm Qᶜ, n1, n2] at ht
  have := pr_add_pr_compl c P
  linarith

/-! ### Learning the conditional itself -/

/-- Learning a centred conditional, or its negation, or neither: the family `{C, ¬C}` is
antecedent-independent (case (B)) as soon as the Thesis holds. -/
theorem antecedentIndep_conditional (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (hP : 0 < c.pr P) (hT : Thesis c imp P Q) :
    AntecedentIndep c imp P Q (fun b : Bool => if b then imp P Q else (imp P Q)ᶜ) := by
  have hne : c.pr P ≠ 0 := hP.ne'
  have hC : c.pr (imp P Q) = c.pr (P ∩ Q) / c.pr P := hT hP
  have e1 : P ∩ imp P Q = P ∩ Q := by rw [Finset.inter_comm]; exact h
  have e2 : P ∩ Q ∩ imp P Q = P ∩ Q := by
    ext x
    have hx := mem_centred h x
    simp only [Finset.mem_inter]
    tauto
  have e3 : P ∩ Q ∩ (imp P Q)ᶜ = ∅ := by
    ext x
    have hx := mem_centred h x
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.notMem_empty, iff_false]
    tauto
  have e0 : c.pr (∅ : Finset Ω) = 0 := Finset.sum_empty
  have hs := pr_total c (imp P Q) P
  rw [Finset.inter_comm (imp P Q) P, Finset.inter_comm (imp P Q)ᶜ P, e1] at hs
  have hn := pr_add_pr_compl c (imp P Q)
  refine ⟨1 / c.pr P, fun b => ?_⟩
  cases b
  · simp only [Bool.false_eq_true, if_false]
    refine ⟨?_, ?_⟩
    · have k1 : c.pr (P ∩ (imp P Q)ᶜ) = c.pr P - c.pr (P ∩ Q) := by linarith
      have k2 : c.pr (imp P Q)ᶜ = 1 - c.pr (P ∩ Q) / c.pr P := by linarith
      rw [k1, k2]
      field_simp
    · rw [Finset.inter_compl, e3, e0, mul_zero]
  · simp only [if_true]
    refine ⟨?_, ?_⟩
    · rw [e1, hC]; ring
    · rw [Finset.inter_self, e2, hC]; ring

/-- Hence resilience under every union of `{C, ¬C}`, by the two-ways theorem. -/
theorem resilient_conditional (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (hpos : 0 < c.pr (P ∩ Q)) (hT : Thesis c imp P Q) (S : Finset Bool) :
    Resilient c imp P Q (S.biUnion fun b => if b then imp P Q else (imp P Q)ᶜ) := by
  have hP : 0 < c.pr P := lt_of_lt_of_le hpos (pr_mono c Finset.inter_subset_left)
  have hB : ∀ i j : Bool, i ≠ j →
      Disjoint ((fun b : Bool => if b then imp P Q else (imp P Q)ᶜ) i)
        ((fun b : Bool => if b then imp P Q else (imp P Q)ᶜ) j) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact absurd rfl hij
  have e1 : P ∩ imp P Q = P ∩ Q := by rw [Finset.inter_comm]; exact h
  refine (two_ways c imp P Q _ hB ⟨true, ?_⟩).mpr
    (Or.inr (antecedentIndep_conditional c h hP hT)) S
  simpa only [if_true, e1] using hpos

/-- For a positive pair, `{C, ¬C}` is not a uniform-rate family: case (B) only. -/
theorem not_uniformRate_conditional (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (hpos : Positive c P Q) :
    ¬ UniformRate c imp P Q (fun b : Bool => if b then imp P Q else (imp P Q)ᶜ) := by
  rintro ⟨μ, hμ⟩
  have e1 : P ∩ imp P Q = P ∩ Q := by rw [Finset.inter_comm]; exact h
  have e2 : P ∩ Q ∩ imp P Q = P ∩ Q := by
    ext x
    have hx := mem_centred h x
    simp only [Finset.mem_inter]
    tauto
  have e3 : P ∩ Q ∩ (imp P Q)ᶜ = ∅ := by
    ext x
    have hx := mem_centred h x
    simp only [Finset.mem_inter, Finset.mem_compl, Finset.notMem_empty, iff_false]
    tauto
  have e4 : P ∩ (imp P Q)ᶜ = P ∩ Qᶜ := by
    ext x
    have hx := mem_centred h x
    simp only [Finset.mem_inter, Finset.mem_compl]
    tauto
  have e0 : c.pr (∅ : Finset Ω) = 0 := Finset.sum_empty
  have ht := (hμ true).1
  have hf := (hμ false).1
  simp only [if_true, e1, e2] at ht
  simp only [Bool.false_eq_true, if_false, e3, e4, e0] at hf
  have h1 := hpos.1
  have h2 := hpos.2
  have : μ ≠ 0 := by
    rintro rfl
    linarith
  rcases mul_eq_zero.mp hf.symm with k | k
  · exact this k
  · linarith

/-- Learning `P ∨ (P → Q)` always breaks resilience for a nondegenerate centred pair satisfying
the Thesis (compare Dorr–Mandelkern, Theorem 7.8(a)). -/
theorem not_resilient_or (c : Credence Ω) {imp : Conditional Ω} {P Q : Finset Ω}
    (h : Centred imp P Q) (hpos : Positive c P Q) (hP1 : c.pr P < 1) (hT : Thesis c imp P Q) :
    ¬ Resilient c imp P Q (P ∪ imp P Q) := by
  rw [resilient_centred c h]
  intro e
  have hP : 0 < c.pr P := lt_of_lt_of_le hpos.1 (pr_mono c Finset.inter_subset_left)
  have hC : c.pr (imp P Q) = c.pr (P ∩ Q) / c.pr P := hT hP
  have s1 : imp P Q ∩ Pᶜ ∩ (P ∪ imp P Q) = imp P Q ∩ Pᶜ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    tauto
  have s2 : Pᶜ ∩ (P ∪ imp P Q) = imp P Q ∩ Pᶜ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
    tauto
  have s3 : P ∩ (P ∪ imp P Q) = P := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have s4 : P ∩ Q ∩ (P ∪ imp P Q) = P ∩ Q := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  rw [s1, s2, s3, s4] at e
  have hs := pr_split c h Finset.univ
  simp only [Finset.inter_univ] at hs
  have hp := pr_total c Q P
  rw [Finset.inter_comm Q, Finset.inter_comm Qᶜ] at hp
  have hd : c.pr (imp P Q ∩ Pᶜ) * c.pr P = c.pr (P ∩ Q) * (1 - c.pr P) := by
    have k : c.pr (imp P Q) * c.pr P = c.pr (P ∩ Q) := by
      rw [hC, div_mul_cancel₀ _ hP.ne']
    rw [hs] at k
    linear_combination k
  have hdpos : 0 < c.pr (imp P Q ∩ Pᶜ) := by
    have : 0 < c.pr (imp P Q ∩ Pᶜ) * c.pr P := by
      rw [hd]; exact mul_pos hpos.1 (by linarith)
    exact pos_of_mul_pos_left this hP.le
  have hq := hpos.2
  have : c.pr (imp P Q ∩ Pᶜ) * c.pr (P ∩ Qᶜ) = 0 := by
    rw [hp] at e
    linear_combination e
  exact (mul_pos hdpos hq).ne' this

/-- For `P ⊆ X`, resilience under `X` says the conditional has rate `Pr (Q | P)` outside `X`
(the form of Dorr–Mandelkern, Lemma H.1). -/
theorem resilient_superset (c : Credence Ω) {imp : Conditional Ω} {P Q X : Finset Ω}
    (hP : 0 < c.pr P) (hT : Thesis c imp P Q) (hX : P ⊆ X) :
    Resilient c imp P Q X ↔ c.pr (imp P Q ∩ Xᶜ) * c.pr P = c.pr (P ∩ Q) * c.pr Xᶜ := by
  have hC : c.pr (imp P Q) = c.pr (P ∩ Q) / c.pr P := hT hP
  have k : c.pr (imp P Q) * c.pr P = c.pr (P ∩ Q) := by rw [hC, div_mul_cancel₀ _ hP.ne']
  have s1 : P ∩ X = P := Finset.inter_eq_left.mpr hX
  have s2 : P ∩ Q ∩ X = P ∩ Q := by rw [Finset.inter_right_comm, s1]
  have ht := pr_total c X (imp P Q)
  rw [Finset.inter_comm X, Finset.inter_comm Xᶜ] at ht
  have hn := pr_add_pr_compl c X
  have hx : c.pr X = 1 - c.pr Xᶜ := by linarith
  have hc : c.pr (imp P Q ∩ X) = c.pr (imp P Q) - c.pr (imp P Q ∩ Xᶜ) := by linarith
  rw [resilient_iff_mul, s1, s2, hx, hc]
  constructor
  · intro e; linear_combination k - e
  · intro e; linear_combination k - e

/-! ### The same pair on a finite space -/

/-- The uniform credence on six worlds. -/
noncomputable def six : Credence (Fin 6) where
  w _ := 1 / 6
  nonneg _ := by norm_num
  sum_one := by rw [Finset.sum_const]; norm_num

theorem six_pr (A : Finset (Fin 6)) : six.pr A = (A.card : ℝ) / 6 := by
  change ∑ _ω ∈ A, (1 / 6 : ℝ) = _
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Worlds `P∧Q`, `P∧¬Q`, and the four cells of `±Q`, `±C` outside `P`. -/
def sixImp : Conditional (Fin 6) := fun _ _ => {0, 2, 4}

/-- The six-cell shadow of a sequence model keeps S1–S4 and the Thesis for the pair, has the
sequence model's rate off `P`, and fails resilience under both `Q` and `¬Q`. -/
theorem six_verdict :
    Centred sixImp {0, 1} {0, 2, 3} ∧ Positive six {0, 1} {0, 2, 3} ∧
      Thesis six sixImp {0, 1} {0, 2, 3} ∧
      ¬ Resilient six sixImp {0, 1} {0, 2, 3} {0, 2, 3} ∧
      ¬ Resilient six sixImp {0, 1} {0, 2, 3} ({0, 2, 3} : Finset (Fin 6))ᶜ := by
  refine ⟨by unfold Centred; decide, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [six_pr, show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3}).card = 1 by decide]; norm_num
  · rw [six_pr, show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3}ᶜ).card = 1 by decide]; norm_num
  · intro _
    unfold Credence.cond
    rw [six_pr, six_pr, six_pr,
      show (sixImp {0, 1} {0, 2, 3}).card = 3 by decide,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3}).card = 1 by decide,
      show (({0, 1} : Finset (Fin 6))).card = 2 by decide]
    norm_num
  · rw [resilient_iff_mul, six_pr, six_pr, six_pr, six_pr,
      show (sixImp {0, 1} {0, 2, 3} ∩ {0, 2, 3}).card = 2 by decide,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3}).card = 1 by decide,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3} ∩ {0, 2, 3}).card = 1 by decide,
      show (({0, 2, 3} : Finset (Fin 6))).card = 3 by decide]
    norm_num
  · rw [resilient_iff_mul, six_pr, six_pr, six_pr, six_pr,
      show (sixImp {0, 1} {0, 2, 3} ∩ {0, 2, 3}ᶜ).card = 1 by decide,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3}ᶜ).card = 1 by decide,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 2, 3} ∩ {0, 2, 3}ᶜ).card = 0 by decide,
      show (({0, 2, 3} : Finset (Fin 6))ᶜ).card = 3 by decide]
    norm_num

/-! ### Nested consequents need an infinite algebra -/

/-- On a finite space, a centred conditional cannot satisfy the Thesis for an antecedent of
credence in `(1/2, 1)` and a consequent that is a least positive-weight world inside it. -/
theorem finite_obstruction (c : Credence Ω) (imp : Conditional Ω) {P : Finset Ω} {y : Ω}
    (hy : y ∈ P) (hw : 0 < c.w y) (hmin : ∀ ω, 0 < c.w ω → c.w y ≤ c.w ω)
    (h1 : 1 < 2 * c.pr P) (h2 : c.pr P < 1) (hC : Centred imp P {y}) :
    ¬ Thesis c imp P {y} := by
  intro hT
  have hP : 0 < c.pr P := by linarith
  have hT' : c.pr (imp P {y}) = c.pr (P ∩ {y}) / c.pr P := hT hP
  have k : c.pr (imp P {y}) * c.pr P = c.pr (P ∩ {y}) := by
    rw [hT', div_mul_cancel₀ _ hP.ne']
  have ey : c.pr (P ∩ {y}) = c.w y := by rw [pr_inter_singleton, if_pos hy]
  have hs := pr_split c hC Finset.univ
  simp only [Finset.inter_univ] at hs
  rw [hs, ey] at k
  have hd : c.pr (imp P {y} ∩ Pᶜ) * c.pr P = c.w y * (1 - c.pr P) := by linear_combination k
  have hdpos : 0 < c.pr (imp P {y} ∩ Pᶜ) := by
    have : 0 < c.pr (imp P {y} ∩ Pᶜ) * c.pr P := by
      rw [hd]; exact mul_pos hw (by linarith)
    exact pos_of_mul_pos_left this hP.le
  obtain ⟨ω, hω, hωpos⟩ := exists_pos_of_pr_pos c hdpos
  have hle : c.w ω ≤ c.pr (imp P {y} ∩ Pᶜ) := by
    rw [← pr_singleton c ω]
    exact pr_mono c (Finset.singleton_subset_iff.mpr hω)
  have hge := le_trans (hmin ω hωpos) hle
  have := mul_le_mul_of_nonneg_right hge hP.le
  rw [hd] at this
  nlinarith

theorem three_cells_aux (c : Credence Ω) (imp : Conditional Ω) {A B D : Finset Ω}
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hsum : c.pr A + c.pr B + c.pr D = 1)
    (hA : 0 < c.pr A) (hB : 0 < c.pr B) (hD : 0 < c.pr D)
    (H : ∀ P : Finset Ω, P = A ∪ B ∨ P = A ∪ D → ∀ y ∈ P, Centred imp P {y} ∧ Thesis c imp P {y})
    {y : Ω} (hy : y ∈ A) (hw : 0 < c.w y) (hmin : ∀ ω, 0 < c.w ω → c.w y ≤ c.w ω) : False := by
  rcases le_total (c.pr B) (c.pr D) with hle | hle
  · have hy' : y ∈ A ∪ D := Finset.mem_union_left _ hy
    have hp := pr_union_of_disjoint c hAD
    obtain ⟨h1, h2⟩ := H _ (Or.inr rfl) y hy'
    exact finite_obstruction c imp hy' hw hmin (by linarith) (by linarith) h1 h2
  · have hy' : y ∈ A ∪ B := Finset.mem_union_left _ hy
    have hp := pr_union_of_disjoint c hAB
    obtain ⟨h1, h2⟩ := H _ (Or.inl rfl) y hy'
    exact finite_obstruction c imp hy' hw hmin (by linarith) (by linarith) h1 h2

/-- With three cells of positive credence, no finite space carries a centred conditional that
satisfies the Thesis for every two-cell antecedent and every world-consequent in it. So the
algebra of a sequence model with at least three cells and the Thesis for all consequents is
infinite. -/
theorem three_cells_infinite (c : Credence Ω) (imp : Conditional Ω) {A B D : Finset Ω}
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D) (hcov : A ∪ B ∪ D = Finset.univ)
    (hA : 0 < c.pr A) (hB : 0 < c.pr B) (hD : 0 < c.pr D) :
    ¬ ∀ P : Finset Ω, P = A ∪ B ∨ P = A ∪ D ∨ P = B ∪ D →
      ∀ y ∈ P, Centred imp P {y} ∧ Thesis c imp P {y} := by
  intro H
  have hsum : c.pr A + c.pr B + c.pr D = 1 := by
    rw [← pr_union_of_disjoint c hAB,
      ← pr_union_of_disjoint c (Finset.disjoint_union_left.mpr ⟨hAD, hBD⟩), hcov, pr_univ]
  obtain ⟨a, _, ha⟩ := exists_pos_of_pr_pos c hA
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun ω => 0 < c.w ω) c.w
    ⟨a, by simp [ha]⟩
  have hw : 0 < c.w y := (Finset.mem_filter.mp hy).2
  have hmin' : ∀ ω, 0 < c.w ω → c.w y ≤ c.w ω := fun ω hω => hmin ω (by simp [hω])
  have hyU : y ∈ A ∪ B ∪ D := hcov ▸ Finset.mem_univ y
  rcases Finset.mem_union.mp hyU with hAy | hDy
  · rcases Finset.mem_union.mp hAy with hAy | hBy
    · refine three_cells_aux c imp hAB hAD hsum hA hB hD (fun P hP => H P ?_) hAy hw hmin'
      tauto
    · refine three_cells_aux c imp hAB.symm hBD (by linarith) hB hA hD (fun P hP => H P ?_) hBy hw
        hmin'
      rw [Finset.union_comm B A] at hP
      tauto
  · refine three_cells_aux c imp hAD.symm hBD.symm (by linarith) hD hA hB (fun P hP => H P ?_) hDy
      hw hmin'
    rw [Finset.union_comm D A, Finset.union_comm D B] at hP
    tauto

end Triviality.SequenceSemantics
