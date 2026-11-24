/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Basic
import Triviality.Probability

/-!
# The two-ways theorem: resilience under a learning partition

Fix a conditional `P → Q` and a finite family of pairwise disjoint blocks `B i`. The agent may
learn any union of blocks. Assume some block meets `P` with positive credence. Then the Resilient
Equation holds under every union of blocks iff one of two things holds:

* (A) `UniformRate`: for some `μ`, every block has `Pr (P ∧ Q ∧ B) = μ Pr (P ∧ B)` and
  `Pr ((P → Q) ∧ B) = μ Pr B`. Learning the block tells nothing about `P → Q`, nor about `Q`
  given `P`.
* (B) `AntecedentIndep`: for some `λ`, every block has `Pr B = λ Pr (P ∧ B)` and
  `Pr ((P → Q) ∧ B) = λ Pr (P ∧ Q ∧ B)`. Learning the block tells nothing about `P`, and each
  block satisfies the Resilient Equation on its own.

The proof is linear algebra. With `a_X = (Pr (C ∧ X), Pr (P ∧ X), Pr (P ∧ Q ∧ X), Pr X)`,
the Resilient Equation under `X` is `q (a_X) = 0` for the split form `q (c, p, r, t) = c p - r t`
(`resilient_iff_mul`). Requiring it for all unions makes the span of the block vectors totally
isotropic, and the two cases are the two rulings of the quadric `c p = r t` (`two_ways_vec`).

Lewis 1976 (`two_ways_lewis`, the partition `{Q, ¬Q}`) and Fitelson's R2 (`two_ways_fitelson`,
the partition into worlds) follow.

## Main results

* `Triviality.resilient_iff_mul`: the guarded Resilient Equation as one polynomial identity.
* `Triviality.two_ways_vec`, `Triviality.two_ways_vec_converse`: the algebraic core.
* `Triviality.two_ways`: the theorem for any finite space and any finite family of disjoint blocks.
* `Triviality.two_ways_lewis`, `Triviality.two_ways_fitelson`: the corollaries.
-/

open Finset

namespace Triviality

set_option linter.unusedSectionVars false

/-! ### The algebraic core -/

/-- If `(∑ c)(∑ p) = (∑ r)(∑ t)` over every finite set of indices, and some `p k ≠ 0`, then the
vectors `(c, p, r, t)` all lie in one plane of one of the two rulings of `c p = r t`. -/
theorem two_ways_vec {ι : Type*} [DecidableEq ι] (c p r t : ι → ℝ)
    (h : ∀ S : Finset ι,
      (∑ i ∈ S, c i) * (∑ i ∈ S, p i) = (∑ i ∈ S, r i) * (∑ i ∈ S, t i))
    (k : ι) (hk : p k ≠ 0) :
    (∃ μ : ℝ, ∀ i, r i = μ * p i ∧ c i = μ * t i) ∨
    (∃ l : ℝ, ∀ i, t i = l * p i ∧ c i = l * r i) := by
  have hs : ∀ i, c i * p i = r i * t i := by
    intro i
    have := h {i}
    simp only [Finset.sum_singleton] at this
    exact this
  -- the polarized identity: the bilinear form vanishes on every pair of block vectors
  have hb : ∀ i j, c i * p j + c j * p i = r i * t j + r j * t i := by
    intro i j
    by_cases hij : i = j
    · subst hij
      linear_combination 2 * hs i
    · have := h {i, j}
      simp only [Finset.sum_pair hij] at this
      linear_combination this - hs i - hs j
  obtain ⟨l, hl⟩ : ∃ l, t k = l * p k := ⟨t k / p k, (div_mul_cancel₀ (t k) hk).symm⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, r k = μ * p k := ⟨r k / p k, (div_mul_cancel₀ (r k) hk).symm⟩
  have hck : c k = μ * l * p k := by
    apply mul_right_cancel₀ hk
    rw [hs k, hμ, hl]
    ring
  have hcj : ∀ j, c j = μ * t j + l * r j - μ * l * p j := by
    intro j
    have e0 := hb k j
    rw [hck, hμ, hl] at e0
    have e : p k * (c j - (μ * t j + l * r j - μ * l * p j)) = 0 := by
      linear_combination e0
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hk)
  have hq : ∀ j, (t j - l * p j) * (μ * p j - r j) = 0 := by
    intro j
    linear_combination hs j - p j * hcj j
  have hmix : ∀ i j,
      (t j - l * p j) * (μ * p i - r i) + (t i - l * p i) * (μ * p j - r j) = 0 := by
    intro i j
    linear_combination hb i j - p j * hcj i - p i * hcj j
  by_cases hall : ∀ j, t j = l * p j
  · right
    refine ⟨l, fun j => ⟨hall j, ?_⟩⟩
    rw [hcj j, hall j]
    ring
  · left
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hj' : t j - l * p j ≠ 0 := sub_ne_zero.mpr hj
    have hrj : μ * p j - r j = 0 := (mul_eq_zero.mp (hq j)).resolve_left hj'
    refine ⟨μ, fun i => ?_⟩
    have e := hmix i j
    rw [hrj, mul_zero, add_zero] at e
    have hri : r i = μ * p i := by
      have := (mul_eq_zero.mp e).resolve_left hj'
      linarith
    refine ⟨hri, ?_⟩
    rw [hcj i, hri]
    ring

/-- Conversely, vectors in one plane of either ruling satisfy `(∑ c)(∑ p) = (∑ r)(∑ t)` over every
finite set of indices. -/
theorem two_ways_vec_converse {ι : Type*} (c p r t : ι → ℝ)
    (h : (∃ μ : ℝ, ∀ i, r i = μ * p i ∧ c i = μ * t i) ∨
      (∃ l : ℝ, ∀ i, t i = l * p i ∧ c i = l * r i))
    (S : Finset ι) :
    (∑ i ∈ S, c i) * (∑ i ∈ S, p i) = (∑ i ∈ S, r i) * (∑ i ∈ S, t i) := by
  rcases h with ⟨μ, hμ⟩ | ⟨l, hl⟩
  · have h1 : ∑ i ∈ S, r i = μ * ∑ i ∈ S, p i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (hμ i).1
    have h2 : ∑ i ∈ S, c i = μ * ∑ i ∈ S, t i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (hμ i).2
    rw [h1, h2]; ring
  · have h1 : ∑ i ∈ S, t i = l * ∑ i ∈ S, p i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (hl i).1
    have h2 : ∑ i ∈ S, c i = l * ∑ i ∈ S, r i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => (hl i).2
    rw [h1, h2]; ring

/-! ### The probabilistic statement -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The guarded Resilient Equation under `X` is the single identity
`Pr (C ∧ X) Pr (P ∧ X) = Pr (P ∧ Q ∧ X) Pr X`. The guard is automatic: if `Pr (P ∧ X) = 0` both
sides vanish. -/
theorem resilient_iff_mul (c : Credence Ω) (imp : Conditional Ω) (P Q X : Finset Ω) :
    Resilient c imp P Q X ↔
      c.pr (imp P Q ∩ X) * c.pr (P ∩ X) = c.pr (P ∩ Q ∩ X) * c.pr X := by
  unfold Resilient Credence.cond
  have e1 : X ∩ imp P Q = imp P Q ∩ X := Finset.inter_comm _ _
  have e2 : P ∩ X ∩ Q = P ∩ Q ∩ X := Finset.inter_right_comm _ _ _
  rw [e1, e2]
  have hsub : P ∩ Q ∩ X ⊆ P ∩ X := by
    intro x hx
    simp only [Finset.mem_inter] at hx ⊢
    tauto
  constructor
  · intro h
    rcases (pr_nonneg c (P ∩ X)).eq_or_lt with h0 | hpos
    · have hr : c.pr (P ∩ Q ∩ X) = 0 :=
        le_antisymm (by linarith [pr_mono c hsub]) (pr_nonneg c _)
      rw [hr, ← h0]
      ring
    · have hX : 0 < c.pr X := lt_of_lt_of_le hpos (pr_mono c Finset.inter_subset_right)
      have := h hpos
      rw [div_eq_div_iff hX.ne' hpos.ne'] at this
      exact this
  · intro h hpos
    have hX : 0 < c.pr X := lt_of_lt_of_le hpos (pr_mono c Finset.inter_subset_right)
    rw [div_eq_div_iff hX.ne' hpos.ne']
    exact h

/-- Credence of `A` intersected with a union of disjoint blocks adds over the blocks. -/
theorem pr_inter_biUnion (c : Credence Ω) {ι : Type*} [DecidableEq ι] (B : ι → Finset Ω)
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j)) (A : Finset Ω) (S : Finset ι) :
    c.pr (A ∩ S.biUnion B) = ∑ i ∈ S, c.pr (A ∩ B i) := by
  unfold Credence.pr
  rw [Finset.inter_biUnion, Finset.sum_biUnion]
  intro i _ j _ hij
  exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hB i j hij)

/-- (A) Uniform rate: every block gives `Q` given `P`, and `P → Q`, the same credence `μ`
(written multiplicatively, so null blocks are allowed). -/
def UniformRate (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω) {ι : Type*}
    (B : ι → Finset Ω) : Prop :=
  ∃ μ : ℝ, ∀ i, c.pr (P ∩ Q ∩ B i) = μ * c.pr (P ∩ B i) ∧ c.pr (imp P Q ∩ B i) = μ * c.pr (B i)

/-- (B) Antecedent-independence: every block gives `P` the same credence `1 / λ`, and each block
satisfies the Resilient Equation on its own (written multiplicatively). -/
def AntecedentIndep (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω) {ι : Type*}
    (B : ι → Finset Ω) : Prop :=
  ∃ l : ℝ, ∀ i, c.pr (B i) = l * c.pr (P ∩ B i) ∧ c.pr (imp P Q ∩ B i) = l * c.pr (P ∩ Q ∩ B i)

/-- **The two-ways theorem.** For pairwise disjoint blocks `B i`, some block meeting `P` with
positive credence, the Resilient Equation holds under every union of blocks iff the blocks have a
uniform rate or are antecedent-independent. -/
theorem two_ways (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω) {ι : Type*}
    [DecidableEq ι] (B : ι → Finset Ω) (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hP : ∃ i, 0 < c.pr (P ∩ B i)) :
    (∀ S : Finset ι, Resilient c imp P Q (S.biUnion B)) ↔
      UniformRate c imp P Q B ∨ AntecedentIndep c imp P Q B := by
  have key : ∀ S : Finset ι, Resilient c imp P Q (S.biUnion B) ↔
      (∑ i ∈ S, c.pr (imp P Q ∩ B i)) * (∑ i ∈ S, c.pr (P ∩ B i)) =
        (∑ i ∈ S, c.pr (P ∩ Q ∩ B i)) * (∑ i ∈ S, c.pr (B i)) := by
    intro S
    have ht : c.pr (S.biUnion B) = ∑ i ∈ S, c.pr (B i) := by
      simpa using pr_inter_biUnion c B hB Finset.univ S
    rw [resilient_iff_mul, pr_inter_biUnion c B hB, pr_inter_biUnion c B hB,
      pr_inter_biUnion c B hB, ht]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hP
    rcases two_ways_vec (fun i => c.pr (imp P Q ∩ B i)) (fun i => c.pr (P ∩ B i))
        (fun i => c.pr (P ∩ Q ∩ B i)) (fun i => c.pr (B i)) (fun S => (key S).1 (h S)) k
        hk.ne' with ⟨μ, hμ⟩ | ⟨l, hl⟩
    · exact Or.inl ⟨μ, hμ⟩
    · exact Or.inr ⟨l, hl⟩
  · intro h S
    apply (key S).2
    rcases h with ⟨μ, hμ⟩ | ⟨l, hl⟩
    · exact two_ways_vec_converse (fun i => c.pr (imp P Q ∩ B i)) (fun i => c.pr (P ∩ B i))
        (fun i => c.pr (P ∩ Q ∩ B i)) (fun i => c.pr (B i)) (Or.inl ⟨μ, hμ⟩) S
    · exact two_ways_vec_converse (fun i => c.pr (imp P Q ∩ B i)) (fun i => c.pr (P ∩ B i))
        (fun i => c.pr (P ∩ Q ∩ B i)) (fun i => c.pr (B i)) (Or.inr ⟨l, hl⟩) S

/-! ### Corollaries -/

/-- Lewis 1976 from the two-ways theorem: positivity and resilience under every union of
`{Q, ¬Q}` give `Pr (Q | P) = Pr Q`. Case (A) is impossible and case (B) is independence. -/
theorem two_ways_lewis (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q)
    (h : ∀ S : Finset Bool, Resilient c imp P Q (S.biUnion fun b => if b then Q else Qᶜ)) :
    c.cond Q P = c.pr Q := by
  have hB : ∀ i j : Bool, i ≠ j →
      Disjoint ((fun b => if b then Q else Qᶜ) i) ((fun b => if b then Q else Qᶜ) j) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact absurd rfl hij
  have hP : ∃ i : Bool, 0 < c.pr (P ∩ (fun b => if b then Q else Qᶜ) i) := ⟨true, hpos.1⟩
  rcases (two_ways c imp P Q _ hB hP).1 h with ⟨μ, hμ⟩ | ⟨l, hl⟩
  · exfalso
    have h1 : c.pr (P ∩ Q ∩ Q) = μ * c.pr (P ∩ Q) := (hμ true).1
    have h0 : c.pr (P ∩ Q ∩ Qᶜ) = μ * c.pr (P ∩ Qᶜ) := (hμ false).1
    have e1 : P ∩ Q ∩ Q = P ∩ Q := by rw [Finset.inter_assoc, Finset.inter_self]
    have e0 : c.pr (P ∩ Q ∩ Qᶜ) = 0 := by
      have : P ∩ Q ∩ Qᶜ = ∅ := by
        rw [Finset.inter_assoc, Finset.disjoint_iff_inter_eq_empty.mp
          (disjoint_compl_right (a := Q)), Finset.inter_empty]
      rw [this]
      exact Finset.sum_empty
    rw [e1] at h1
    rw [e0] at h0
    rcases mul_eq_zero.mp h0.symm with hz | hz
    · rw [hz, zero_mul] at h1
      linarith [hpos.1]
    · linarith [hpos.2]
  · have h1 : c.pr Q = l * c.pr (P ∩ Q) := (hl true).1
    have h0 : c.pr Qᶜ = l * c.pr (P ∩ Qᶜ) := (hl false).1
    have hPpos : 0 < c.pr P := lt_of_lt_of_le hpos.1 (pr_mono c Finset.inter_subset_left)
    have htot : c.pr P = c.pr (P ∩ Q) + c.pr (P ∩ Qᶜ) := by
      rw [pr_total c Q P, Finset.inter_comm Q P, Finset.inter_comm Qᶜ P]
    have hsum : l * c.pr P = 1 := by
      have := pr_add_pr_compl c Q
      rw [htot]
      linarith
    unfold Credence.cond
    rw [div_eq_iff hPpos.ne']
    linear_combination -(c.pr P) * h1 - c.pr (P ∩ Q) * hsum

/-- Credence of `A` intersected with one world. -/
theorem pr_inter_singleton (c : Credence Ω) (A : Finset Ω) (ω : Ω) :
    c.pr (A ∩ {ω}) = if ω ∈ A then c.w ω else 0 := by
  by_cases h : ω ∈ A
  · rw [if_pos h, Finset.inter_singleton_of_mem h]
    exact Finset.sum_singleton _ _
  · rw [if_neg h, Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_singleton_right.mpr h)]
    exact Finset.sum_empty

/-- Credence of one world. -/
theorem pr_singleton (c : Credence Ω) (ω : Ω) : c.pr {ω} = c.w ω :=
  Finset.sum_singleton _ _

/-- A proposition with positive credence contains a world of positive weight. -/
theorem exists_pos_of_pr_pos (c : Credence Ω) {A : Finset Ω} (hA : 0 < c.pr A) :
    ∃ ω ∈ A, 0 < c.w ω := by
  by_contra hne
  push Not at hne
  have := Finset.sum_nonpos hne
  unfold Credence.pr at hA
  linarith

/-- Fitelson's R2 from the two-ways theorem: positivity and resilience under every union of
worlds (that is, under every proposition) give C4. Case (A) is impossible; case (B) puts all
weight on `P`-worlds where `P → Q` agrees with `Q`. -/
theorem two_ways_fitelson (c : Credence Ω) (imp : Conditional Ω) (P Q : Finset Ω)
    (hpos : Positive c P Q)
    (h : ∀ S : Finset Ω, Resilient c imp P Q (S.biUnion fun ω => {ω})) :
    C4 c imp P Q := by
  have hB : ∀ i j : Ω, i ≠ j →
      Disjoint ((fun ω => ({ω} : Finset Ω)) i) ((fun ω => ({ω} : Finset Ω)) j) := by
    intro i j hij
    exact Finset.disjoint_singleton.mpr hij
  obtain ⟨a, ha, hwa⟩ := exists_pos_of_pr_pos c hpos.1
  obtain ⟨b, hb, hwb⟩ := exists_pos_of_pr_pos c hpos.2
  have haP : a ∈ P := (Finset.mem_inter.mp ha).1
  have hbP : b ∈ P := (Finset.mem_inter.mp hb).1
  have hbQ : b ∉ P ∩ Q := fun hm =>
    (Finset.mem_compl.mp (Finset.mem_inter.mp hb).2) (Finset.mem_inter.mp hm).2
  have hP : ∃ i : Ω, 0 < c.pr (P ∩ (fun ω => ({ω} : Finset Ω)) i) :=
    ⟨a, show 0 < c.pr (P ∩ {a}) by rw [pr_inter_singleton, if_pos haP]; exact hwa⟩
  rcases (two_ways c imp P Q _ hB hP).1 h with ⟨μ, hμ⟩ | ⟨l, hl⟩
  · exfalso
    have h1 : c.pr (P ∩ Q ∩ {a}) = μ * c.pr (P ∩ {a}) := (hμ a).1
    have h0 : c.pr (P ∩ Q ∩ {b}) = μ * c.pr (P ∩ {b}) := (hμ b).1
    rw [pr_inter_singleton, pr_inter_singleton, if_pos ha, if_pos haP] at h1
    rw [pr_inter_singleton, pr_inter_singleton, if_neg hbQ, if_pos hbP] at h0
    rcases mul_eq_zero.mp h0.symm with hz | hz
    · rw [hz, zero_mul] at h1
      linarith
    · linarith
  · have hl1 : l = 1 := by
      have e : c.pr {a} = l * c.pr (P ∩ {a}) := (hl a).1
      rw [pr_singleton, pr_inter_singleton, if_pos haP] at e
      have : (l - 1) * c.w a = 0 := by linear_combination -e
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hwa.ne')
    have hw : ∀ ω, c.w ω ≠ 0 → ω ∈ P ∧ (ω ∈ imp P Q ↔ ω ∈ Q) := by
      intro ω hω
      have e1 : c.pr {ω} = l * c.pr (P ∩ {ω}) := (hl ω).1
      have e2 : c.pr (imp P Q ∩ {ω}) = l * c.pr (P ∩ Q ∩ {ω}) := (hl ω).2
      rw [hl1, one_mul] at e1 e2
      rw [pr_singleton, pr_inter_singleton] at e1
      have hωP : ω ∈ P := by
        by_contra hn
        rw [if_neg hn] at e1
        exact hω e1
      refine ⟨hωP, ?_⟩
      rw [pr_inter_singleton, pr_inter_singleton] at e2
      by_cases hC : ω ∈ imp P Q <;> by_cases hQ : ω ∈ Q
      · exact iff_of_true hC hQ
      · exfalso
        rw [if_pos hC, if_neg (fun hm => hQ (Finset.mem_inter.mp hm).2)] at e2
        exact hω e2
      · exfalso
        rw [if_neg hC, if_pos (Finset.mem_inter.mpr ⟨hωP, hQ⟩)] at e2
        exact hω e2.symm
      · exact iff_of_false hC hQ
    unfold C4
    have hc : c.pr (P ∩ ((Q ∩ imp P Q) ∪ (Qᶜ ∩ (imp P Q)ᶜ)))ᶜ = 0 := by
      unfold Credence.pr
      apply Finset.sum_eq_zero
      intro ω hω
      by_contra hne
      obtain ⟨h1, h2⟩ := hw ω hne
      apply Finset.mem_compl.mp hω
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
      tauto
    have := pr_add_pr_compl c (P ∩ ((Q ∩ imp P Q) ∪ (Qᶜ ∩ (imp P Q)ᶜ)))
    linarith

end Triviality
