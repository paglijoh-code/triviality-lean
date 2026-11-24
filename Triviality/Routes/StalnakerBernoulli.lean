/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Probability

/-!
# Route: Stalnaker–Bernoulli, truncated to `n` draws

Points are sequences `Fin n → Ω` of worlds drawn independently from a base credence `c`. "If `P`,
`Q`" is true at a sequence when the first coordinate lying in `P` lies in `Q`. If no coordinate
lies in `P`, the default `d : Bool` decides. The truncation keeps S1–S4 and denies P1, by an exact
error term.

The infinite version satisfies the Thesis for a pair of descriptive propositions and denies the
Resilient Equation. Its infinity is not what blocks triviality for one pair: the algebra generated
by `P`, `Q` and `P → Q` is finite, and `sb_finite_verdict` gives such a finite coarsening, which
keeps S1–S4 and the Thesis for the pair and fails the Resilient Equation at `¬Q`.

## Main results

* `Triviality.Routes.seqCred`: the product credence on `Fin n → Ω`.
* `Triviality.Routes.sb_pr_imp`: `Pr (sbImp n d P Q) = Pr (Q | P) (1 - q ^ n) + d q ^ n`, with
  `q = 1 - Pr P`. So P1 fails by exactly `q ^ n (d - Pr (Q | P))`.
* `Triviality.Routes.sb_p1_fails`: a concrete failure on `Fin 2` with `n = 2`, `d = false`.
* `Triviality.Routes.sb_p1_iff`: for `0 < Pr P < 1`, P1 holds iff `Pr (Q | P) = d`.
* `Triviality.Routes.sb_finite_verdict`: the finite coarsening of the infinite model.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace Routes

/-- Route Stalnaker–Bernoulli: the product weight of a sequence, `∏ i, c.w (s i)`. -/
noncomputable def seqWeight (c : Credence Ω) (n : ℕ) (s : Fin n → Ω) : ℝ := ∏ i, c.w (s i)

/-- Sum over sequences of length `n + 1` splits into first coordinate and tail. -/
theorem sum_seq_succ {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin (n + 1) → Ω) → M) :
    ∑ s, f s = ∑ ω, ∑ t : Fin n → Ω, f (Fin.cons ω t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Ω)) _ _ (fun _ => rfl)).symm

/-- Route Stalnaker–Bernoulli: the product credence on `n` independent draws from `c`. In words:
each coordinate is drawn from `c`, independently of the others. -/
noncomputable def seqCred (c : Credence Ω) (n : ℕ) : Credence (Fin n → Ω) where
  w := seqWeight c n
  nonneg s := Finset.prod_nonneg fun i _ => c.nonneg (s i)
  sum_one := by
    induction n with
    | zero => simp [seqWeight]
    | succ n ih =>
      rw [sum_seq_succ]
      simp only [seqWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [← Finset.mul_sum]
      have : ∑ t : Fin n → Ω, ∏ i, c.w (t i) = 1 := ih
      rw [this]; simp [c.sum_one]

/-- Route Stalnaker–Bernoulli: the truncated conditional holds at `s` if the first coordinate in
`P` lies in `Q`, or no coordinate lies in `P` and the default `d` is `true`. -/
def SBHolds (n : ℕ) (d : Bool) (P Q : Finset Ω) (s : Fin n → Ω) : Prop :=
  (∃ i, s i ∈ P ∧ s i ∈ Q ∧ ∀ j < i, s j ∉ P) ∨ ((∀ i, s i ∉ P) ∧ d = true)

/-- Route Stalnaker–Bernoulli: the proposition "if `P`, `Q`" on sequences of length `n`, with
default `d` when no draw lands in `P`. -/
noncomputable def sbImp (n : ℕ) (d : Bool) (P Q : Finset Ω) : Finset (Fin n → Ω) := by
  classical exact Finset.univ.filter (SBHolds n d P Q)

/-- Route Stalnaker–Bernoulli: the base proposition `A` read on sequences of length `n + 1`, as
"the first draw lies in `A`". -/
def liftSeq (n : ℕ) (A : Finset Ω) : Finset (Fin (n + 1) → Ω) :=
  Finset.univ.filter (fun s => s 0 ∈ A)

theorem sbHolds_cons {n : ℕ} (d : Bool) (P Q : Finset Ω) (ω : Ω) (t : Fin n → Ω) :
    SBHolds (n + 1) d P Q (Fin.cons ω t) ↔
      (if ω ∈ P then ω ∈ Q else SBHolds n d P Q t) := by
  unfold SBHolds
  by_cases hP : ω ∈ P
  · simp only [hP, if_true]
    constructor
    · rintro (⟨i, hi, hiq, hj⟩ | ⟨h, _⟩)
      · induction i using Fin.cases with
        | zero => simpa using hiq
        | succ k =>
          exact absurd hP (by simpa using hj 0 (Fin.succ_pos k))
      · exact absurd hP (by simpa using h 0)
    · intro hQ
      exact Or.inl ⟨0, by simpa using hP, by simpa using hQ, fun j hj => absurd hj (by simp)⟩
  · simp only [hP, if_false]
    constructor
    · rintro (⟨i, hi, hiq, hj⟩ | ⟨h, hd⟩)
      · induction i using Fin.cases with
        | zero => exact absurd (by simpa using hi) hP
        | succ k =>
          refine Or.inl ⟨k, by simpa using hi, by simpa using hiq, fun j hjk => ?_⟩
          simpa using hj j.succ (Fin.succ_lt_succ_iff.2 hjk)
      · exact Or.inr ⟨fun i => by simpa using h i.succ, hd⟩
    · rintro (⟨i, hi, hiq, hj⟩ | ⟨h, hd⟩)
      · refine Or.inl ⟨i.succ, by simpa using hi, by simpa using hiq, fun j hji => ?_⟩
        induction j using Fin.cases with
        | zero => simpa using hP
        | succ k => simpa using hj k (Fin.succ_lt_succ_iff.1 hji)
      · refine Or.inr ⟨fun i => ?_, hd⟩
        induction i using Fin.cases with
        | zero => simpa using hP
        | succ k => simpa using h k

theorem sbHolds_zero (d : Bool) (P Q : Finset Ω) (s : Fin 0 → Ω) :
    SBHolds 0 d P Q s ↔ d = true := by
  simp [SBHolds]

/-- Route Stalnaker–Bernoulli, the exact value. With `q = 1 - Pr P`, the credence of the
truncated conditional on `n` draws is `Pr (Q | P) (1 - q ^ n) + d q ^ n`, where `d` counts as `1`
for `true` and `0` for `false`. In words: with chance `1 - q ^ n` some draw lands in `P`, and then
the answer is `Pr (Q | P)`. Otherwise the default decides. -/
theorem sb_pr_imp (c : Credence Ω) (n : ℕ) (d : Bool) (P Q : Finset Ω) (hP : 0 < c.pr P) :
    (seqCred c n).pr (sbImp n d P Q) =
      c.cond Q P * (1 - (1 - c.pr P) ^ n) + (if d then 1 else 0) * (1 - c.pr P) ^ n := by
  classical
  have key : ∀ n, (seqCred c n).pr (sbImp n d P Q) =
      ∑ s : Fin n → Ω, if SBHolds n d P Q s then seqWeight c n s else 0 := by
    intro n
    unfold Credence.pr sbImp
    rw [Finset.sum_filter]
    rfl
  have hPQ : c.pr (P ∩ Q) = c.cond Q P * c.pr P := (cond_mul_pr c Q P).symm
  induction n with
  | zero =>
    rw [key]
    simp [sbHolds_zero, seqWeight]
  | succ n ih =>
    rw [key, sum_seq_succ]
    have step : ∀ ω : Ω, ∑ t : Fin n → Ω,
        (if SBHolds (n + 1) d P Q (Fin.cons ω t) then seqWeight c (n + 1) (Fin.cons ω t) else 0) =
        c.w ω * (if ω ∈ P then (if ω ∈ Q then 1 else 0)
          else ∑ t : Fin n → Ω, if SBHolds n d P Q t then seqWeight c n t else 0) := by
      intro ω
      have hw : ∀ t : Fin n → Ω, seqWeight c (n + 1) (Fin.cons ω t) = c.w ω * seqWeight c n t := by
        intro t; simp [seqWeight, Fin.prod_univ_succ]
      simp only [sbHolds_cons, hw]
      by_cases hωP : ω ∈ P
      · by_cases hωQ : ω ∈ Q
        · simp only [hωP, hωQ, ite_true]
          rw [← Finset.mul_sum]
          have : ∑ t : Fin n → Ω, seqWeight c n t = 1 := (seqCred c n).sum_one
          rw [this]
        · simp [hωP, hωQ]
      · simp only [hωP, ite_false]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp
    simp only [step]
    rw [← key n, ih]
    have h1 : ∑ ω : Ω, c.w ω * (if ω ∈ P then (if ω ∈ Q then (1 : ℝ) else 0)
          else (c.cond Q P * (1 - (1 - c.pr P) ^ n) + (if d then 1 else 0) * (1 - c.pr P) ^ n)) =
        c.pr (P ∩ Q) + (1 - c.pr P) *
          (c.cond Q P * (1 - (1 - c.pr P) ^ n) + (if d then 1 else 0) * (1 - c.pr P) ^ n) := by
      set X := c.cond Q P * (1 - (1 - c.pr P) ^ n) + (if d then 1 else 0) * (1 - c.pr P) ^ n
      have hA : ∑ ω : Ω, c.w ω * (if ω ∈ P then (if ω ∈ Q then (1 : ℝ) else 0) else X) =
          ∑ ω : Ω, ((if ω ∈ P ∩ Q then c.w ω else 0) + (if ω ∈ Pᶜ then c.w ω * X else 0)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases a : ω ∈ P <;> by_cases b : ω ∈ Q <;> simp [a, b]
      rw [hA, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.univ_inter, ← Finset.sum_mul]
      have hc : c.pr Pᶜ = 1 - c.pr P := by linarith [pr_add_pr_compl c P]
      show c.pr (P ∩ Q) + c.pr Pᶜ * X = _
      rw [hc]
    rw [h1, hPQ]
    ring

/-- Route Stalnaker–Bernoulli, P1 fails by exactly `q ^ n (d - Pr (Q | P))`: the credence of the
truncated conditional minus `Pr (Q | P)`. -/
theorem sb_pr_imp_sub_cond (c : Credence Ω) (n : ℕ) (d : Bool) (P Q : Finset Ω)
    (hP : 0 < c.pr P) :
    (seqCred c n).pr (sbImp n d P Q) - c.cond Q P =
      (1 - c.pr P) ^ n * ((if d then 1 else 0) - c.cond Q P) := by
  rw [sb_pr_imp c n d P Q hP]; ring

/-- Route Stalnaker–Bernoulli, degenerate cases: for `0 < Pr P < 1`, the truncated conditional
has credence `Pr (Q | P)` exactly when `Pr (Q | P)` equals the default (`1` for `true`, `0` for
`false`). The hypothesis `n ≥ 1` is not needed, since `q ^ 0 = 1 ≠ 0` too. -/
theorem sb_p1_iff (c : Credence Ω) (n : ℕ) (d : Bool) (P Q : Finset Ω)
    (hP : 0 < c.pr P) (hP1 : c.pr P < 1) :
    (seqCred c n).pr (sbImp n d P Q) = c.cond Q P ↔ c.cond Q P = (if d then 1 else 0) := by
  have h := sb_pr_imp_sub_cond c n d P Q hP
  have hq : (1 - c.pr P) ^ n ≠ 0 := pow_ne_zero _ (by linarith)
  constructor
  · intro e
    rw [e, sub_self] at h
    have := (mul_eq_zero.1 h.symm).resolve_left hq
    linarith
  · intro e
    rw [e, sub_self, mul_zero] at h
    rw [e]; linarith

/-- The lift of `A ∩ B` is the intersection of the lifts. -/
theorem liftSeq_inter (n : ℕ) (A B : Finset Ω) :
    liftSeq n (A ∩ B) = liftSeq n A ∩ liftSeq n B := by
  ext s; simp [liftSeq]

/-- Route Stalnaker–Bernoulli: lifting a base proposition to "the first draw lies in it" keeps its
credence. -/
theorem pr_liftSeq (c : Credence Ω) (n : ℕ) (A : Finset Ω) :
    (seqCred c (n + 1)).pr (liftSeq n A) = c.pr A := by
  unfold Credence.pr liftSeq
  rw [Finset.sum_filter, sum_seq_succ]
  simp only [seqCred, seqWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have : ∑ t : Fin n → Ω, ∏ i, c.w (t i) = 1 := (seqCred c n).sum_one
  have e : ∀ ω : Ω, ∑ t : Fin n → Ω, (if ω ∈ A then c.w ω * ∏ i, c.w (t i) else 0) =
      if ω ∈ A then c.w ω else 0 := by
    intro ω
    split_ifs
    · rw [← Finset.mul_sum, this, mul_one]
    · simp
  simp only [e]
  rw [← Finset.sum_filter]; congr 1; ext; simp

/-- Route Stalnaker–Bernoulli: the lifted conditional credence equals the base one. -/
theorem cond_liftSeq (c : Credence Ω) (n : ℕ) (P Q : Finset Ω) :
    (seqCred c (n + 1)).cond (liftSeq n Q) (liftSeq n P) = c.cond Q P := by
  unfold Credence.cond
  rw [← liftSeq_inter, pr_liftSeq, pr_liftSeq]

/-- Witness: the uniform credence on `Fin 2`. -/
noncomputable def sbCred : Credence (Fin 2) where
  w _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by simp

private theorem sbCred_pr : sbCred.pr ({0} : Finset (Fin 2)) = 1 / 2 := by
  simp [Credence.pr, sbCred]

/-- Route Stalnaker–Bernoulli, P1 fails: on `Fin 2` with the uniform credence, `P = Q = {0}`
(so `Pr P = 1/2`, `Pr (Q | P) = 1`), `n = 2` draws and default `false`, the truncated
conditional has credence `3 / 4`, not `1`. The statement is on the sequence space with the lifted
`P` and `Q`, whose conditional credence is the base value `1`. -/
theorem sb_p1_fails :
    (seqCred sbCred 2).pr (sbImp 2 false {0} {0}) = 3 / 4 ∧
    (seqCred sbCred 2).cond (liftSeq 1 {0}) (liftSeq 1 {0}) = 1 ∧
    (seqCred sbCred 2).pr (sbImp 2 false {0} {0}) ≠
      (seqCred sbCred 2).cond (liftSeq 1 {0}) (liftSeq 1 {0}) := by
  have h1 : (seqCred sbCred 2).pr (sbImp 2 false {0} {0}) = 3 / 4 := by
    rw [sb_pr_imp sbCred 2 false _ _ (by rw [sbCred_pr]; norm_num)]
    have : sbCred.cond ({0} : Finset (Fin 2)) {0} = 1 :=
      cond_eq_one_of_subset sbCred (by rw [sbCred_pr]; norm_num) subset_rfl
    rw [this, sbCred_pr]; norm_num
  have h2 : (seqCred sbCred 2).cond (liftSeq 1 {0}) (liftSeq 1 {0}) = 1 := by
    rw [cond_liftSeq]
    exact cond_eq_one_of_subset sbCred (by rw [sbCred_pr]; norm_num) subset_rfl
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]; norm_num

/-- Route Stalnaker–Bernoulli, P1 fails as a Thesis statement: any conditional `imp` on the
sequence space that returns `sbImp` at the lifted pair violates `Thesis` there. -/
theorem sb_thesis_fails (imp : Conditional (Fin 2 → Fin 2))
    (himp : imp (liftSeq 1 {0}) (liftSeq 1 {0}) = sbImp 2 false {0} {0}) :
    ¬ Thesis (seqCred sbCred 2) imp (liftSeq 1 {0}) (liftSeq 1 {0}) := by
  intro h
  have hpos : 0 < (seqCred sbCred 2).pr (liftSeq 1 {0}) := by
    rw [pr_liftSeq, sbCred_pr]; norm_num
  have := h hpos
  rw [himp] at this
  exact sb_p1_fails.2.2 this

/-! ### A finite coarsening of the infinite model

Base worlds `w1, w2, w3` with `Pr = (1/2, 1/3, 1/6)`, `P = {w1, w2}`, `Q = {w1}`. In the infinite
model `P → Q` contains the sequences starting with `w1`, excludes those starting with `w2`, and
has conditional credence `Pr (Q | P) = 3/5` on those starting with `w3`. Grouping the sequences by
first world, and splitting the third group by `P → Q`, gives four atoms of weights `1/2`, `1/3`,
`1/6 * 3/5` and `1/6 * 2/5`. -/

/-- Route Stalnaker–Bernoulli: the weights of the four atoms. -/
noncomputable def sbFinWeight : Fin 4 → ℝ := ![1/2, 1/3, 1/10, 1/15]

theorem sbFinW0 : sbFinWeight 0 = 1/2 := rfl
theorem sbFinW1 : sbFinWeight 1 = 1/3 := rfl
theorem sbFinW2 : sbFinWeight 2 = 1/10 := rfl
theorem sbFinW3 : sbFinWeight 3 = 1/15 := rfl

/-- Route Stalnaker–Bernoulli: the credence on the four atoms. -/
noncomputable def sbFinCred : Credence (Fin 4) where
  w := sbFinWeight
  nonneg p := by
    fin_cases p <;> norm_num [sbFinWeight]
  sum_one := by norm_num [Fin.sum_univ_four, sbFinW0, sbFinW1, sbFinW2, sbFinW3]

/-- Route Stalnaker–Bernoulli: the conditional of the one pair at issue, "if `w1 or w2`, `w1`",
as atoms. Constant, so it says nothing about other pairs. -/
def sbFinImp : Conditional (Fin 4) := fun _ _ => {0, 2}

theorem sb_fin_pr_eq (S : Finset (Fin 4)) : sbFinCred.pr S = ∑ p ∈ S, sbFinWeight p := rfl

/-- Route Stalnaker–Bernoulli, finite coarsening: with `P = {0, 1}` and `Q = {0}`, positivity and
the Thesis hold (both sides `3/5`), the Resilient Equation holds at `Q` and fails at `¬Q` (`1/5`
against `0`), and `Pr (Q | P) ≠ Pr Q`. The verdict has the form of `gs_verdict`. -/
theorem sb_finite_verdict :
    Positive sbFinCred {0, 1} {0} ∧
    Thesis sbFinCred sbFinImp {0, 1} {0} ∧
    Resilient sbFinCred sbFinImp {0, 1} {0} {0} ∧
    ¬ Resilient sbFinCred sbFinImp {0, 1} {0} ({0} : Finset (Fin 4))ᶜ ∧
    sbFinCred.cond {0} {0, 1} ≠ sbFinCred.pr {0} := by
  have hc : ({0} : Finset (Fin 4))ᶜ = {1, 2, 3} := by decide
  have p0 : sbFinCred.pr {0} = 1 / 2 := by
    rw [sb_fin_pr_eq, Finset.sum_singleton, sbFinW0]
  have p1 : sbFinCred.pr {1} = 1 / 3 := by
    rw [sb_fin_pr_eq, Finset.sum_singleton, sbFinW1]
  have p2 : sbFinCred.pr {2} = 1 / 10 := by
    rw [sb_fin_pr_eq, Finset.sum_singleton, sbFinW2]
  have pe : sbFinCred.pr ∅ = 0 := by rw [sb_fin_pr_eq, Finset.sum_empty]
  have p01 : sbFinCred.pr {0, 1} = 5 / 6 := by
    rw [sb_fin_pr_eq, Finset.sum_pair (by decide), sbFinW0, sbFinW1]; norm_num
  have p02 : sbFinCred.pr {0, 2} = 3 / 5 := by
    rw [sb_fin_pr_eq, Finset.sum_pair (by decide), sbFinW0, sbFinW2]; norm_num
  have p123 : sbFinCred.pr {1, 2, 3} = 1 / 2 := by
    rw [sb_fin_pr_eq, Finset.sum_insert (by decide), Finset.sum_pair (by decide),
      sbFinW1, sbFinW2, sbFinW3]
    norm_num
  have i1 : ({0, 1} : Finset (Fin 4)) ∩ {0} = {0} := by decide
  have i2 : ({0, 1} : Finset (Fin 4)) ∩ {1, 2, 3} = {1} := by decide
  have i3 : ({0} : Finset (Fin 4)) ∩ {0, 2} = {0} := by decide
  have i4 : ({1, 2, 3} : Finset (Fin 4)) ∩ {0, 2} = {2} := by decide
  have i5 : ({1} : Finset (Fin 4)) ∩ {0} = ∅ := by decide
  have i7 : ({0} : Finset (Fin 4)) ∩ {0} = {0} := by decide
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [i1, p0]; norm_num
  · rw [hc, i2, p1]; norm_num
  · intro _
    unfold Credence.cond sbFinImp
    rw [i1, p02, p0, p01]; norm_num
  · intro _
    unfold Credence.cond sbFinImp
    rw [i1, i3, i7]
  · intro h
    have hg : 0 < sbFinCred.pr (({0, 1} : Finset (Fin 4)) ∩ ({0} : Finset (Fin 4))ᶜ) := by
      rw [hc, i2, p1]; norm_num
    have e := h hg
    unfold Credence.cond sbFinImp at e
    rw [hc, i2, i4, i5, p2, pe, p123, p1] at e
    norm_num at e
  · unfold Credence.cond
    rw [i1, p0, p01]; norm_num

end Routes

end Triviality
