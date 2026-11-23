/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Probability

/-!
# Khoo and Mandelkern's probabilistic triviality result

Seven premises: PIE for `(q, p, q)` and `(qᶜ, p, q)`, and the Thesis for `p > q`,
`(q ∧ p) > q`, `(¬q ∧ p) > q`, `q > (p > q)`, `¬q > (p > q)`. With positivity and
`Pr (q | p) ≠ Pr q` they are inconsistent (R7).

## Main results

* `Triviality.km_cond_imp_given_q`, `Triviality.km_cond_imp_given_not_q`: the two lemmas,
  `Pr (p > q | q) = 1` and `Pr (p > q | ¬q) = 0`.
* `Triviality.km_probabilistic_triviality`: R7.

The tightness countermodels (K5) and the dropped-positivity controls are in
`Triviality.Countermodels.KhooMandelkern`.

## References

* Khoo and Mandelkern, "Triviality results and the relationship between logical and natural
  languages", Mind 2019.
-/

open Finset

namespace Triviality

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Lemma 1 of R7 (Khoo and Mandelkern 2019): given `Pr(p ∧ q) > 0`, PIE for `(q, p, q)`, and the
Thesis for
`(q ∧ p) > q` and `q > (p > q)`, `Pr(p > q | q) = 1`. -/
theorem km_cond_imp_given_q (c : Credence Ω) (imp : Conditional Ω) (p q : Finset Ω)
    (hpos : 0 < c.pr (p ∩ q)) (hpie : PIE c imp q p q)
    (hbi : Thesis c imp (q ∩ p) q) (hci : Thesis c imp q (imp p q)) :
    c.cond (imp p q) q = 1 := by
  have hq : 0 < c.pr q := lt_of_lt_of_le hpos (pr_mono c Finset.inter_subset_right)
  have hqp : 0 < c.pr (q ∩ p) := by rwa [Finset.inter_comm]
  have h1 : c.cond q (q ∩ p) = 1 := by
    apply cond_eq_one_of_subset c (by rwa [Finset.inter_comm])
    exact Finset.inter_subset_left
  unfold Thesis at hbi hci
  unfold PIE at hpie
  rw [← hci hq, hpie, hbi hqp, h1]

@[deprecated (since := "2026-11-22")] alias km_L1 := km_cond_imp_given_q

/-- Lemma 2 of R7 (Khoo and Mandelkern 2019): given `Pr(p ∧ ¬q) > 0`, PIE for `(¬q, p, q)` and the
Thesis for
`(¬q ∧ p) > q` and `¬q > (p > q)`, `Pr(p > q | ¬q) = 0`. (With the guarded Thesis the positivity
is needed, to make the two Thesis instances bite.) -/
theorem km_cond_imp_given_not_q (c : Credence Ω) (imp : Conditional Ω) (p q : Finset Ω)
    (hpos : 0 < c.pr (p ∩ qᶜ)) (hpie : PIE c imp qᶜ p q)
    (hbii : Thesis c imp (qᶜ ∩ p) q) (hcii : Thesis c imp qᶜ (imp p q)) :
    c.cond (imp p q) qᶜ = 0 := by
  have hqc : 0 < c.pr qᶜ := lt_of_lt_of_le hpos (pr_mono c Finset.inter_subset_right)
  have hqcp : 0 < c.pr (qᶜ ∩ p) := by rwa [Finset.inter_comm]
  have h0 : c.cond q (qᶜ ∩ p) = 0 := by
    apply cond_eq_zero_of_disjoint
    ext x; simp; tauto
  unfold Thesis at hbii hcii
  unfold PIE at hpie
  rw [← hcii hqc, hpie, hbii hqcp, h0]

@[deprecated (since := "2026-11-22")] alias km_L2 := km_cond_imp_given_not_q

/-- R7 (Khoo and Mandelkern 2019): if `Pr(p ∧ q) > 0`, `Pr(p ∧ ¬q) > 0` and
`Pr(q | p) ≠ Pr(q)`, the two PIE instances and the five Thesis instances cannot all hold. -/
theorem km_probabilistic_triviality (c : Credence Ω) (imp : Conditional Ω) (p q : Finset Ω)
    (hpos : Positive c p q) (hne : c.cond q p ≠ c.pr q)
    (hpie1 : PIE c imp q p q) (hpie2 : PIE c imp qᶜ p q)
    (ha : Thesis c imp p q) (hbi : Thesis c imp (q ∩ p) q)
    (hbii : Thesis c imp (qᶜ ∩ p) q) (hci : Thesis c imp q (imp p q))
    (hcii : Thesis c imp qᶜ (imp p q)) : False := by
  obtain ⟨hp1, hp2⟩ := hpos
  have e1 := km_cond_imp_given_q c imp p q hp1 hpie1 hbi hci
  have e0 := km_cond_imp_given_not_q c imp p q hp2 hpie2 hbii hcii
  have := pr_eq_of_cond c q (imp p q) e1 e0
  exact hne (by
    rw [← ha (lt_of_lt_of_le hp1 (pr_mono c Finset.inter_subset_left)), this])


end Triviality
