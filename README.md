# triviality-lean

Machine-checked Lewisian triviality results in Lean 4 and Mathlib.

Lewis (1976) showed that if the probability of a conditional always equals the matching
conditional probability, and this keeps holding after learning, then credences become trivial.
Later results sharpened the premises: Milne (2003) needed only one extra conditioning, Fitelson
(2015) characterized exactly when resilience collapses, Bradley (2000) gave a qualitative
version, and Khoo and Mandelkern (2019) traced the family to Import-Export. This library proves
these results in one setting, with every premise named and guarded, and gives a finite
countermodel for each premise, showing it cannot be dropped. Together they form a *premise
lattice*: for any proposed escape route, you can ask which premise it gives up.

The two-instance collapse is Milne 2003. The lattice's contribution is that it is checked,
including an exact characterization of the 135 pairs of resilience instances that collapse
(`pair_collapse`).

From v0.2.0 the library also asks which evidence is safe for a conditional. Let the learnable
evidence be every union of cells of a partition. The *two-ways theorem* (`two_ways`) says that
the Resilient Equation holds under all of it iff one of two irrelevances holds: (A) the cells are
irrelevant to `P → Q`, and to `Q` given `P`, with one common rate; or (B) the cells are irrelevant to `P`, and each cell
satisfies the Resilient Equation. We know of no systematic treatment of that question in the
triviality literature, though we have not been able to read every source. The algebra is
classical, an analogous dichotomy is known in epidemiology (Geng, Guo and Fung 2002), and for
local readings of conditionals Zhao (2015) notes the two irrelevances as sufficient for agreement
with the Thesis.

## The setting (S1–S4)

| | Assumption | Lean |
|---|---|---|
| S1 | Worlds form a finite type; propositions are sets of worlds. | `Ω` with `[Fintype Ω]`, `Finset Ω` |
| S2 | Credence is a probability mass function; `Pr(B \| A) = Pr(A ∧ B) / Pr(A)`. | `Credence`, `Credence.pr`, `Credence.cond` |
| S3 | The conditional is a proposition: an arbitrary binary operation, with no logical axioms. | `Conditional Ω` |
| S4 | One credence function at a time (only R5 and R6 quantify more widely). | a single `c : Credence Ω` |

Every premise that mentions a conditional probability is guarded by the positivity of what is
conditioned on, so Lean's convention `x / 0 = 0` adds no hidden constraint.

## Premises and results

Premises: `Thesis` (the Equation, P1), `Resilient … X` (the Resilient Equation under `X`, P2[X]),
`PIE` (probabilistic Import-Export), `Preservation`, `Positive` (`Pr(P ∧ Q) > 0` and
`Pr(P ∧ ¬Q) > 0`). The conclusion `C4` is Fitelson's collapse,
`Pr(P ∧ (Q ↔ (P → Q))) = 1`.

| Result | Theorem | Premises (each one needed) | Conclusion |
|---|---|---|---|
| R1 Lewis 1976 | `lewis_1976` | Positive, P1, P2[Q], P2[¬Q] | `Pr(Q \| P) = Pr Q` |
| K1 | `lewis_implies_c3` | Positive, P2[Q], P2[¬Q] | `Pr(P → Q) = Pr Q` |
| Milne 2003 | `milne_collapse` | Positive, P1, P2[P ⊃ Q] | C4 |
| R3 Fitelson | `fitelson_three_instances` | Milne's set plus P2[¬Q] (redundant) | C4 |
| R2 Fitelson | `fitelson_triviality` | Positive | (∀ X, P2[X]) ↔ C4 |
| R4 | `fitelson_maximality` | Positive, P1, P2[P ⊃ Q] | ∀ X, P2[X] |
| Pairs | `pair_collapse` | Positive, P2[X], P2[Y] for the 135 collapsing shapes | C4 |
| R5 Fitelson | `fitelson_ie_iff_resilient` | P1 for all A, B | (∀ X, PIE) ↔ (∀ X, P2[X]) |
| R6 Bradley | `bradley_preservation_iff` | — | Preservation for every credence ↔ the conditional is trivial |
| R7 Khoo–Mandelkern | `km_probabilistic_triviality` | Positive, 2 PIE and 5 P1 instances, `Pr(q \| p) ≠ Pr q` | `False` |
| Per-instance R5 | `pie_iff_resilient` | P1 for (X, P → Q) and (X ∧ P, Q), `Pr(X ∧ P) > 0` | PIE ↔ P2[X] (the step is Fitelson's) |
| Two ways | `two_ways` | some cell meets `P` with positive credence | (P2 under every union of cells) ↔ (A) or (B) |
| Lewis, Fitelson from two ways | `two_ways_lewis`, `two_ways_fitelson` | Positive, P2 under every union of `{Q, ¬Q}`, or of worlds | `Pr(Q \| P) = Pr Q`, or C4 |

The countermodels live in `Triviality.Countermodels.*`, named `*_drop_<premise>`. Two caveats:
the countermodels that drop half of positivity are degenerate (a guard fails and the
conditional is constant), and R5's hypothesis "the Thesis for every A, B" holds only for
few-valued credences, so R5 is narrow.

## Route models

`Triviality.Routes.*` holds finite models of theories that escape the results, and shows which
premise each gives up.

| Module | Main theorem | What it shows |
|---|---|---|
| `GoldsteinSantorio` | `gs_verdict` | a three-world path model keeps S1–S4 and P1 for a pair, and fails P2[¬Q] |
| `StalnakerBernoulli` | `sb_p1_iff`, `sb_finite_verdict` | truncated sequences deny P1; a finite coarsening of the infinite model keeps P1 for a pair and fails P2[¬Q] |
| `SequenceSemantics` | `resilient_centred`, `resilient_conditional`, `not_resilient_or` | for centred conditionals: resilience compares rates on and off `P`; learning the conditional is safe given the Thesis, for a nondegenerate pair, learning `P ∨ (P → Q)` is not |

Each route model concerns one antecedent–consequent pair unless it says otherwise. The theories'
general theorems are not formalized.

## Usage

```lean
import Triviality

open Triviality

/-- Milne's two premises force the antecedent to be certain. -/
example {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (c : Credence Ω) (imp : Conditional Ω)
    (P Q : Finset Ω) (hpos : Positive c P Q) (hT : Thesis c imp P Q)
    (hX : Resilient c imp P Q (Pᶜ ∪ Q)) : c.pr P = 1 :=
  pr_eq_one_of_c4 (milne_collapse c imp P Q hpos hT hX)
```

To depend on it, add to your `lakefile.toml`:

```toml
[[require]]
name = "triviality"
git = "https://github.com/paglijoh-code/triviality-lean"
rev = "v0.2.0"
```

## Building

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get && lake build
```

CI builds the library on every push and rejects `sorry`, `axiom`, `native_decide`,
`implemented_by` and `@[extern]`.

## Layout

| Path | What it is |
|---|---|
| `Triviality/` | the library (stable API from v0.1.0) |
| `Triviality/Countermodels/` | the lattice's negative controls (stable names) |
| `Triviality/Routes/` | finite models of escape routes |

## Credit

- David Lewis, "Probabilities of Conditionals and Conditional Probabilities", *Philosophical
  Review* 85(3), 1976, 297–315.
- Peter Milne, "The Simplest Lewis-Style Triviality Proof Yet?", *Analysis* 63(4), 2003,
  300–303.
- Branden Fitelson, "The Strongest Possible Lewisian Triviality Result", *Thought* 4(2), 2015,
  69–74.
- Justin Khoo and Matthew Mandelkern, "Triviality Results and the Relationship between Logical
  and Natural Languages", *Mind* 128(510), 2019, 485–526.
- Richard Bradley, "A Preservation Condition for Conditionals", *Analysis* 60(3), 2000, 219–222,
  as restated in Mandelkern and Khoo, "Against Preservation", *Analysis* 79(3), 2019.
- Simon Goldstein and Paolo Santorio, "Probability for Epistemic Modalities", *Philosophers'
  Imprint* 21(33), 2021.
- C. Dorr and M. Mandelkern, "Sequence and Consequence", arXiv:2411.16994, 2024.
- Z. Geng, J. Guo and W.-K. Fung, "Criteria for Confounders in Epidemiological Studies", *Journal
  of the Royal Statistical Society B* 64(1), 2002, 3–15.
- M. Zhao, "Intervention and the Probabilities of Indicative Conditionals", *Journal of
  Philosophy* 112(9), 2015, 477–503.
- [linglib](https://github.com/linglib-community/linglib), whose Lean statements of Lewis 1976
  and Milne 2003 we cross-checked against ours. linglib is not a dependency.

## License

Apache-2.0, the same as Mathlib. See `LICENSE`.
