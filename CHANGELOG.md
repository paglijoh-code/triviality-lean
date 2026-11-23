# Changelog

All notable changes to `triviality-lean` are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/) (before 1.0, a minor version may break the API).

## [0.1.0] - 2026-11-22

First release. Lean 4 v4.36.0, Mathlib v4.36.0.

### Added
- The setting S1–S4 (`Credence`, `Credence.pr`, `Credence.cond`, `Conditional`) and the guarded
  premises `Thesis`, `Resilient`, `PIE`, `Preservation`, `Positive`, with the conclusion `C4`.
- R1 `lewis_1976`, K1 `lewis_implies_c3`, Milne 2003 `milne_collapse`, R3
  `fitelson_three_instances`, R2 `fitelson_triviality`, R4 `fitelson_maximality`, R5
  `fitelson_ie_iff_resilient`, the 135 collapsing pairs `pair_collapse`, R7
  `km_probabilistic_triviality`, R6 `bradley_preservation` and `bradley_preservation_iff`.
- A countermodel for every premise of every result (`Triviality.Countermodels.*`).
- `thesis_iff_resilient_univ`, `pr_eq_one_of_c4`, `trivial_preservation` (the converse of R6).
- GitHub Actions CI with the Mathlib cache.

### Changed (from the pre-release research code)
- Renamed `fitelson_without_res_notq` → `milne_collapse`, `km_L1` → `km_cond_imp_given_q`,
  `km_L2` → `km_cond_imp_given_not_q`. The old names remain as deprecated aliases.
- `cond_mul_pr` no longer assumes `0 < Pr A`; `pr_eq_of_cond` no longer assumes `0 < Pr Q` or
  `0 < Pr Qᶜ` (both were redundant).
- `Lemmas.lean` is now `Probability.lean`; countermodels moved to `Triviality/Countermodels/`.

[0.1.0]: https://github.com/paglijoh-code/triviality-lean/releases/tag/v0.1.0
