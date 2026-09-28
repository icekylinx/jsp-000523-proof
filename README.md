# JSP-000523 proof

The mathematical proof of JSP-000523 is [paper/proof.pdf](paper/proof.pdf). The author and formalization contributor is Yilin Liu; the [contribution record](CONTRIBUTIONS.md) distinguishes the two roles.

## Lean formalization

**Status: partial; formalization is in progress.** The repository contains selected, dependency-closed Lean 4 results corresponding to parts of the manuscript. The toolchain is Lean 4.34.0; Mathlib and its dependencies are pinned in [lake-manifest.json](lake-manifest.json).

| Manuscript result | Lean theorem | Scope |
| --- | --- | --- |
| Theorem I.1, coarse bound in every rank | `JSP523.Coarse.coarse_bound_all_rank` | Finite bound for `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.corollary_II_2_asymptotic` | Rank-three support bound and extremal asymptotic. |
| Theorem III.2 | `JSP523.Rank4.rank_four_near_star_theorem_III2` | Rank-four local bound and forward equality classification under the stated near-star condition. |
| Theorem IV.2.1 and its equality cases | `JSP523.quantitative_near_star_exact`, `JSP523.quantitative_local_equality_classification`; converse constructions in `JSP523.Rank5.LocalEqualityConstruction` | Fixed-rank local bound and equality classification for `r ≥ 5` under explicit density and size conditions. |
| Rank-four graph and colored-slot lemmas | `JSP523.Rank4.graphDeficit_marked`, `JSP523.Rank4.colored_family_payment` | Finite components of the simplified rank-four deficit argument. |

The manuscript's Theorem 1, rank-four Theorem III.1, and the global argument in Part IV are not yet assembled as Lean theorems. The rank-four global preprocessing and deficit assembly, and the high-rank global extraction and cleanup, are still being formalized.

## Reproduce

From the repository root, with `elan` installed:

```bash
lake update
lake exe cache get
lake build JSP523
bash scripts/check_no_sorry.sh
```

`JSP523.lean` imports the selected results. The repository's GitHub Actions workflow builds them on each push and pull request.
