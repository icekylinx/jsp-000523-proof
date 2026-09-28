# JSP-000523 proof

The mathematical proof of JSP-000523 is [paper/proof.md](paper/proof.md). The author and formalization contributor is Yilin Liu; the [contribution record](CONTRIBUTIONS.md) distinguishes the two roles.

## Lean formalization

The repository contains selected, dependency-closed Lean 4 results from the proof program. The toolchain is Lean 4.34.0; Mathlib and its dependencies are pinned in [lake-manifest.json](lake-manifest.json).

| Manuscript result | Lean theorem | Scope |
| --- | --- | --- |
| Theorem I.1, coarse bound in every rank | `JSP523.Coarse.coarse_bound_all_rank` | Complete finite theorem for `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.corollary_II_2_asymptotic` | Complete rank-three upper bound and asymptotic. |
| Theorem III.2 | `JSP523.Rank4.rank_four_near_star_theorem_III2` | Complete rank-four local theorem under its explicit near-star condition. |
| Theorem IV.2.1 and its equality cases | `JSP523.quantitative_near_star_exact`, `JSP523.quantitative_local_equality_classification` | Fixed-rank local theorem for `r ≥ 5` under explicit density and size conditions. |
| Rank-four graph and colored-slot lemmas | `JSP523.Rank4.graphDeficit_marked`, `JSP523.Rank4.colored_family_payment` | Finite components of the simplified rank-four deficit argument. |

The all-rank main theorem is not yet a theorem of this Lean snapshot. In particular, the rank-four global preprocessing and deficit assembly, and the high-rank global extraction and cleanup, remain separate formalization tasks.

## Reproduce

From the repository root, with `elan` installed:

```bash
lake update
lake exe cache get
lake build JSP523
bash scripts/check_no_sorry.sh
```

`JSP523.lean` imports the selected results. The repository's GitHub Actions workflow builds them on each push and pull request.
