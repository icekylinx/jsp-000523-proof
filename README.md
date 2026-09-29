# JSP-000523 proof

The mathematical paper is [paper/proof.pdf](paper/proof.pdf). Yilin Liu is the mathematical author and Lean formalization contributor; [CONTRIBUTIONS.md](CONTRIBUTIONS.md) records the contributions and AI use.

## Lean formalization

The main theorem, its forcing-threshold form, the rank-four stability theorem, and the eventual equality classifications have unconditional Lean proofs. [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) lists the principal interfaces. The toolchain is Lean 4.34.0, with Mathlib dependencies pinned in [lake-manifest.json](lake-manifest.json).

| Paper result | Lean interface |
| --- | --- |
| Common construction and finite coarse bound | `JSP523.exists_star_plus_matching_exact`, `JSP523.Coarse.coarse_bound_all_rank` |
| Rank-three finite bound and asymptotics | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.rank_three_forcing_density_tendsto_one` |
| Rank-four stability, exact formula, and equality forms | `JSP523.Rank4.rank_four_actual_near_extremal_outside_tendsto_zero`, `JSP523.Rank4.eventually_rank_four_extremal_exact`, `JSP523.Rank4.eventually_rank_four_extremal_equality_iff` |
| Every fixed rank at least five | `JSP523.Rank5.eventually_rank_at_least_five_extremal_exact`, `JSP523.Rank5.eventually_rank_at_least_five_extremal_classification` |
| All-rank main theorem and coefficient-one forcing asymptotic | `JSP523.jsp_000523_main_theorem`, `JSP523.coefficient_one_forcing_density` |

## Build

From the repository root, with `elan` installed:

```bash
lake exe cache get
lake build JSP523
bash scripts/check_no_sorry.sh
```

`JSP523.lean` imports every module in `JSP523/`. GitHub Actions builds this entry point on each push and pull request.
