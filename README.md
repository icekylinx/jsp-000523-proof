# JSP-000523 proof

The mathematical proof of JSP-000523 is [paper/proof.pdf](paper/proof.pdf). Yilin Liu is the author and Lean formalization contributor; the [contribution record](CONTRIBUTIONS.md) describes both roles.

## Lean formalization

**Status: partial; formalization is in progress.** The current review estimates are about **70% for rank four** and **60% for ranks at least five**; these describe the work toward unconditional global Lean theorems, not a count of files or lines. The [formalization status](FORMALIZATION_STATUS.md) gives the completed interfaces and remaining proof obligations. The toolchain is Lean 4.34.0; Mathlib and its dependencies are pinned in [lake-manifest.json](lake-manifest.json).

| Manuscript result | Lean theorem or module | Scope |
| --- | --- | --- |
| Common construction and extremal convention | `JSP523.exists_star_plus_matching_exact`, `JSP523.max_avoiding_card_lower_all_rank`, `JSP523.forcing_threshold_exact` | Exact star-plus-matching lower bound and least-forcing-threshold identity on finite ground sets. |
| Theorem I.1, coarse bound in every rank | `JSP523.Coarse.coarse_bound_all_rank` | Finite bound for `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.corollary_ii_2_asymptotic`, `JSP523.Rank3.rank_three_forcing_density_tendsto_one` | Rank-three support bound and coefficient-one asymptotics for the extremal size and forcing threshold. |
| Theorem III.2 and both equality forms | `JSP523.Rank4.rank_four_near_star_theorem_iii2`, `JSP523.Rank4.exists_rank_four_exceptional_equality_family` | Local bound, equality classification and exceptional construction under their explicit size and residue conditions. |
| Lemma IV.1.1, intersecting covers | `JSP523.intersecting_vertex_cover`, `JSP523.intersecting_pair_cover`, `JSP523.intersecting_common_pair_cover` | Finite vertex-star and pair-star covers in `JSP523.Counting.IntersectingCovers`. |
| Common cells and (IV.1.1)–(IV.1.3) | `JSP523.common_prefix_tails_intersecting`, `JSP523.common_prefix_tails_fiber_le_parent_degree`, `JSP523.common_prefix_tails_card_le_vertex_degree`, `JSP523.common_prefix_tails_card_le_pair_degree_no_center` | Crossed-completion obstruction and parent-codegree bounds in `JSP523.Counting.CommonPrefixTails`. |
| Lemma IV.1.2, distance packing | `JSP523.distance_packing_at_most_one`, `JSP523.distance_packing_choose_bound` | Finite distance-packing count for all `t,d`. |
| Theorem IV.2.1 and its equality cases | `JSP523.quantitative_near_star_exact`, `JSP523.quantitative_local_equality_classification`, `JSP523.Rank5.exists_high_rank_exceptional_equality_family` | Fixed-rank local bound, classification and exceptional construction for `r ≥ 5` under explicit conditions. |
| Equality construction shared by ranks four and above | `JSP523.star_plus_linear_outside_admissible`, `JSP523.one_missing_star_exceptional_pair_admissible`, `JSP523.exists_exceptional_equality_family` | Shared admissibility, cardinality and residue-class existence proofs. |
| Rank-four graph and colored-facet payment | `JSP523.Rank4.GraphActualMixedColoredRecords`, `JSP523.Rank4.GraphActualColoredMarks`, `JSP523.Rank4.GraphActualColoredFamilyPayment` | Actual selected pair links pay mixed rainbow-triangle and proper-`K₄` records and full-degree marks for finite canonical facet families. |
| Rank-four reciprocal cleanup and global interfaces | `JSP523.Rank4.PreprocessReciprocalC4Asymptotic`, `JSP523.Rank4.GlobalReciprocalAsymptotic`, `JSP523.Rank4.GraphActualPaymentBridge`, `JSP523.Rank4.GlobalActualMaster` | Actual three-stage cleanup has loss `o(\binom n3)` under fixed degree and label-fiber caps; the global finite payment and stability interfaces retain hypotheses. |
| Higher-rank regularization and inheritance | `JSP523.Rank5.FarStarAsymptotic`, `JSP523.Rank5.InitialPolynomialScale`, `JSP523.Rank5.RegularizationLossAsymptotic`, `JSP523.Rank5.InheritanceLowRetention` | Positive far-star mass from a fixed gap, an explicit polynomial initial scale, fixed-round regularization loss `o(\binom{n-1}{r-1})`, and actual lower/upper facet cleanup interfaces. |

The manuscript's Theorem 1, rank-four Theorem III.1, and the global argument in Part IV are not yet assembled as unconditional Lean theorems. See the status page for the exact remaining inputs.

## Reproduce

From the repository root, with `elan` installed:

```bash
lake exe cache get
lake build JSP523
bash scripts/check_no_sorry.sh
```

`JSP523.lean` imports the migrated finite modules. The repository's GitHub Actions workflow builds them on each push and pull request.
