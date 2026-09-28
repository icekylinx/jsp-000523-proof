# JSP-000523 proof

The mathematical proof of JSP-000523 is [paper/proof.pdf](paper/proof.pdf). The author and formalization contributor is Yilin Liu; the [contribution record](CONTRIBUTIONS.md) distinguishes the two roles.

## Lean formalization

**Status: partial; formalization is in progress.** The repository contains the finite Lean modules for Parts I–IV, including global interfaces with explicit hypotheses. The toolchain is Lean 4.34.0; Mathlib and its dependencies are pinned in [lake-manifest.json](lake-manifest.json).

| Manuscript result | Lean theorem or module | Scope |
| --- | --- | --- |
| Theorem I.1, coarse bound in every rank | `JSP523.Coarse.coarse_bound_all_rank` | Finite bound for `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.corollary_II_2_asymptotic` | Rank-three support bound and extremal asymptotic. |
| Theorem III.2 | `JSP523.Rank4.rank_four_near_star_theorem_III2` | Rank-four local bound and forward equality classification under the stated near-star condition. |
| Lemma IV.1.1, intersecting covers | `JSP523.intersecting_vertex_cover`, `JSP523.intersecting_pair_cover`, `JSP523.intersecting_common_pair_cover` | Finite vertex-star and pair-star covers in `JSP523.Counting.IntersectingCovers`. |
| Common cells and (IV.1.1)–(IV.1.3) | `JSP523.commonPrefixTails_intersecting`, `JSP523.commonPrefixTails_fiber_le_parent_degree`, `JSP523.commonPrefixTails_card_le_vertex_degree`, `JSP523.commonPrefixTails_card_le_pair_degree_no_center` | Crossed-completion obstruction and parent-codegree bounds in `JSP523.Counting.CommonPrefixTails`. |
| Lemma IV.1.2, distance packing | `JSP523.distance_packing_at_most_one`, `JSP523.distance_packing_choose_bound` | Finite distance-packing count for all `t,d`. |
| Theorem IV.2.1 and its equality cases | `JSP523.quantitative_near_star_exact`, `JSP523.quantitative_local_equality_classification`; converse constructions in `JSP523.Rank5.LocalEqualityConstruction` | Fixed-rank local bound and equality classification for `r ≥ 5` under explicit density and size conditions. |
| Rank-four graph and colored-slot lemmas | `JSP523.Rank4.graphDeficit_marked`, `JSP523.Rank4.colored_family_payment` | Finite components of the simplified rank-four deficit argument. |
| Rank-four global interfaces | `JSP523.Rank4.GlobalAsymptotic`, `JSP523.Rank4.GlobalStabilityFinite`, and the preprocessing, native-ledger, and shared-budget modules | Finite conditional interfaces for §III.A–§III.B. |
| Higher-rank global interfaces | `JSP523.Rank5.ShadowAllocation`, `JSP523.Rank5.RegularizationAssembly`, `JSP523.Rank5.ExtractionSurplus`, `JSP523.Rank5.ColorRigidity`, `JSP523.Rank5.MultilevelCleanup`, `JSP523.Counting.PrefixAssignment` | Finite components of §§IV.3–IV.B, with their stated hypotheses. |

The manuscript's Theorem 1, rank-four Theorem III.1, and the global argument in Part IV are not yet assembled as unconditional Lean theorems. The rank-four preprocessing and aggregate deficit, and the higher-rank regularization, extraction, and cleanup, retain explicit inputs.

## Reproduce

From the repository root, with `elan` installed:

```bash
lake update
lake exe cache get
lake build JSP523
bash scripts/check_no_sorry.sh
```

`JSP523.lean` imports the migrated finite modules. The repository's GitHub Actions workflow builds them on each push and pull request.
