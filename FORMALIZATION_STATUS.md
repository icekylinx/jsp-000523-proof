# Lean formalization status

The mathematical statement and section numbers refer to [proof.pdf](paper/proof.pdf). The Lean development is partial. Its entry point, [JSP523.lean](JSP523.lean), imports every module in `JSP523/`.

| Manuscript | Established Lean interface | Current scope |
| --- | --- | --- |
| §I, common construction | `JSP523.exists_uniform_matching_floor`, `JSP523.uniform_matching_card_le_floor`, `JSP523.exists_perfect_uniform_matching`, `JSP523.exists_star_plus_matching_exact`, `JSP523.maxAvoidingCard_lower_all_rank` | A maximum outside matching of exactly `⌊(n−1)/r⌋` edges and the admissible star-plus-matching construction, for every positive rank and nonempty finite ground set. |
| Theorem I.1 | `JSP523.Coarse.coarse_bound_all_rank`, `JSP523.maxAvoidingCard_all_rank_sandwich` | The finite coarse upper bound for every `r ≥ 3`, together with the construction lower bound. |
| Threshold convention | `JSP523.forcing_threshold_exact`, `JSP523.forcing_threshold_bounds_all_rank` | The least forcing edge count equals the largest admissible size plus one, with finite construction and coarse bounds for every `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.rank_three_forcing_threshold_bounds`, `JSP523.Rank3.corollary_II_2_asymptotic`, `JSP523.Rank3.rank_three_forcing_density_tendsto_one` | Rank-three finite bounds and coefficient-one asymptotics for the extremal size and forcing threshold. |
| Theorem III.2 and §III.C.5 | `JSP523.Rank4.rank_four_near_star_theorem_III2`, `JSP523.Rank4.exists_rank_four_exceptional_equality_family` | Local rank-four theorem and both equality constructions under their explicit size and residue conditions. |
| §§III.A–III.B | `JSP523.Rank4.GlobalLeadingInterface`, `JSP523.Rank4.GlobalStabilityFinite`, `JSP523.Rank4.GlobalAsymptotic` | Finite preprocessing, deficit and stability components; final global conclusions have explicit cleanup or parameter hypotheses. |
| Lemmas IV.1.1–IV.1.2 | `JSP523.Counting.IntersectingCovers`, `JSP523.Counting.CommonPrefixTails`, `JSP523.Counting.DistancePacking` | Finite covering, common-cell and packing lemmas. |
| Theorem IV.2.1 and §IV.2.3 | `JSP523.quantitative_near_star_exact`, `JSP523.Rank5.exists_high_rank_exceptional_equality_family` | Local high-rank theorem and both equality constructions for `r ≥ 5` under explicit size, density and residue conditions. |
| §§IV.3–IV.B | `JSP523.Rank5.RegularizationAssembly`, `JSP523.Rank5.ExtractionSurplus`, `JSP523.Rank5.MultilevelCleanup`, `JSP523.Counting.PrefixAssignment` | Finite shadow, regularization, extraction, cleanup and prefix interfaces with the stated inputs. |

The centered-star admissibility criterion is `JSP523.star_plus_linear_outside_admissible`. The exceptional-pair admissibility, cardinality and unique missing facet are combined in `JSP523.exists_exceptional_pair_equality_data`; `JSP523.exists_exceptional_equality_fin` states the construction on `n` vertices. The all-rank forward normal form is `JSP523.Rank5.one_missing_equality_outside_normal_form`. The rank-specific modules expose the manuscript's specialized interfaces.

## Remaining integration

- **Rank four:** instantiate `rank_four_original_leading_bound` with the deficit, native-star, overlap, decomposition and deletion estimates of the actual preprocessing output. Instantiate the parameter-cleanup premises of `rank_four_extremal_ratio_tendsto_one` and `rank_four_stability_ratio_tendsto_zero`, then connect the resulting near-star family to `rank_four_near_star_theorem_III2`. This yields the unconditional Theorem III.1.
- **Ranks at least five:** discharge the cover and layer-loss inputs of `regularization_round_from_cover_and_layer_bound` for the actual parent family, then connect extraction to parent labels, quantitative color cleanup, inherited centers and the assigned-prefix bound at the manuscript's scales. Apply `quantitative_near_star_exact` to obtain (IV.10.2).
- **Main theorem:** assemble the rank-three theorem and the two eventual exact formulas into the statement about `maxAvoidingCard`, then use `forcing_threshold_exact` for the forcing formulation.

The local and finite interfaces should be read with their Lean hypotheses. An imported module or an abstract limit theorem is not, by itself, the unconditional global conclusion.
