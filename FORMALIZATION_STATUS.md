# Lean formalization status

The statements and section numbers refer to [paper/proof.pdf](paper/proof.pdf). The main mathematical conclusions have unconditional Lean proofs, assembled in [JSP523/MainTheorem.lean](JSP523/MainTheorem.lean).

| Paper result | Principal Lean theorem | Scope |
| --- | --- | --- |
| Theorem I.1 | `JSP523.Coarse.coarse_bound_all_rank` | Finite self-contained coarse bound for every rank at least three. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.corollary_ii_2_asymptotic` | Rank-three finite upper bound and coefficient-one density. |
| Theorem III.1, stability | `JSP523.Rank4.rank_four_actual_near_extremal_outside_tendsto_zero` | For any admissible four-uniform sequence with star deficit `o(n³)`, the number of edges outside one original-family center is `o(n³)`. |
| Theorem III.1, exactness and equality | `JSP523.Rank4.eventually_rank_four_extremal_exact`, `JSP523.Rank4.eventually_rank_four_extremal_equality_iff` | Exact eventual maximum and both equality forms, without preprocessing assumptions. |
| Theorem IV.2.1 and Part IV | `JSP523.Rank5.eventually_rank_at_least_five_extremal_exact`, `JSP523.Rank5.eventually_rank_at_least_five_extremal_classification` | Exact eventual maximum and equality classification for every fixed rank at least five. |
| Theorem 1 | `JSP523.jsp_000523_main_theorem`, `JSP523.eventually_fixed_rank_at_least_four_forcing_exact`, `JSP523.coefficient_one_forcing_density` | Rank-three finite bound; exact formula and least forcing threshold for every fixed rank at least four; coefficient-one forcing asymptotic for every fixed rank at least three. |

The rank-four global route uses an actual initial cover, owner assignment, original-family loss, regularization, reciprocal cleanup, and a single master budget. The initial loss and star/core overlap are `o(n³)`; the master error is arbitrarily small after cubic normalization. The near-extremal stability proof permits a vanishing cubic deficit below the complete-star size. The higher-rank global route closes the finite cleanup and inherited-center estimates before invoking the quantitative local theorem.

The entry point [JSP523.lean](JSP523.lean) imports every module. Run `lake build JSP523` to check the full development.
