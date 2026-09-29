# Lean formalization status

The mathematical statement and section numbers refer to [proof.pdf](paper/proof.pdf). The Lean development is partial. Its entry point, [JSP523.lean](JSP523.lean), imports every module in `JSP523/`.

## Completion estimates

These are review estimates for the route to unconditional global Lean theorems. They measure remaining proof obligations, not file count or lines of code.

| Scope | Estimate | Established route | Main gap |
| --- | ---: | --- | --- |
| Rank three, Part II | 95% | Finite support bounds and both coefficient-one limits compile. | State the final all-rank conclusion from the rank-specific results. |
| Rank four, §§III.A–III.C | 70% | Local exact theorem, reciprocal cleanup with vanishing normalized loss, and actual mixed colored-facet payment compile. | Connect that payment and the remaining common-pair excess to the full finite global bound, then obtain unconditional stability and exactness. |
| Ranks at least five, Part IV | 60% | Local exact theorem, far-star mass, actual initial cover, fixed-round loss `o` of star size, and substantial IV.8–IV.9 cleanup lemmas compile. | Close the sharp upper-facet deletion budget and the initial positive-mass/extraction/inheritance chain with one compatible parameter choice. |
| Main all-rank theorem | 65% | Common construction, threshold convention, and rank-specific local results are available. | Assemble the unconditional rank-four and higher-rank conclusions. |

The estimates will change when a remaining global implication is discharged; a compiled conditional interface alone does not count as that implication.

| Manuscript | Established Lean interface | Current scope |
| --- | --- | --- |
| §I, common construction | `JSP523.exists_uniform_matching_floor`, `JSP523.uniform_matching_card_le_floor`, `JSP523.exists_perfect_uniform_matching`, `JSP523.exists_star_plus_matching_exact`, `JSP523.max_avoiding_card_lower_all_rank` | A maximum outside matching of exactly `⌊(n−1)/r⌋` edges and the admissible star-plus-matching construction, for every positive rank and nonempty finite ground set. |
| Theorem I.1 | `JSP523.Coarse.coarse_bound_all_rank`, `JSP523.max_avoiding_card_all_rank_sandwich` | The finite coarse upper bound for every `r ≥ 3`, together with the construction lower bound. |
| Threshold convention | `JSP523.forcing_threshold_exact`, `JSP523.forcing_threshold_bounds_all_rank` | The least forcing edge count equals the largest admissible size plus one, with finite construction and coarse bounds for every `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.rank_three_forcing_threshold_bounds`, `JSP523.Rank3.corollary_ii_2_asymptotic`, `JSP523.Rank3.rank_three_forcing_density_tendsto_one` | Rank-three finite bounds and coefficient-one asymptotics for the extremal size and forcing threshold. |
| Theorem III.2 and §III.C.5 | `JSP523.Rank4.rank_four_near_star_theorem_iii2`, `JSP523.Rank4.exists_rank_four_exceptional_equality_family` | Local rank-four theorem and both equality constructions under their explicit size and residue conditions. |
| §§III.A–III.B | `JSP523.Rank4.PreprocessReciprocalC4Asymptotic`, `JSP523.Rank4.GlobalReciprocalAsymptotic`, `JSP523.Rank4.GraphActualMixedColoredRecords`, `JSP523.Rank4.GraphActualColoredMarks`, `JSP523.Rank4.GraphActualPaymentBridge` | The actual three-stage reciprocal cleanup proves `R ≤ b`; with fixed triple-degree and label-fiber caps its loss is `o(\binom n3)`. Actual selected pair links pay the canonical rainbow-triangle and proper-`K₄` colored facets, including unique records and full-degree marks. The unconditional facet base budget `18m+3b+6m₀ ≤ 2∑d(T)²+4s` also compiles. The full finite graph-payment inequality still needs the noncolored/common-pair-excess contribution and global assembly. |
| Lemmas IV.1.1–IV.1.2 | `JSP523.Counting.IntersectingCovers`, `JSP523.Counting.CommonPrefixTails`, `JSP523.Counting.DistancePacking` | Finite covering, common-cell and packing lemmas. |
| Theorem IV.2.1 and §IV.2.3 | `JSP523.quantitative_near_star_exact`, `JSP523.Rank5.exists_high_rank_exceptional_equality_family` | Local high-rank theorem and both equality constructions for `r ≥ 5` under explicit size, density and residue conditions. |
| §§IV.3–IV.B | `JSP523.Rank5.FarStarAsymptotic`, `JSP523.Rank5.InitialCodegreeCleanup`, `JSP523.Rank5.InitialPolynomialScale`, `JSP523.Rank5.RegularizationLossAsymptotic`, `JSP523.Rank5.InheritanceLowRetention`, `JSP523.Rank5.ExtractionSurplus`, `JSP523.Rank5.MultilevelCleanup`, `JSP523.Counting.PrefixAssignment` | Fixed positive degree gaps give far-star mass; the initial high-degree cover is selected from the actual family. An explicit polynomial scale satisfies the initial separation estimates, and every fixed number of natural regularization rounds has complete explicit loss `o(\binom{n-1}{r-1})`. IV.7 retention and the genuine IV.8 partial coloring yield upper-facet color centers after actual deletion; the IV.9 facet witness lower/upper bound, low-retention budget, and natural codegree substitution compile with stated cleanup hypotheses. The upper-facet deletion bound currently uses a coarse bicolored term; its sharp three-orientation budget and the final global extraction remain open. |

The centered-star admissibility criterion is `JSP523.star_plus_linear_outside_admissible`. The exceptional-pair admissibility, cardinality and unique missing facet are combined in `JSP523.exists_exceptional_pair_equality_data`; `JSP523.exists_exceptional_equality_fin` states the construction on `n` vertices. The all-rank forward normal form is `JSP523.Rank5.one_missing_equality_outside_normal_form`. The rank-specific modules expose the manuscript's specialized interfaces.

## Remaining integration

- **Rank four:** combine the compiled mixed colored-facet payment with the complete facet classification and actual common-pair excess bound in §III.B.9. Replace the current cap on all label fibers in the reciprocal-loss theorem by the manuscript's used-pair cap, then discharge the finite upper estimate and stability premises in `GlobalReciprocalAsymptotic`. Apply `rank_four_near_star_theorem_iii2` after global stability.
- **Ranks at least five:** replace the coarse bicolored IV.8 deletion term by the repeated-color pinned budget in all three orientations; integrate the resulting actual cleanup and IV.9 incidence bounds. Choose one initial scale and show the retained far-star mass exceeds initial cleanup plus fixed-round losses, then complete extraction, inherited-center, and assigned-prefix assembly before applying `quantitative_near_star_exact`.
- **Main theorem:** assemble the rank-three theorem and the two eventual exact formulas for `maxAvoidingCard`, then use `forcing_threshold_exact` for the forcing formulation.

The local and finite interfaces should be read with their Lean hypotheses. An imported module or an abstract limit theorem is not, by itself, the unconditional global conclusion.
