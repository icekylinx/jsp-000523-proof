# Lean formalization status

The mathematical statement and section numbers refer to [proof.pdf](paper/proof.pdf). The Lean development is partial. Its entry point, [JSP523.lean](JSP523.lean), imports every module in `JSP523/`.

| Manuscript | Established Lean interface | Current scope |
| --- | --- | --- |
| §I, common construction | `JSP523.exists_uniform_matching_floor`, `JSP523.uniform_matching_card_le_floor`, `JSP523.exists_perfect_uniform_matching`, `JSP523.exists_star_plus_matching_exact`, `JSP523.max_avoiding_card_lower_all_rank` | A maximum outside matching of exactly `⌊(n−1)/r⌋` edges and the admissible star-plus-matching construction, for every positive rank and nonempty finite ground set. |
| Theorem I.1 | `JSP523.Coarse.coarse_bound_all_rank`, `JSP523.max_avoiding_card_all_rank_sandwich` | The finite coarse upper bound for every `r ≥ 3`, together with the construction lower bound. |
| Threshold convention | `JSP523.forcing_threshold_exact`, `JSP523.forcing_threshold_bounds_all_rank` | The least forcing edge count equals the largest admissible size plus one, with finite construction and coarse bounds for every `r ≥ 3`. |
| Theorem II.1 and Corollary II.2 | `JSP523.Rank3.rank_three_part_ii_theorem`, `JSP523.Rank3.rank_three_forcing_threshold_bounds`, `JSP523.Rank3.corollary_ii_2_asymptotic`, `JSP523.Rank3.rank_three_forcing_density_tendsto_one` | Rank-three finite bounds and coefficient-one asymptotics for the extremal size and forcing threshold. |
| Theorem III.2 and §III.C.5 | `JSP523.Rank4.rank_four_near_star_theorem_iii2`, `JSP523.Rank4.exists_rank_four_exceptional_equality_family` | Local rank-four theorem and both equality constructions under their explicit size and residue conditions. |
| §§III.A–III.B | `JSP523.Rank4.PreprocessReciprocalAssembly`, `JSP523.Rank4.GraphActualColoredMultiplicity`, `JSP523.Rank4.GraphActualPaymentBridge`, `JSP523.Rank4.GlobalActualMaster` | Actual three-stage reciprocal cleanup proves `R ≤ b` for its survivor; colored slots have common-neighbor multiplicity at most two. The facet budget `18m+3b+6m₀ ≤ 2∑d(T)²+4s` is unconditional. The full graph payment and quantitative cleanup losses remain open. |
| Lemmas IV.1.1–IV.1.2 | `JSP523.Counting.IntersectingCovers`, `JSP523.Counting.CommonPrefixTails`, `JSP523.Counting.DistancePacking` | Finite covering, common-cell and packing lemmas. |
| Theorem IV.2.1 and §IV.2.3 | `JSP523.quantitative_near_star_exact`, `JSP523.Rank5.exists_high_rank_exceptional_equality_family` | Local high-rank theorem and both equality constructions for `r ≥ 5` under explicit size, density and residue conditions. |
| §§IV.3–IV.B | `JSP523.Rank5.ShadowPowerGeneral`, `JSP523.Rank5.FarStarAsymptotic`, `JSP523.Rank5.InitialCodegreeCleanup`, `JSP523.Rank5.InheritanceWitness`, `JSP523.Rank5.InheritanceLowRetention`, `JSP523.Rank5.ExtractionSurplus`, `JSP523.Rank5.MultilevelCleanup`, `JSP523.Counting.PrefixAssignment` | Actual finite shadow allocation, far-star positive-mass estimate, `h₀²=o(n)`, and first natural regularization round. The facet case of IV.9.3 has a genuine weighted lower/upper witness count under explicit IV.7–IV.8 retention and color conditions; low-retention four-face incidences have a finite budget. Constant selection, later regularization rounds, remaining bad-incidence cases and the final extraction chain remain open. |

The centered-star admissibility criterion is `JSP523.star_plus_linear_outside_admissible`. The exceptional-pair admissibility, cardinality and unique missing facet are combined in `JSP523.exists_exceptional_pair_equality_data`; `JSP523.exists_exceptional_equality_fin` states the construction on `n` vertices. The all-rank forward normal form is `JSP523.Rank5.one_missing_equality_outside_normal_form`. The rank-specific modules expose the manuscript's specialized interfaces.

## Remaining integration

- **Rank four:** prove the full actual graph-payment inequality of §III.B.9, bound the used-parent separation cleanup losses at the manuscript's scale, and discharge the remaining asymptotic parameter premises. Apply the local theorem `rank_four_near_star_theorem_iii2` after global stability.
- **Ranks at least five:** derive the fixed far-star constants from the real density gap and the chosen `h₀` scale; connect later regularization rounds and the remaining IV.9 bad-incidence cases to actual cleanup. Complete the extraction, inherited-center and assigned-prefix chain before applying `quantitative_near_star_exact`.
- **Main theorem:** assemble the rank-three theorem and the two eventual exact formulas for `maxAvoidingCard`, then use `forcing_threshold_exact` for the forcing formulation.

The local and finite interfaces should be read with their Lean hypotheses. An imported module or an abstract limit theorem is not, by itself, the unconditional global conclusion.
