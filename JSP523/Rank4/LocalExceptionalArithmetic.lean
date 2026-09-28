import JSP523.Rank4.LocalExceptionalSets
import JSP523.Rank4.LocalExactConstants

/-!
# Exact exceptional-set bounds for the local numerical close

The generic missing-facet incidence count uses a binomial singleton
threshold.  This module proves the polynomial comparison needed to feed
that exact count into the scalar bounds of §III.C.3–4.
-/

namespace JSP523.Rank4

/-- For w at least twenty, the singleton threshold is at least w²/4. -/
theorem four_times_singleton_threshold_ge_square
    {w : ℕ} (hw : 20 ≤ w) :
    w * w ≤ 4 * ((w - 5).choose 2) := by
  have h5 : w - 5 + 5 = w := by omega
  have h6 : w - 6 + 6 = w := by omega
  have hchoose : 2 * ((w - 5).choose 2) =
      (w - 5) * (w - 6) := by
    rw [Nat.choose_two_right]
    have hPred : w - 5 - 1 = w - 6 := by omega
    rw [hPred]
    have heven : Even ((w - 5) * (w - 6)) := by
      simpa only [← hPred] using Nat.even_mul_pred_self (w - 5)
    have hCancel := Nat.div_two_mul_two_of_even heven
    nlinarith
  nlinarith

/-- The exact vertex-incidence estimate (III.C.4) supplies the simpler
polynomial premise used by the numerical close. -/
theorem near_star_exceptional_vertices_quadratic
    {α : Type*} [DecidableEq α]
    (H : Family α) (W : Edge α) (v : α)
    (hw : 20 ≤ W.card) :
    (badSingletonVertices H W v 4).card * W.card * W.card ≤
      24 * (missingStarTriples H W v).card := by
  have hSquare :=
    four_times_singleton_threshold_ge_square (w := W.card) hw
  have hIncidence := near_star_exceptional_vertices_incidence H W v
  have hMul := Nat.mul_le_mul_left
    (badSingletonVertices H W v 4).card hSquare
  change (W.card - 5).choose 2 *
    (badSingletonVertices H W v 4).card ≤
      6 * (missingStarTriples H W v).card at hIncidence
  nlinarith

/-- The numerical local close now takes only its genuinely open coarse
and refined edge-count estimates; both exceptional-set hypotheses are
discharged by the actual missing-facet incidence counts. -/
theorem rank_four_local_upper_of_edge_count_interfaces
    {α : Type*} [DecidableEq α]
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W) (hw : 1000 ≤ W.card)
    (hCoarse :
      12 * (outsideEdges H W).card ≤
        3 * W.card + 11 * (missingStarTriples H W v).card)
    (hRefined :
      (badSingletonVertices H W v 4).card = 0 →
      (nearStarBadPairs H W v).card ≤ 18 →
        4 * (outsideEdges H W).card ≤
          (missingStarTriples H W v).card + W.card + 244) :
    H.card ≤ W.card.choose 3 + W.card / 4 := by
  apply rank_four_local_upper_of_numerical_interfaces
    (d := (badSingletonVertices H W v 4).card)
    (h := (nearStarBadPairs H W v).card)
    hH hU hSupport hvW hw hCoarse
  · exact near_star_exceptional_vertices_quadratic H W v (by omega)
  · have hPair := near_star_bad_pairs_incidence H W v
    change (W.card - 6) * (nearStarBadPairs H W v).card ≤
      6 * (missingStarTriples H W v).card at hPair
    nlinarith
  · exact hRefined

end JSP523.Rank4
