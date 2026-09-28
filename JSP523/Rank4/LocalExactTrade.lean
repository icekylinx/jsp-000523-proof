import JSP523.Counting.OverlapTrade

/-!
# The rank-four near-star overlap trade

These are the rank-four specializations of the all-rank trade and deficit
estimate (IV.2.2).  In the rank-four local proof they give (III.C.2).
The general arguments are in `Counting/OverlapTrade.lean`.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The missing triples from the star at `v` inside `W`. -/
def missingStarTriples (H : Family α) (W : Edge α) (v : α) : Family α :=
  (W.powersetCard 3).filter fun T => insert v T ∉ H

/-- Distinct overlapping four-edges force a missing star extension for
every fresh set `X`. -/
theorem overlapping_outside_edges_force_missing_star
    {H : Family α} {E F X : Edge α} {v : α}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEcard : E.card = 4) (hFcard : F.card = 4)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hv : v ∉ E ∪ F)
    (hX : Disjoint X (E ∪ F)) (hvX : v ∉ X) :
    insert v ((E \ F) ∪ X) ∉ H ∨
      insert v ((F \ E) ∪ X) ∉ H :=
  overlap_trade_force_missing_star hH hE hF hEcard hFcard
    hEF hShared hv hX hvX

/-- The exact missing-triple count in (III.C.2), using the available
fresh vertex set explicitly. -/
theorem overlapping_outside_edges_missing_star_count
    {H : Family α} {W E F : Edge α} {v : α}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = 4) (hFcard : F.card = 4)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    ((W \ (E ∪ F)).card).choose (3 - (E \ F).card) ≤
      (missingStarTriples H W v).card := by
  simpa only [missingStarFacets, missingStarTriples, Nat.reduceSubDiff]
    using (overlap_trade_missing_star_count hH hE hF hEsub hFsub
      hEcard hFcard hEF hShared hvW)

/-- The numerical form of the rank-four overlap bound (III.C.2). -/
theorem overlapping_outside_edges_missing_star_binomial
    {H : Family α} {W E F : Edge α} {v : α}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = 4) (hFcard : F.card = 4)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    (W.card - 4 - (E \ F).card).choose (3 - (E \ F).card) ≤
      (missingStarTriples H W v).card := by
  simpa only [missingStarFacets, missingStarTriples, Nat.reduceSubDiff]
    using (overlap_trade_missing_star_binomial hH hE hF hEsub hFsub
      hEcard hFcard hEF hShared hvW)

end JSP523.Rank4
