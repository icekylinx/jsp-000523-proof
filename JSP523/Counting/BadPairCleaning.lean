import JSP523.Counting.BadSetIncidence
import JSP523.Counting.DistancePacking

/-!
# Exact tail counts for the bad-pair deletion step

These are the finite binomial forms of the first two tail counts in
§IV.2.1 of `paper/proof.pdf`.  The hypotheses `hDistance`
are the geometric conclusions to be supplied when tails are extracted from
outside edges: distance at least three for a single bad pair, and at least
two for a fixed pair of disjoint bad pairs.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- For a fixed bad pair, tails of size `r - 2` that are mutually at
distance at least three have this exact finite bound. The factor
`choose (r - 2) (r - 4)` counts the `(r - 4)`-subsets used in packing. -/
theorem fixed_bad_pair_tail_count
    {W : Edge α} {T : Family α} {r : ℕ}
    (hr : 5 ≤ r)
    (hW : ∀ A ∈ T, A ⊆ W)
    (hU : Uniform (r - 2) T)
    (hDistance : ∀ ⦃A B : Edge α⦄, A ∈ T → B ∈ T → A ≠ B →
      3 ≤ (A \ B).card) :
    T.card * (r - 2).choose (r - 4) ≤ W.card.choose (r - 4) := by
  have hdt : 3 ≤ r - 2 := by omega
  have h := distance_packing_choose_bound hW hU hDistance hdt
  have hk : (r - 2) - 3 + 1 = r - 4 := by omega
  simpa only [hk] using h

/-- For two fixed disjoint bad pairs, tails of size `r - 4` at mutual
distance at least two satisfy the exact finite packing bound. -/
theorem fixed_two_bad_pairs_tail_count
    {W : Edge α} {T : Family α} {r : ℕ}
    (hr : 6 ≤ r)
    (hW : ∀ A ∈ T, A ⊆ W)
    (hU : Uniform (r - 4) T)
    (hDistance : ∀ ⦃A B : Edge α⦄, A ∈ T → B ∈ T → A ≠ B →
      2 ≤ (A \ B).card) :
    T.card * (r - 4).choose (r - 5) ≤ W.card.choose (r - 5) := by
  have hdt : 2 ≤ r - 4 := by omega
  have h := distance_packing_choose_bound hW hU hDistance hdt
  have hk : (r - 4) - 2 + 1 = r - 5 := by omega
  simpa only [hk] using h

/-- The endpoint case `r = 5` of the two-disjoint-pair count: tails have
size one and distance at least two, so there is at most one. -/
theorem fixed_two_bad_pairs_tail_count_rank_five
    {W : Edge α} {T : Family α}
    (hU : Uniform 1 T)
    (hDistance : ∀ ⦃A B : Edge α⦄, A ∈ T → B ∈ T → A ≠ B →
      2 ≤ (A \ B).card) :
    T.card ≤ 1 := by
  exact distance_packing_at_most_one (_W := W) hU hDistance (by omega)

end JSP523
