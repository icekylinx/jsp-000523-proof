import JSP523.Counting.BadSetIncidence

/-!
# Exceptional vertices and pairs in the rank-four near-star argument

This specializes the generic high-multiplicity missing-facet count to the
sets `D` and the bad pairs of §III.C.2. It supplies the exceptional-count
inputs used by the numerical close in `LocalExactConstants.lean`.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- A pair is exceptional when it lies in at least half of the
`w - 6` missing-triple completions. -/
def nearStarBadPairs (H : Family α) (W : Edge α) (v : α) : Family α :=
  badMissingSets H W v 4 2 (W.card - 6)

/-- Incidence bound for the exceptional vertices `D` from §III.C.2. -/
theorem near_star_exceptional_vertices_incidence
    (H : Family α) (W : Edge α) (v : α) :
    (W.card - 5).choose 2 * (badSingletonVertices H W v 4).card ≤
      6 * (missingStarFacets H W v 4).card := by
  have h := bad_singleton_vertices_card_bound H W v 4
  simpa only [Nat.sub_sub] using h

/-- Incidence bound (III.C.5) for exceptional pairs. -/
theorem near_star_bad_pairs_incidence
    (H : Family α) (W : Edge α) (v : α) :
    (W.card - 6) * (nearStarBadPairs H W v).card ≤
      6 * (missingStarFacets H W v 4).card := by
  unfold nearStarBadPairs
  have h := bad_missing_sets_card_bound H W v 4 2 (W.card - 6)
  norm_num at h ⊢
  exact h

/-- In the coarse extremal range there are at most eighteen exceptional
pairs. The exceptional vertex incidence estimate remains available above
in its exact binomial form. -/
theorem near_star_exceptional_sets_small
    (H : Family α) (W : Edge α) (v : α)
    (hw : 1000 ≤ W.card)
    (hq : (missingStarFacets H W v 4).card ≤ 3 * W.card) :
    (nearStarBadPairs H W v).card ≤ 18 := by
  have hpairs := near_star_bad_pairs_incidence H W v
  have hpairs18 : (nearStarBadPairs H W v).card ≤ 18 := by
    by_contra hlarge
    have h19 : 19 ≤ (nearStarBadPairs H W v).card := by omega
    have := Nat.mul_le_mul_right (W.card - 6) h19
    have hStrict : 18 * W.card < 19 * (W.card - 6) := by omega
    have hq' : 6 * (missingStarFacets H W v 4).card ≤
        18 * W.card := by nlinarith [hq]
    nlinarith [this, hpairs, hq]
  exact hpairs18

/-- The exact singleton incidence inequality already forces the exceptional
vertex set to be empty once `q ≤ 3w` and `w ≥ 1000`. -/
theorem near_star_no_exceptional_vertices
    (H : Family α) (W : Edge α) (v : α)
    (hw : 1000 ≤ W.card)
    (hq : (missingStarFacets H W v 4).card ≤ 3 * W.card) :
    badSingletonVertices H W v 4 = ∅ := by
  have hverts := near_star_exceptional_vertices_incidence H W v
  have hDzero : (badSingletonVertices H W v 4).card = 0 := by
    by_contra hne
    have hDpos : 1 ≤ (badSingletonVertices H W v 4).card := by omega
    have hx6 : W.card - 5 - 1 = W.card - 6 := by omega
    have hprod : 36 * W.card + 2 ≤
        (W.card - 5) * (W.card - 6) := by
      have hx : 995 ≤ W.card - 5 := by omega
      have hx' : W.card - 5 + 5 = W.card := by omega
      have hmul := Nat.mul_le_mul_right (W.card - 6) hx
      omega
    have hchoose : 18 * W.card + 1 ≤ (W.card - 5).choose 2 := by
      rw [Nat.choose_two_right, hx6]
      omega
    have hq' : 6 * (missingStarFacets H W v 4).card ≤ 18 * W.card := by
      nlinarith [hq]
    have hleft : (W.card - 5).choose 2 ≤
        (W.card - 5).choose 2 * (badSingletonVertices H W v 4).card := by
      nlinarith
    omega
  exact Finset.card_eq_zero.mp hDzero

/-- The full exceptional-set conclusion in the coarse extremal range. -/
theorem near_star_exceptional_counts
    (H : Family α) (W : Edge α) (v : α)
    (hw : 1000 ≤ W.card)
    (hq : (missingStarFacets H W v 4).card ≤ 3 * W.card) :
    badSingletonVertices H W v 4 = ∅ ∧
      (nearStarBadPairs H W v).card ≤ 18 := by
  exact ⟨near_star_no_exceptional_vertices H W v hw hq,
    near_star_exceptional_sets_small H W v hw hq⟩

end JSP523.Rank4
