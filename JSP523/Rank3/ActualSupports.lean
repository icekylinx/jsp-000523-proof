import JSP523.Rank3.SupportLedger

/-!
# Actual finite supports of a triple system

`usedPairs` is the set of pairs contained in an edge.  `usedCells` is the
set of two-point cells whose common link contains a pair: the same pair
completes to an edge through each cell vertex.  These are the actual sets
counted by the rank-three support inequality, rather than free cardinal
parameters.  Proving the support inequality from admissibility remains a
separate structural task.
-/

namespace JSP523.Rank3

section Supports

variable {α : Type*} [DecidableEq α]

/-- Pair support on the chosen finite vertex set. -/
def usedPairs (H : Family α) (V : Finset α) : Family α := by
  exact (V.powersetCard 2).filter (fun p => ∃ E ∈ H, p ⊆ E)

/-- The actual common link of a two-point cell.  Its elements are the
    pairs which complete to two edges through the two cell vertices. -/
def commonLink (H : Family α) (V : Finset α) (q : Edge α) : Family α := by
  exact (V.powersetCard 2).filter (fun p =>
    ∃ x ∈ q, ∃ y ∈ q,
      x ≠ y ∧ Disjoint p q ∧
      p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H)

/-- Common-link cell support on the chosen finite vertex set. -/
def usedCells (H : Family α) (V : Finset α) : Family α := by
  exact (V.powersetCard 2).filter (fun q =>
    ∃ p ∈ V.powersetCard 2, ∃ x ∈ q, ∃ y ∈ q,
      x ≠ y ∧ Disjoint p q ∧
      p ∪ {x} ∈ H ∧ p ∪ {y} ∈ H)

theorem usedPairs_subset (H : Family α) (V : Finset α) :
    usedPairs H V ⊆ V.powersetCard 2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem usedCells_subset (H : Family α) (V : Finset α) :
    usedCells H V ⊆ V.powersetCard 2 := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- The cell support is exactly the collection of ambient pairs with a
    nonempty actual common link. -/
theorem mem_usedCells_iff_commonLink_nonempty
    (H : Family α) (V : Finset α) (q : Edge α) :
    q ∈ usedCells H V ↔
      q ∈ V.powersetCard 2 ∧ (commonLink H V q).Nonempty := by
  constructor
  · intro hq
    obtain ⟨hqV, p, hpV, x, hx, y, hy, hxy, hpq, hpx, hpy⟩ :=
      Finset.mem_filter.mp hq
    refine ⟨hqV, ⟨p, ?_⟩⟩
    exact Finset.mem_filter.mpr
      ⟨hpV, ⟨x, hx, y, hy, hxy, hpq, hpx, hpy⟩⟩
  · rintro ⟨hqV, ⟨p, hp⟩⟩
    obtain ⟨hpV, hcert⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hqV, ⟨p, hpV, hcert⟩⟩

/-- This is the concrete support theorem's final counting implication.  The
    hypothesis `hSupport` remains the combinatorial payment theorem to be
    formalized from admissibility. -/
theorem triple_family_card_le_choose_two_of_actual_supports
    (H : Family α) (V : Finset α)
    (hSupport : 2 * H.card ≤
      (usedPairs H V).card + (usedCells H V).card) :
    H.card ≤ V.card.choose 2 := by
  exact triple_family_card_le_choose_two H V (usedPairs H V) (usedCells H V)
    (usedPairs_subset H V) (usedCells_subset H V) hSupport

end Supports

end JSP523.Rank3
