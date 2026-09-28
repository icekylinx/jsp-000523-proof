import JSP523.Basic

/-!
# Matchings as admissible families

This module proves a first nontrivial, fully finite fact used by the extremal
construction: a positive-uniformity matching cannot itself contain a forbidden
quadruple.
-/

namespace JSP523

section Matching

variable {α : Type*} [DecidableEq α]

/-- A hypergraph matching: distinct member edges are disjoint. -/
def IsMatching (M : Family α) : Prop :=
  ∀ ⦃E F : Edge α⦄, E ∈ M → F ∈ M → E ≠ F → Disjoint E F

/-- Any matching of nonempty uniform edges is admissible. -/
theorem matching_admissible {r : ℕ} {M : Family α}
    (hr : 0 < r) (hU : Uniform r M) (hM : IsMatching M) : Admissible M := by
  intro A B C D hA hB hC hD hq
  have hCA : Disjoint C A := hM hC hA hq.distinct.ac.symm
  have hCB : Disjoint C B := hM hC hB hq.distinct.bc.symm
  have hCcard : C.card = r := hU hC
  have hCpos : 0 < C.card := hCcard.symm ▸ hr
  obtain ⟨x, hxC⟩ := Finset.card_pos.mp hCpos
  have hxCD : x ∈ C ∪ D := Finset.mem_union.mpr (Or.inl hxC)
  have hxAB : x ∈ A ∪ B := by
    rw [hq.sameUnion]
    exact hxCD
  rcases Finset.mem_union.mp hxAB with hxA | hxB
  · exact (Finset.disjoint_left.mp hCA) hxC hxA
  · exact (Finset.disjoint_left.mp hCB) hxC hxB

end Matching

end JSP523
