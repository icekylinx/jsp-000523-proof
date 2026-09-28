import JSP523.Rank3.PairGraphClassification
import JSP523.Rank3.CellDegreeLedger
import Lean.Elab.Tactic.Omega

/-!
# Grounded centers and consistency between large rank-three links

The pair-graph classification gives a unique center for any common link
with at least four pairs.  Here that center is shown to be a genuine ground
vertex outside the cell.  Two links with at least two common pair edges
have the same center; this is a local propagation rule for later payment
arguments.
-/

namespace JSP523.Rank3

section LargeLinkCenters

variable {α : Type*} [DecidableEq α]

/-- Actual used cells whose common link contains at least four pairs. -/
def largeLinkCells (H : Family α) (V : Edge α) : Family α :=
  (usedCells H V).filter (fun q => 3 < (commonLink H V q).card)

theorem large_link_cells_subset_used_cells (H : Family α) (V : Edge α) :
    largeLinkCells H V ⊆ usedCells H V := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

theorem large_link_cells_subset_ground_pairs (H : Family α) (V : Edge α) :
    largeLinkCells H V ⊆ V.powersetCard 2 := by
  intro q hq
  exact used_cells_subset H V (large_link_cells_subset_used_cells H V hq)

/-- A large common-link star has a unique center in the ground set,
    outside its two-point cell. -/
theorem large_common_link_center_in_ground
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ largeLinkCells H V) :
    ∃ x ∈ V, x ∉ q ∧
      (∀ p ∈ commonLink H V q, x ∈ p) ∧
      ∀ y : α, (∀ p ∈ commonLink H V q, y ∈ p) → y = x := by
  have hqP : q ∈ V.powersetCard 2 :=
    large_link_cells_subset_ground_pairs H V hq
  have hlarge : 3 < (commonLink H V q).card :=
    (Finset.mem_filter.mp hq).2
  obtain ⟨x, hx, hunique⟩ :=
    actual_common_link_unique_center_of_large hH hqP hlarge
  have hpos : 0 < (commonLink H V q).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  obtain ⟨hpP, hcert⟩ := Finset.mem_filter.mp hp
  have hxV : x ∈ V := (Finset.mem_powersetCard.mp hpP).1 (hx p hp)
  obtain ⟨_, _, _, _, _, hdis, _, _⟩ := hcert
  have hxq : x ∉ q := by
    intro hxq
    exact (Finset.disjoint_left.mp hdis) (hx p hp) hxq
  exact ⟨x, hxV, hxq, hx, hunique⟩

/-- Two pair graphs with at least two common edges cannot have distinct
    universal vertices.  Applied to common links, this identifies their
    large-link centers across overlaps. -/
theorem common_link_centers_agree_of_two_common_pairs
    (H : Family α) (V q t : Edge α)
    (hcommon : 1 <
      ((commonLink H V q) ∩ (commonLink H V t)).card)
    {x y : α}
    (hx : ∀ p ∈ commonLink H V q, x ∈ p)
    (hy : ∀ p ∈ commonLink H V t, y ∈ p) :
    x = y := by
  let G : Family α := (commonLink H V q) ∩ (commonLink H V t)
  apply pair_graph_center_unique_of_two_edges G
  · intro p hp
    have hpq : p ∈ commonLink H V q := (Finset.mem_inter.mp hp).1
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpq).1).2
  · exact hcommon
  · intro p hp
    exact hx p (Finset.mem_inter.mp hp).1
  · intro p hp
    exact hy p (Finset.mem_inter.mp hp).2

/-- A pair of large common links sharing at least two base pairs has a
    common center that is an actual ground vertex. -/
theorem large_common_links_share_ground_center
    {H : Family α} {V q t : Edge α}
    (hH : Admissible H)
    (hq : q ∈ largeLinkCells H V)
    (ht : t ∈ largeLinkCells H V)
    (hcommon : 1 <
      ((commonLink H V q) ∩ (commonLink H V t)).card) :
    ∃ x ∈ V,
      (∀ p ∈ commonLink H V q, x ∈ p) ∧
      (∀ p ∈ commonLink H V t, x ∈ p) := by
  obtain ⟨x, hxV, _, hx, _⟩ :=
    large_common_link_center_in_ground hH hq
  obtain ⟨y, _, _, hy, _⟩ :=
    large_common_link_center_in_ground hH ht
  have hxy : x = y :=
    common_link_centers_agree_of_two_common_pairs H V q t hcommon hx hy
  subst y
  exact ⟨x, hxV, hx, hy⟩

end LargeLinkCenters

end JSP523.Rank3
