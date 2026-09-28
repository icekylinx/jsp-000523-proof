import JSP523.Rank3.ReceiverExclusion
import JSP523.Rank3.LargeLinkCenters

/-!
# Common-neighbor fibers and large common-link centers

The common-neighbor set in a root graph is exactly the fiber of common-link
base pairs through that root.  When a common link is a star, its center
accounts for all base pairs, so its rooted common-neighbor count equals the
whole common-link degree.
-/

namespace JSP523.Rank3

section RootCommonLinkFibers

variable {α : Type*} [DecidableEq α]

/-- Actual common neighbors and reciprocal common-link pairs through `z`
    are the same vertices. -/
theorem root_common_neighbors_eq_common_link_fiber
    (H : Family α) (V : Edge α)
    {z x u : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u) :
    rootCommonNeighbors H V z x u =
      commonLinkFiber H V ({x, u} : Edge α) z := by
  apply Finset.Subset.antisymm
  · exact root_common_neighbors_subset_common_link_fiber H V
      hzV hzx hzu hxu
  · intro t ht
    obtain ⟨htV, hztLink⟩ := Finset.mem_filter.mp ht
    have hztOrient : ({z, t} : Edge α) ∈ orientedCommonLink H V x u :=
      (mem_common_link_pair_iff_oriented H V hxu _).mp hztLink
    obtain ⟨_, hdis, hzxEdge, hzuEdge⟩ :=
      Finset.mem_filter.mp hztOrient
    have htz : t ≠ z := by
      intro h
      have hcard : ({z, t} : Edge α).card = 2 :=
        (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp hztOrient).1).2
      simp [h] at hcard
    have htx : t ≠ x := by
      intro h
      subst t
      have hxL : x ∈ ({z, x} : Edge α) := by simp
      have hxR : x ∈ ({x, u} : Edge α) := by simp
      exact (Finset.disjoint_left.mp hdis) hxL hxR
    have htu : t ≠ u := by
      intro h
      subst t
      have huL : u ∈ ({z, u} : Edge α) := by simp
      have huR : u ∈ ({x, u} : Edge α) := by simp
      exact (Finset.disjoint_left.mp hdis) huL huR
    have hxTriple : ({x, t} : Edge α) ∪ {z} ∈ H := by
      have heq : ({x, t} : Edge α) ∪ {z} =
          ({z, t} : Edge α) ∪ {x} := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq.symm ▸ hzxEdge
    have huTriple : ({u, t} : Edge α) ∪ {z} ∈ H := by
      have heq : ({u, t} : Edge α) ∪ {z} =
          ({z, t} : Edge α) ∪ {u} := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq.symm ▸ hzuEdge
    exact Finset.mem_filter.mpr ⟨htV, htz, htx, htu, hxTriple, huTriple⟩

private theorem common_link_fiber_vertex_ne_root
    (H : Family α) (V q : Edge α) (z : α)
    {t : α} (ht : t ∈ commonLinkFiber H V q z) : t ≠ z := by
  intro h
  have hzt : ({z, t} : Edge α) ∈ commonLink H V q :=
    (Finset.mem_filter.mp ht).2
  have hcard : ({z, t} : Edge α).card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hzt).1).2
  simp [h] at hcard

/-- If every base pair in a common link contains `z`, then the common
    link and the fiber through `z` have the same cardinality. -/
theorem common_link_fiber_card_eq_of_center
    (H : Family α) (V q : Edge α) (z : α)
    (hcenter : ∀ p ∈ commonLink H V q, z ∈ p) :
    (commonLinkFiber H V q z).card = (commonLink H V q).card := by
  apply Finset.card_bij (fun t _ => ({z, t} : Edge α))
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu heq
    have htz := common_link_fiber_vertex_ne_root H V q z ht
    have huz := common_link_fiber_vertex_ne_root H V q z hu
    have htMem : t ∈ ({z, t} : Edge α) := by simp
    have htOther : t ∈ ({z, u} : Edge α) := heq ▸ htMem
    rcases Finset.mem_insert.mp htOther with htz' | htu
    · exact False.elim (htz htz')
    · exact Finset.mem_singleton.mp htu
  · intro p hp
    have hp2 : p.card = 2 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
    have hz : z ∈ p := hcenter p hp
    have hmore : (p.erase z).Nonempty := by
      apply Finset.card_pos.mp
      have hErase := Finset.card_erase_add_one hz
      omega
    obtain ⟨t, htErase⟩ := hmore
    have htz : t ≠ z := (Finset.mem_erase.mp htErase).1
    have ht : t ∈ p := (Finset.mem_erase.mp htErase).2
    have heq : ({z, t} : Edge α) = p := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwz | hwt
        · exact hwz ▸ hz
        · exact (Finset.mem_singleton.mp hwt) ▸ ht
      · rw [Finset.card_pair (Ne.symm htz), hp2]
    have htV : t ∈ V :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).1 ht
    refine ⟨t, Finset.mem_filter.mpr ⟨htV, ?_⟩, heq⟩
    exact heq.symm ▸ hp

/-- The fiber through one root is bounded by the whole common link. -/
theorem common_link_fiber_card_le_common_link_card
    (H : Family α) (V q : Edge α) (z : α) :
    (commonLinkFiber H V q z).card ≤ (commonLink H V q).card := by
  apply Finset.card_le_card_of_injOn
    (fun t => ({z, t} : Edge α))
  · intro t ht
    exact (Finset.mem_filter.mp ht).2
  · intro t ht u hu heq
    have htz := common_link_fiber_vertex_ne_root H V q z ht
    have htMem : t ∈ ({z, t} : Edge α) := by simp
    change ({z, t} : Edge α) = ({z, u} : Edge α) at heq
    have htOther : t ∈ ({z, u} : Edge α) := heq ▸ htMem
    rcases Finset.mem_insert.mp htOther with htz' | htu
    · exact False.elim (htz htz')
    · exact Finset.mem_singleton.mp htu

/-- A centered common link is counted exactly at its root in the graph
    common-neighbor statistic. -/
theorem root_common_neighbors_card_eq_common_link_card_of_center
    (H : Family α) (V : Edge α)
    {z x u : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u)
    (hcenter : ∀ p ∈ commonLink H V ({x, u} : Edge α), z ∈ p) :
    (rootCommonNeighbors H V z x u).card =
      (commonLink H V ({x, u} : Edge α)).card := by
  rw [root_common_neighbors_eq_common_link_fiber H V hzV hzx hzu hxu]
  exact common_link_fiber_card_eq_of_center H V _ z hcenter

/-- Every rooted common-neighbor count is at most its reciprocal
    common-link size. -/
theorem root_common_neighbors_card_le_common_link_card
    (H : Family α) (V : Edge α)
    {z x u : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u) :
    (rootCommonNeighbors H V z x u).card ≤
      (commonLink H V ({x, u} : Edge α)).card := by
  rw [root_common_neighbors_eq_common_link_fiber H V hzV hzx hzu hxu]
  exact common_link_fiber_card_le_common_link_card H V _ z

/-- If a common link is centered at `c`, every different root has at
    most one common neighbor in its graph link. -/
theorem root_common_neighbors_card_le_one_of_other_center
    (H : Family α) (V : Edge α)
    {z x u c : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzu : z ≠ u) (hxu : x ≠ u)
    (hzc : z ≠ c)
    (hcenter : ∀ p ∈ commonLink H V ({x, u} : Edge α), c ∈ p) :
    (rootCommonNeighbors H V z x u).card ≤ 1 := by
  have hsub : commonLinkFiber H V ({x, u} : Edge α) z ⊆ ({c} : Edge α) := by
    intro t ht
    have hzt : ({z, t} : Edge α) ∈ commonLink H V ({x, u} : Edge α) :=
      (Finset.mem_filter.mp ht).2
    have hc : c ∈ ({z, t} : Edge α) := hcenter _ hzt
    rcases Finset.mem_insert.mp hc with hcz | hct
    · exact False.elim (hzc hcz.symm)
    · exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp hct).symm
  rw [root_common_neighbors_eq_common_link_fiber H V hzV hzx hzu hxu]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- The manuscript's common-link surplus appears at exactly its unique
    center root when the link is large, and nowhere else. -/
theorem sum_root_link_surplus_eq_link_surplus
    {H : Family α} {V : Edge α} {x u : α}
    (hH : Admissible H)
    (hxV : x ∈ V) (huV : u ∈ V) (hxu : x ≠ u) :
    (∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
      linkSurplus (rootCommonNeighbors H V z x u).card) =
      linkSurplus (commonLink H V ({x, u} : Edge α)).card := by
  let q : Edge α := {x, u}
  have hqV : q ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htx | htu
      · exact htx ▸ hxV
      · exact (Finset.mem_singleton.mp htu) ▸ huV
    · exact Finset.card_pair hxu
  by_cases hlarge : 3 < (commonLink H V q).card
  · have hqUsed : q ∈ usedCells H V :=
      (mem_used_cells_iff_common_link_nonempty H V q).mpr
        ⟨hqV, Finset.card_pos.mp (by omega)⟩
    have hqLarge : q ∈ largeLinkCells H V :=
      Finset.mem_filter.mpr ⟨hqUsed, hlarge⟩
    obtain ⟨c, hcV, hcNot, hcenter, _⟩ :=
      large_common_link_center_in_ground hH hqLarge
    have hcx : c ≠ x := by
      intro h
      exact hcNot (by simp [q, h])
    have hcu : c ≠ u := by
      intro h
      exact hcNot (by simp [q, h])
    have hcFiltered : c ∈ V.filter (fun z => z ≠ x ∧ z ≠ u) :=
      Finset.mem_filter.mpr ⟨hcV, hcx, hcu⟩
    have hsingle :
        (∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
          linkSurplus (rootCommonNeighbors H V z x u).card) =
        linkSurplus (rootCommonNeighbors H V c x u).card := by
      apply Finset.sum_eq_single_of_mem c hcFiltered
      intro z hz hzc
      obtain ⟨hzV, hzx, hzu⟩ := Finset.mem_filter.mp hz
      have hsmall := root_common_neighbors_card_le_one_of_other_center
        H V hzV hzx hzu hxu hzc hcenter
      simp [linkSurplus, show ¬ 3 < (rootCommonNeighbors H V z x u).card by omega]
    rw [hsingle, root_common_neighbors_card_eq_common_link_card_of_center
      H V hcV hcx hcu hxu hcenter]
  · have hzero : linkSurplus (commonLink H V q).card = 0 := by
      simp [linkSurplus, hlarge]
    rw [hzero]
    apply Finset.sum_eq_zero
    intro z hz
    obtain ⟨hzV, hzx, hzu⟩ := Finset.mem_filter.mp hz
    have hbound := root_common_neighbors_card_le_common_link_card
      H V hzV hzx hzu hxu
    dsimp [q] at hlarge
    have hsmall : ¬ 3 < (rootCommonNeighbors H V z x u).card := by
      omega
    simp [linkSurplus, hsmall]

end RootCommonLinkFibers

end JSP523.Rank3
