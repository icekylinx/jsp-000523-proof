import JSP523.Rank5.HereditaryCenterExtension

/-!
# One-rank and two-rank completion of hereditary centers

The fixed `r ≥ 6` proof first completes centers of every free facet from
centers of its deletion faces, then repeats the same operation on edges.
This module makes that extension a global function on finite sets and shows
that each newly assigned rank inherits the same noncenter-deletion law.
-/

namespace JSP523.Rank5

section HereditaryCenterTower

variable {α : Type*} [DecidableEq α]

/-- A center assignment at one fixed cardinal rank with exact inheritance
    after deletion of any noncenter vertex. -/
def RankCenterInheritance (n : ℕ) (z : Edge α → α) : Prop :=
  ∀ T : Edge α, T.card = n →
    z T ∈ T ∧ ∀ a ∈ T, a ≠ z T → z (T.erase a) = z T

/-- Every set one rank higher has compatible deletion-face centers. -/
theorem hereditary_deletion_centers_of_rank_inheritance
    {n : ℕ} {z : Edge α → α} {T : Edge α}
    (hRank : RankCenterInheritance n z)
    (hT : T.card = n + 1) :
    HereditaryDeletionCenters T z := by
  have hFace : ∀ a ∈ T, (T.erase a).card = n := by
    intro a ha
    have hErase := Finset.card_erase_add_one ha
    omega
  constructor
  · intro a ha
    exact (hRank (T.erase a) (hFace a ha)).1
  · intro a ha b hb hbCenter
    exact (hRank (T.erase a) (hFace a ha)).2 b hb hbCenter

/-- Extend the center function by one rank, leaving every other rank's
    previously assigned values intact.  The choice is unique on the new
    rank by the partial functional-root lemma. -/
noncomputable def extendRankCenter
    (n : ℕ) (z : Edge α → α)
    (hRank : RankCenterInheritance n z) (hn : 3 ≤ n) :
    Edge α → α := fun T =>
  if hT : T.card = n + 1 then
    Classical.choose
      (hereditary_center_exists_unique
        (by omega : 4 ≤ T.card)
        (hereditary_deletion_centers_of_rank_inheritance hRank hT))
  else z T

theorem extend_rank_center_eq_of_card_ne
    {n : ℕ} {z : Edge α → α}
    (hRank : RankCenterInheritance n z) (hn : 3 ≤ n)
    {T : Edge α} (hT : T.card ≠ n + 1) :
    extendRankCenter n z hRank hn T = z T := by
  simp [extendRankCenter, hT]

/-- On a newly completed set, the chosen center lies in the set and agrees
    with the old centers on all deletion faces retaining it. -/
theorem extend_rank_center_spec
    {n : ℕ} {z : Edge α → α}
    (hRank : RankCenterInheritance n z) (hn : 3 ≤ n)
    {T : Edge α} (hT : T.card = n + 1) :
    extendRankCenter n z hRank hn T ∈ T ∧
      ∀ a ∈ T, a ≠ extendRankCenter n z hRank hn T →
        z (T.erase a) = extendRankCenter n z hRank hn T := by
  let hExist := hereditary_center_exists_unique
    (by omega : 4 ≤ T.card)
    (hereditary_deletion_centers_of_rank_inheritance hRank hT)
  have hSpec := (Classical.choose_spec hExist).1
  simpa only [extendRankCenter, dite_eq_left hT] using hSpec

/-- A pre-existing center on a shared facet is preserved whenever its
    noncenter deletion faces carry the inherited center. -/
theorem extend_rank_center_agrees_with_existing
    {n : ℕ} {z : Edge α → α}
    (hRank : RankCenterInheritance n z) (hn : 3 ≤ n)
    {T : Edge α} (hT : T.card = n + 1) {w : α}
    (hw : ∀ a ∈ T, a ≠ w → z (T.erase a) = w) :
    extendRankCenter n z hRank hn T = w := by
  have hcard : 4 ≤ T.card := by omega
  have hSpec := (extend_rank_center_spec hRank hn hT).2
  exact hereditary_center_agrees_with_existing hcard hSpec hw

/-- One extension step preserves the exact hereditary law at the new rank. -/
theorem extend_rank_center_inheritance
    {n : ℕ} {z : Edge α → α}
    (hRank : RankCenterInheritance n z) (hn : 3 ≤ n) :
    RankCenterInheritance (n + 1)
      (extendRankCenter n z hRank hn) := by
  intro T hT
  have hSpec := extend_rank_center_spec hRank hn hT
  refine ⟨hSpec.1, ?_⟩
  intro a ha haCenter
  have hFace : (T.erase a).card = n := by
    have hErase := Finset.card_erase_add_one ha
    omega
  have hNe : (T.erase a).card ≠ n + 1 := by omega
  rw [extend_rank_center_eq_of_card_ne hRank hn hNe]
  exact hSpec.2 a ha haCenter

/-- For every fixed `r ≥ 6`, a hereditary assignment on `(r-2)`-sets
    extends first to all `(r-1)`-facets and then to all `r`-edges.  Both
    extensions preserve the preceding rank's centers exactly. -/
theorem extend_centers_to_facets_and_edges
    {r : ℕ} (hr : 6 ≤ r)
    {z : Edge α → α}
    (hBase : RankCenterInheritance (r - 2) z) :
    ∃ zFacet zEdge : Edge α → α,
      RankCenterInheritance (r - 1) zFacet ∧
      RankCenterInheritance r zEdge ∧
      (∀ T : Edge α, T.card = r - 2 → zFacet T = z T) ∧
      (∀ T : Edge α, T.card = r - 1 → zEdge T = zFacet T) := by
  have hBaseMin : 3 ≤ r - 2 := by omega
  let zFacet := extendRankCenter (r - 2) z hBase hBaseMin
  have hFacetRaw : RankCenterInheritance (r - 2 + 1) zFacet :=
    extend_rank_center_inheritance hBase hBaseMin
  have hFacet : RankCenterInheritance (r - 1) zFacet := by
    simpa [show r - 2 + 1 = r - 1 by omega] using hFacetRaw
  have hFacetMin : 3 ≤ r - 1 := by omega
  let zEdge := extendRankCenter (r - 1) zFacet hFacet hFacetMin
  have hEdgeRaw : RankCenterInheritance (r - 1 + 1) zEdge :=
    extend_rank_center_inheritance hFacet hFacetMin
  have hEdge : RankCenterInheritance r zEdge := by
    simpa [show r - 1 + 1 = r by omega] using hEdgeRaw
  refine ⟨zFacet, zEdge, hFacet, hEdge, ?_, ?_⟩
  · intro T hT
    exact extend_rank_center_eq_of_card_ne hBase hBaseMin (by omega)
  · intro T hT
    exact extend_rank_center_eq_of_card_ne hFacet hFacetMin (by omega)

end HereditaryCenterTower

end JSP523.Rank5
