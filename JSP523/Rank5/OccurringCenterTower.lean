import JSP523.Rank5.HereditaryCenterExtension

/-! # Completing centers only on cores occurring in a family

The cleanup inheritance law is available on occurring cores. These
extensions apply the compatibility lemma on exactly those cores, and
preserve old assignments at lower ranks.
-/

namespace JSP523.Rank5

section OccurringCenterTower

variable {α : Type*} [DecidableEq α]

/-- A center assignment at one fixed cardinal rank with exact inheritance
    after deletion of any noncenter vertex. -/
def FamilyRankCenterInheritance (K : Family α) (n : ℕ) (z : Edge α → α) : Prop :=
  ∀ T : Edge α, (∃ E ∈ K, T ⊆ E) → T.card = n →
    z T ∈ T ∧ ∀ a ∈ T, a ≠ z T → z (T.erase a) = z T

/-- Inheritance also applies to a codimension-one subset containing the
    center, without choosing a presentation as an erased face. -/
theorem family_rank_center_eq_on_subset
    {K : Family α} {n : ℕ} {z : Edge α → α}
    (hRank : FamilyRankCenterInheritance K n z)
    {A T : Edge α} (hOcc : ∃ E ∈ K, T ⊆ E)
    (hT : T.card = n) (hAT : A ⊆ T)
    (hCard : A.card + 1 = T.card) (hz : z T ∈ A) : z A = z T := by
  have hDiffCard : (T \ A).card = 1 := by
    rw [Finset.card_sdiff_of_subset hAT]
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (T \ A).card)
  have haT := (Finset.mem_sdiff.mp ha).1
  have haA := (Finset.mem_sdiff.mp ha).2
  have hSub : A ⊆ T.erase a := by
    intro b hb
    exact Finset.mem_erase.mpr ⟨by intro h; exact haA (h ▸ hb), hAT hb⟩
  have hEq : A = T.erase a := Finset.eq_of_subset_of_card_le hSub (by
    have hErase := Finset.card_erase_add_one haT
    omega)
  have haCenter : a ≠ z T := by intro h; exact haA (h.symm ▸ hz)
  rw [hEq]
  exact (hRank T hOcc hT).2 a haT haCenter

/-- Every occurring set one rank higher has compatible deletion-face centers. -/
theorem hereditary_deletion_centers_of_family_rank_inheritance
    {K : Family α} {n : ℕ} {z : Edge α → α} {T : Edge α}
    (hRank : FamilyRankCenterInheritance K n z)
    (hT : T.card = n + 1) (hOcc : ∃ E ∈ K, T ⊆ E) :
    HereditaryDeletionCenters T z := by
  have hOccFace : ∀ a, ∃ E ∈ K, T.erase a ⊆ E := by
    intro a
    obtain ⟨E, hE, hTE⟩ := hOcc
    exact ⟨E, hE, (Finset.erase_subset a T).trans hTE⟩
  have hFace : ∀ a ∈ T, (T.erase a).card = n := by
    intro a ha
    have hErase := Finset.card_erase_add_one ha
    omega
  constructor
  · intro a ha
    exact (hRank (T.erase a) (hOccFace a) (hFace a ha)).1
  · intro a ha b hb hbCenter
    exact (hRank (T.erase a) (hOccFace a) (hFace a ha)).2 b hb hbCenter

/-- Extend the center function by one rank, leaving every other rank's
    previously assigned values intact.  The choice is unique on the new
    rank by the partial functional-root lemma. -/
noncomputable def extendFamilyRankCenter
    (K : Family α) (n : ℕ) (z : Edge α → α)
    (hRank : FamilyRankCenterInheritance K n z) (hn : 3 ≤ n) :
    Edge α → α := fun T =>
  if hT : T.card = n + 1 ∧ ∃ E ∈ K, T ⊆ E then
    Classical.choose
      (hereditary_center_exists_unique
        (by have := hT.1; omega : 4 ≤ T.card)
        (hereditary_deletion_centers_of_family_rank_inheritance hRank hT.1 hT.2))
  else z T

theorem extend_family_rank_center_eq_of_card_ne
    {K : Family α} {n : ℕ} {z : Edge α → α}
    (hRank : FamilyRankCenterInheritance K n z) (hn : 3 ≤ n)
    {T : Edge α} (hT : T.card ≠ n + 1) :
    extendFamilyRankCenter K n z hRank hn T = z T := by
  simp [extendFamilyRankCenter, hT]

/-- On a newly completed set, the chosen center lies in the set and agrees
    with the old centers on all deletion faces retaining it. -/
theorem extend_family_rank_center_spec
    {K : Family α} {n : ℕ} {z : Edge α → α}
    (hRank : FamilyRankCenterInheritance K n z) (hn : 3 ≤ n)
    {T : Edge α} (hT : T.card = n + 1) (hOcc : ∃ E ∈ K, T ⊆ E) :
    extendFamilyRankCenter K n z hRank hn T ∈ T ∧
      ∀ a ∈ T, a ≠ extendFamilyRankCenter K n z hRank hn T →
        z (T.erase a) = extendFamilyRankCenter K n z hRank hn T := by
  let hExist := hereditary_center_exists_unique
    (by omega : 4 ≤ T.card)
    (hereditary_deletion_centers_of_family_rank_inheritance hRank hT hOcc)
  have hSpec := (Classical.choose_spec hExist).1
  simpa only [extendFamilyRankCenter, dite_eq_left (And.intro hT hOcc)] using hSpec

/-- A pre-existing center on a shared facet is preserved whenever its
    noncenter deletion faces carry the inherited center. -/
theorem extend_family_rank_center_agrees_with_existing
    {K : Family α} {n : ℕ} {z : Edge α → α}
    (hRank : FamilyRankCenterInheritance K n z) (hn : 3 ≤ n)
    {T : Edge α} (hT : T.card = n + 1) (hOcc : ∃ E ∈ K, T ⊆ E) {w : α}
    (hw : ∀ a ∈ T, a ≠ w → z (T.erase a) = w) :
    extendFamilyRankCenter K n z hRank hn T = w := by
  have hcard : 4 ≤ T.card := by omega
  have hSpec := (extend_family_rank_center_spec hRank hn hT hOcc).2
  exact hereditary_center_agrees_with_existing hcard hSpec hw

/-- One extension step preserves the exact hereditary law at the new rank. -/
theorem extend_family_rank_center_inheritance
    {K : Family α} {n : ℕ} {z : Edge α → α}
    (hRank : FamilyRankCenterInheritance K n z) (hn : 3 ≤ n) :
    FamilyRankCenterInheritance K (n + 1)
      (extendFamilyRankCenter K n z hRank hn) := by
  intro T hOcc hT
  have hSpec := extend_family_rank_center_spec hRank hn hT hOcc
  refine ⟨hSpec.1, ?_⟩
  intro a ha haCenter
  have hFace : (T.erase a).card = n := by
    have hErase := Finset.card_erase_add_one ha
    omega
  have hNe : (T.erase a).card ≠ n + 1 := by omega
  rw [extend_family_rank_center_eq_of_card_ne hRank hn hNe]
  exact hSpec.2 a ha haCenter

/-- For every fixed `r ≥ 6`, a hereditary assignment on `(r-2)`-sets
    extends first to occurring `(r-1)`-facets and then to occurring `r`-edges.  Both
    extensions preserve the preceding rank's centers exactly. -/
theorem extend_family_centers_to_facets_and_edges
    {K : Family α} {r : ℕ} (hr : 6 ≤ r)
    {z : Edge α → α}
    (hBase : FamilyRankCenterInheritance K (r - 2) z) :
    ∃ zFacet zEdge : Edge α → α,
      FamilyRankCenterInheritance K (r - 1) zFacet ∧
      FamilyRankCenterInheritance K r zEdge ∧
      (∀ T : Edge α, T.card = r - 2 → zFacet T = z T) ∧
      (∀ T : Edge α, T.card = r - 1 → zEdge T = zFacet T) := by
  have hBaseMin : 3 ≤ r - 2 := by omega
  let zFacet := extendFamilyRankCenter K (r - 2) z hBase hBaseMin
  have hFacetRaw : FamilyRankCenterInheritance K (r - 2 + 1) zFacet :=
    extend_family_rank_center_inheritance hBase hBaseMin
  have hFacet : FamilyRankCenterInheritance K (r - 1) zFacet := by
    simpa [show r - 2 + 1 = r - 1 by omega] using hFacetRaw
  have hFacetMin : 3 ≤ r - 1 := by omega
  let zEdge := extendFamilyRankCenter K (r - 1) zFacet hFacet hFacetMin
  have hEdgeRaw : FamilyRankCenterInheritance K (r - 1 + 1) zEdge :=
    extend_family_rank_center_inheritance hFacet hFacetMin
  have hEdge : FamilyRankCenterInheritance K r zEdge := by
    simpa [show r - 1 + 1 = r by omega] using hEdgeRaw
  refine ⟨zFacet, zEdge, hFacet, hEdge, ?_, ?_⟩
  · intro T hT
    exact extend_family_rank_center_eq_of_card_ne hBase hBaseMin (by omega)
  · intro T hT
    exact extend_family_rank_center_eq_of_card_ne hFacet hFacetMin (by omega)

/-- The actual rank-six-and-higher root property: every occurring edge has
    a center inherited by all its codimension-two faces containing it. -/
theorem occurring_edge_root_exists
    {K : Family α} {r : ℕ} (hr : 6 ≤ r)
    (hUniform : Uniform r K) {z : Edge α → α}
    (hBase : FamilyRankCenterInheritance K (r - 2) z) :
    ∃ root : Edge α → α, ∀ E ∈ K,
      root E ∈ E ∧ ∀ A : Edge α, A ⊆ E → A.card = r - 2 →
        root E ∈ A → z A = root E := by
  obtain ⟨zFacet, zEdge, hFacet, hEdge, hPreserveBase, hPreserveFacet⟩ :=
    extend_family_centers_to_facets_and_edges hr hBase
  refine ⟨zEdge, ?_⟩
  intro E hE
  have hOccE : ∃ F ∈ K, E ⊆ F := ⟨E, hE, Finset.Subset.rfl⟩
  have hEc := hUniform hE
  refine ⟨(hEdge E hOccE hEc).1, ?_⟩
  intro A hAE hAc hzA
  obtain ⟨T, hAT, hTE, hTc⟩ := Finset.exists_subsuperset_card_eq
    hAE (by omega : A.card ≤ r - 1) (by omega : r - 1 ≤ E.card)
  have hOccT : ∃ F ∈ K, T ⊆ F := ⟨E, hE, hTE⟩
  have hTop : zEdge T = zEdge E := family_rank_center_eq_on_subset
    hEdge hOccE hEc hTE (by omega) (hAT hzA)
  have hFacetRoot : zFacet T = zEdge E := by
    rw [← hPreserveFacet T hTc]
    exact hTop
  have hLower : zFacet A = zFacet T := family_rank_center_eq_on_subset
    hFacet hOccT hTc hAT (by omega) (hFacetRoot.symm ▸ hzA)
  rw [hPreserveBase A hAc] at hLower
  exact hLower.trans hFacetRoot

/-- Choose the manuscript's `(r-3)`-prefix in each actual edge. Every
    codimension-two extension of that prefix is centered inside it. -/
theorem exists_occurring_rooted_prefix_assignment
    {K : Family α} {r : ℕ} (hr : 6 ≤ r)
    (hUniform : Uniform r K) {z : Edge α → α}
    (hBase : FamilyRankCenterInheritance K (r - 2) z) :
    ∃ chosenPrefix : Edge α → Edge α, ∀ E ∈ K,
      chosenPrefix E ⊆ E ∧ (chosenPrefix E).card = r - 3 ∧
      ∀ x ∈ E \ chosenPrefix E, z (chosenPrefix E ∪ {x}) ∈ chosenPrefix E := by
  classical
  obtain ⟨root, hRoot⟩ := occurring_edge_root_exists hr hUniform hBase
  have hChoose : ∀ E ∈ K, ∃ Y : Edge α,
      Y ⊆ E ∧ Y.card = r - 3 ∧ root E ∈ Y := by
    intro E hE
    have hEc := hUniform hE
    have hRootE := (hRoot E hE).1
    obtain ⟨Y, hRootY, hYE, hYc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.singleton_subset_iff.mpr hRootE)
      (by simp; omega : ({root E} : Edge α).card ≤ r - 3)
      (by omega : r - 3 ≤ E.card)
    exact ⟨Y, hYE, hYc, Finset.singleton_subset_iff.mp hRootY⟩
  let chosenPrefix : Edge α → Edge α := fun E =>
    if hE : E ∈ K then Classical.choose (hChoose E hE) else ∅
  refine ⟨chosenPrefix, ?_⟩
  intro E hE
  have hP : chosenPrefix E ⊆ E ∧ (chosenPrefix E).card = r - 3 ∧ root E ∈ chosenPrefix E := by
    simpa only [chosenPrefix, dite_eq_left hE] using Classical.choose_spec (hChoose E hE)
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro x hx
  have hxE := (Finset.mem_sdiff.mp hx).1
  have hxP := (Finset.mem_sdiff.mp hx).2
  have hSub : chosenPrefix E ∪ {x} ⊆ E := Finset.union_subset hP.1
    (Finset.singleton_subset_iff.mpr hxE)
  have hCard : (chosenPrefix E ∪ {x}).card = r - 2 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hxP, hP.2.1]
    omega
  have hCenter := (hRoot E hE).2 (chosenPrefix E ∪ {x}) hSub hCard
    (Finset.mem_union_left _ hP.2.2)
  rw [hCenter]
  exact hP.2.2

end OccurringCenterTower

end JSP523.Rank5
