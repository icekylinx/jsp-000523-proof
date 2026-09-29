import JSP523.Rank5.RootedPrefixSelection
import JSP523.Rank5.RootedFacetCenters
import JSP523.Rank5.UpperFacetEndpoint

/-! # Pair labels in actual rooted prefix fibers -/

namespace JSP523.Rank5

open JSP523.Counting

variable {α : Type*} [DecidableEq α]

/-- A parent completion-pair label that agrees with every shared facet's
    inherited center lies in the selected prefix of each rooted fiber. -/
theorem rooted_pair_completion_label_in_prefix
    (L : Family α) (z : Edge α → α) (center : Edge α → α)
    (pairLabel : Edge α → α) (Y : Edge α)
    (hUniform : Uniform 5 L)
    (hInheritance : SharedFacetCenterInheritance L z center)
    (hPairCenter : ∀ A ∈ sharedFourShadow L, ∀ x y : α,
      x ≠ y → insert x A ∈ L → insert y A ∈ L →
        pairLabel {x, y} = center A) :
    PairCompletionLabelInPrefix
      ((rootedEdges L z).filter
        (fun E => rootedChosenPairPrefix z E = Y)) pairLabel Y := by
  intro S x y hSc hxy hEx hEy
  let A := Y ∪ S
  let Ex := Y ∪ (S ∪ {x})
  let Ey := Y ∪ (S ∪ {y})
  have hExRoot : Ex ∈ rootedEdges L z := (Finset.mem_filter.mp hEx).1
  have hEyRoot : Ey ∈ rootedEdges L z := (Finset.mem_filter.mp hEy).1
  have hYchosen : rootedChosenPairPrefix z Ex = Y :=
    (Finset.mem_filter.mp hEx).2
  have hYcard : Y.card = 2 := by
    have h := (rooted_chosen_pair_prefix_spec L z hUniform hExRoot).2.1
    rw [hYchosen] at h
    exact h
  have hAupper : A.card ≤ 4 := by
    have h := Finset.card_union_le Y S
    dsimp [A]
    omega
  have hExEq : Ex = insert x A := by
    dsimp [Ex, A]
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hEyEq : Ey = insert y A := by
    dsimp [Ey, A]
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hExCard : Ex.card = 5 :=
    hUniform (rooted_edges_subset L z hExRoot)
  have hEyCard : Ey.card = 5 :=
    hUniform (rooted_edges_subset L z hEyRoot)
  have hxNotA : x ∉ A := by
    intro hx
    have hEq : insert x A = A := Finset.insert_eq_of_mem hx
    rw [hExEq, hEq] at hExCard
    omega
  have hyNotA : y ∉ A := by
    intro hy
    have hEq : insert y A = A := Finset.insert_eq_of_mem hy
    rw [hEyEq, hEq] at hEyCard
    omega
  have hAcard : A.card = 4 := by
    rw [hExEq, Finset.card_insert_of_notMem hxNotA] at hExCard
    omega
  have hExL : insert x A ∈ L :=
    hExEq ▸ rooted_edges_subset L z hExRoot
  have hEyL : insert y A ∈ L :=
    hEyEq ▸ rooted_edges_subset L z hEyRoot
  have hExNeEy : insert x A ≠ insert y A := by
    intro hEq
    have hx : x ∈ insert y A := hEq ▸ Finset.mem_insert_self x A
    rcases Finset.mem_insert.mp hx with h | h
    · exact hxy h
    · exact hxNotA h
  have hShared : A ∈ sharedFourShadow L := by
    have hShadow : A ∈ fourShadow L :=
      (mem_four_shadow_iff_parent L A).mpr
        ⟨insert x A, hExL, Finset.subset_insert x A, hAcard⟩
    have hParents : ({insert x A, insert y A} : Family α) ⊆
        facetParents L A := by
      intro E hE
      rcases Finset.mem_insert.mp hE with hE | hE
      · rw [hE]
        exact Finset.mem_filter.mpr ⟨hExL, Finset.subset_insert x A⟩
      · rw [Finset.mem_singleton.mp hE]
        exact Finset.mem_filter.mpr ⟨hEyL, Finset.subset_insert y A⟩
    have hTwo : 2 ≤ (facetParents L A).card := by
      have hCard := Finset.card_pair hExNeEy
      have hSub := Finset.card_le_card hParents
      omega
    exact Finset.mem_filter.mpr ⟨hShadow, hTwo⟩
  obtain ⟨v, hvY, hv⟩ :=
    (rooted_chosen_pair_prefix_spec L z hUniform hExRoot).2.2
  rw [hYchosen] at hvY
  have hxEx : x ∈ Ex := hExEq ▸ Finset.mem_insert_self x A
  have hxNeV : x ≠ v := by
    intro h
    exact hxNotA (h ▸ Finset.mem_union_left S hvY)
  have hAerase : Ex.erase x = A := by
    rw [hExEq]
    simp [hxNotA]
  have hCoherent : DeletedFaceCoherent Ex z (fun _ => center A) x := by
    have hSpec := hInheritance A hShared
    dsimp [DeletedFaceCoherent]
    rw [hAerase]
    exact hSpec
  have hCenterRoot := coherent_deleted_face_center_eq_triple_root
    hExCard hxEx hv hxNeV hCoherent
  rw [hPairCenter A hShared x y hxy hExL hEyL, hCenterRoot]
  exact hvY

end JSP523.Rank5
