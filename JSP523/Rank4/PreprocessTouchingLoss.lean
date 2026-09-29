import JSP523.Rank4.PreprocessCappedCrossMoment
import JSP523.Rank4.PreprocessStarAllocation

/-! # Actual cost of edges meeting a vertex cover -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Every error edge of the fixed decomposition contains two cover
vertices, so the original pair cap pays its loss. -/
theorem fixed_decomposition_error_card_le_pair_budget
    (H : Family α) (W X : Edge α) (M : ℕ)
    (hUniform : Uniform 4 H) (hGround : ∀ E ∈ H, E ⊆ W)
    (hPair : ∀ P : Edge α, P.card = 2 → rankFourPairDegree H P ≤ M) :
    (fixedDecompositionError H (W \ X) X).card ≤ X.card.choose 2 * M := by
  classical
  have hSub : fixedDecompositionError H (W \ X) X ⊆
      (X.powersetCard 2).biUnion fun P => H.filter fun E => P ⊆ E := by
    intro E hE
    have hEH := (Finset.mem_sdiff.mp hE).1
    have hNot := (Finset.mem_sdiff.mp hE).2
    have hTwo : 2 ≤ (E ∩ X).card := by
      by_contra h
      have hOne : (E ∩ X).card ≤ 1 := by omega
      have hUnique := Finset.card_le_one.mp hOne
      by_cases hMeet : (E ∩ X).Nonempty
      · obtain ⟨c, hc⟩ := hMeet
        have hcE := (Finset.mem_inter.mp hc).1
        have hcX := (Finset.mem_inter.mp hc).2
        have hTground : E.erase c ⊆ W \ X := by
          intro z hz
          have hzE := (Finset.mem_erase.mp hz).2
          refine Finset.mem_sdiff.mpr ⟨hGround E hEH hzE, ?_⟩
          intro hzX
          exact (Finset.mem_erase.mp hz).1 (hUnique z (Finset.mem_inter.mpr ⟨hzE, hzX⟩) c hc)
        have hTcard : (E.erase c).card = 3 := by rw [Finset.card_erase_of_mem hcE, hUniform hEH]
        have hInsert : insert c (E.erase c) = E := Finset.insert_erase hcE
        have hLink : E.erase c ∈ rankFourStarLink H (W \ X) c :=
          Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hTground, hTcard⟩, by simpa only [hInsert] using hEH⟩
        apply hNot
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_biUnion.mpr ⟨c, hcX, Finset.mem_image.mpr ⟨E.erase c, hLink, hInsert⟩⟩
      · have hEX : Disjoint E X := Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.not_nonempty_iff_eq_empty.mp hMeet)
        apply hNot
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_filter.mpr
        refine ⟨hEH, ?_⟩
        intro z hz
        exact Finset.mem_sdiff.mpr ⟨hGround E hEH hz, fun hzX => Finset.disjoint_left.mp hEX hz hzX⟩
    obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hTwo
    have hPX : P ⊆ X := fun z hz => (Finset.mem_inter.mp (hPsub hz)).2
    have hPE : P ⊆ E := fun z hz => (Finset.mem_inter.mp (hPsub hz)).1
    exact Finset.mem_biUnion.mpr ⟨P, Finset.mem_powersetCard.mpr ⟨hPX, hPcard⟩,
      Finset.mem_filter.mpr ⟨hEH, hPE⟩⟩
  calc
    _ ≤ ((X.powersetCard 2).biUnion fun P => H.filter fun E => P ⊆ E).card := Finset.card_le_card hSub
    _ ≤ ∑ P ∈ X.powersetCard 2, (H.filter fun E => P ⊆ E).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ X.powersetCard 2, M := by
      apply Finset.sum_le_sum
      intro P hP
      exact hPair P (Finset.mem_powersetCard.mp hP).2
    _ = X.card.choose 2 * M := by simp

/-- Original link size is paid by the original center degree. -/
theorem actual_star_link_card_le_vertex_degree
    (H : Family α) (V : Edge α) (c : α) (hcV : c ∉ V) :
    (rankFourStarLink H V c).card ≤ (H.filter fun E => c ∈ E).card := by
  apply Finset.card_le_card_of_injOn (fun T => insert c T)
  · intro T hT
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT).2, Finset.mem_insert_self _ _⟩
  · intro T hT S hS hEq
    have hcT : c ∉ T := fun hc => hcV ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 hc)
    have hcS : c ∉ S := fun hc => hcV ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1 hc)
    have hErase := congrArg (fun E : Edge α => E.erase c) hEq
    simpa only [Finset.erase_insert hcT, Finset.erase_insert hcS] using hErase

/-- The loss from deleting an entire cover is split into pair-charged
multiple hits, actual owner-cleaning loss, and the separated-star allocation. -/
theorem actual_touching_cover_loss
    {n : ℕ} (H : Family (Fin n)) (W X : Edge (Fin n)) (M radius : ℕ)
    [Nonempty {c // c ∈ X}]
    (hUniform : Uniform 4 H) (hGround : ∀ E ∈ H, E ⊆ W)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree H P ≤ M)
    (hSize : ∀ c ∈ X, 6 * (H.filter fun E => c ∈ E).card ≤ radius ^ 3) :
    let V := W \ X
    let L := fun i : {c // c ∈ X} => rankFourStarLink H V i.val
    let owner := maximumDegreePairOwner L
    3 * (H \ fixedDecompositionCore H V).card ≤
      3 * (X.card.choose 2 * M) +
        3 * (∑ i : {c // c ∈ X}, (L i \ pairOwnerCleanedLink L owner i).card) +
        (radius + 3) * V.card.choose 2 := by
  classical
  dsimp only
  let V := W \ X
  let L := fun i : {c // c ∈ X} => rankFourStarLink H V i.val
  let owner := maximumDegreePairOwner L
  have hOutside : ∀ c ∈ X, c ∉ V := by
    intro c hc hV
    exact (Finset.mem_sdiff.mp hV).2 hc
  have hLG : ∀ i : {c // c ∈ X}, ∀ T ∈ L i, T ∈ V.powersetCard 3 := by
    intro i T hT
    exact (Finset.mem_filter.mp hT).1
  have hLSize : ∀ i : {c // c ∈ X}, 6 * (L i).card ≤ radius ^ 3 := by
    intro i
    exact (Nat.mul_le_mul_left 6
      (actual_star_link_card_le_vertex_degree H V i.val (hOutside i.val i.property))).trans (hSize i.val i.property)
  have hAlloc := actual_cleaned_star_allocation V Finset.univ L owner radius
    (fun i _ => hLG i) (fun i _ => hLSize i)
  have hPart : (∑ i : {c // c ∈ X}, (L i).card) =
      (∑ i : {c // c ∈ X}, (pairOwnerCleanedLink L owner i).card) +
        ∑ i : {c // c ∈ X}, (L i \ pairOwnerCleanedLink L owner i).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hp := Finset.card_sdiff_add_card_eq_card (pair_owner_cleaned_link_subset L owner i)
    omega
  have hDecomp := fixed_decomposition_card_bound H V X hOutside
  have hError := fixed_decomposition_error_card_le_pair_budget H W X M hUniform hGround hPair
  have hLinkSum : (∑ c ∈ X, (rankFourStarLink H V c).card) =
      ∑ i : {c // c ∈ X}, (L i).card := by
        exact (Finset.sum_coe_sort X (fun c => (rankFourStarLink H V c).card)).symm
  rw [hLinkSum] at hDecomp
  have hCore : fixedDecompositionCore H V ⊆ H := Finset.filter_subset _ _
  have hCard := Finset.card_sdiff_add_card_eq_card hCore
  change 3 * (H \ fixedDecompositionCore H V).card ≤ _
  change (fixedDecompositionError H V X).card ≤ _ at hError
  dsimp only [V, L, owner] at hAlloc hPart hDecomp hCard hError ⊢
  omega

end JSP523.Rank4
