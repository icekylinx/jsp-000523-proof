import JSP523.Rank4.GraphActualEdgeOccurrence

/-!
# Reindexing selected pair-link edges by four-edges

The edge count `e_*` in (III.B.9) is the number of pairs consisting of
a base pair and an unordered selected pair-link edge. Such a pair
determines a four-edge and two nonprivate opposite facets.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The selected unoriented pair-link edges, indexed by base pair. -/
noncomputable def actualSelectedBasePairOccurrences
    (D : FiniteCompletionCliqueData α) : Finset (Edge α × Edge α) := by
  classical
  exact ((D.ground.powersetCard 2).product
    ((Finset.univ : Finset α).powersetCard 2)).filter fun p =>
      p.2 ∈ (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D p.1) p.1).edgeFinset.image
          Sym2.toFinset

/-- An edge of a simple graph has two distinct endpoints. -/
theorem graph_edge_image_pair_card
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (P : Edge α)
    (hP : P ∈ F.edgeFinset.image Sym2.toFinset) :
    P.card = 2 := by
  classical
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hP
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hAdj : F.Adj a b :=
      (F.mem_edgeSet).1 ((F.mem_edgeFinset).1 he)
    have hab : a ≠ b := by
      intro h
      subst b
      exact F.irrefl hAdj
    simpa [Sym2.toFinset_mk_eq] using Finset.card_pair hab

/-- A two-set belongs to the unoriented graph edge image precisely when
its representative endpoints are adjacent. -/
theorem graph_edge_image_iff_adj
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (P : Edge α) (hPcard : P.card = 2) :
    P ∈ F.edgeFinset.image Sym2.toFinset ↔
      F.Adj (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 := by
  classical
  let a := (pairRootRep P hPcard).1
  let b := (pairRootRep P hPcard).2
  have hSpec := pair_root_rep_spec P hPcard
  constructor
  · intro hP
    obtain ⟨e, he, heP⟩ := Finset.mem_image.mp hP
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hAdj : F.Adj x y :=
        (F.mem_edgeSet).1 ((F.mem_edgeFinset).1 he)
      have hPair : ({x, y} : Edge α) = {a, b} := by
        calc
          ({x, y} : Edge α) = Sym2.toFinset (Sym2.mk x y) :=
            Sym2.toFinset_mk_eq.symm
          _ = P := heP
          _ = {a, b} := hSpec.2
      rcases pair_finset_eq_oriented_eq hSpec.1 hPair with
        ⟨hax, hby⟩ | ⟨hay, hbx⟩
      · simpa [a, b, hax, hby] using hAdj
      · simpa [a, b, hay, hbx] using hAdj.symm
  · intro hAdj
    have he : Sym2.mk a b ∈ F.edgeFinset :=
      (F.mem_edgeFinset).2 ((F.mem_edgeSet).2 hAdj)
    exact Finset.mem_image.mpr
      ⟨Sym2.mk a b, he, by simpa [Sym2.toFinset_mk_eq] using hSpec.2.symm⟩

/-- The actual graph edge total is the cardinality of its base-pair
occurrence set. -/
theorem actual_selected_edge_total_eq_base_pair_occurrences
    (D : FiniteCompletionCliqueData α) :
    actualSelectedEdgeTotal D =
      (actualSelectedBasePairOccurrences D).card := by
  classical
  let C := D.ground.powersetCard 2
  let U := (Finset.univ : Finset α).powersetCard 2
  let F : Edge α → SimpleGraph α := fun Q =>
    selectedCompletionPairGraph D (actualEligiblePairSlotVertices D Q) Q
  let A := actualSelectedBasePairOccurrences D
  have hMaps : (A : Set (Edge α × Edge α)).MapsTo Prod.fst C := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hFiber (Q : Edge α) (hQ : Q ∈ C) :
      (A.filter fun p => p.1 = Q).card =
        (F Q).edgeFinset.card := by
    have hImageSub : (F Q).edgeFinset.image Sym2.toFinset ⊆ U := by
      intro P hP
      exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, graph_edge_image_pair_card (F Q) P hP⟩
    have hSet : (A.filter fun p => p.1 = Q) =
        ({Q} : Finset (Edge α)).product
          ((F Q).edgeFinset.image Sym2.toFinset) := by
      ext p
      rcases p with ⟨Q', P⟩
      constructor
      · intro hp
        obtain ⟨hp, hEq⟩ := Finset.mem_filter.mp hp
        change Q' = Q at hEq
        subst Q'
        have hParts := Finset.mem_filter.mp hp
        have hP := hParts.2
        change P ∈ (F Q).edgeFinset.image Sym2.toFinset at hP
        exact Finset.mem_product.mpr
          ⟨Finset.mem_singleton.mpr rfl, hP⟩
      · intro hp
        obtain ⟨hEq, hP⟩ := Finset.mem_product.mp hp
        have hEq' : Q' = Q := Finset.mem_singleton.mp hEq
        subst Q'
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hQ, hImageSub hP⟩, hP⟩
        · rfl
    rw [hSet]
    change (({Q} : Finset (Edge α)) ×ˢ
      ((F Q).edgeFinset.image Sym2.toFinset)).card = _
    simp only [Finset.card_product, Finset.card_singleton, one_mul]
    exact Finset.card_image_of_injective _ sym2_to_finset_injective
  unfold actualSelectedEdgeTotal
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  exact (Finset.sum_congr rfl hFiber).symm

/-- A selected pair-link edge at a base pair gives a four-edge whose
two complementary opposite facets are nonprivate. -/
theorem actual_selected_base_pair_occurrence_to_edge_rows
    (D : FiniteCompletionCliqueData α)
    (Q P : Edge α)
    (hOcc : (Q, P) ∈ actualSelectedBasePairOccurrences D) :
    let E := Q ∪ P
    E ∈ D.K ∧ E ⊆ D.ground ∧
      P ∈ actualEdgeSelectedOccurrences D E ∧
      actualEdgePairBase E P = Q := by
  classical
  have hParts := Finset.mem_filter.mp hOcc
  have hProduct := Finset.mem_product.mp hParts.1
  have hQ : Q ∈ D.ground.powersetCard 2 := hProduct.1
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hProduct.2).2
  let a := (pairRootRep P hPcard).1
  let b := (pairRootRep P hPcard).2
  have hSpec := pair_root_rep_spec P hPcard
  have hab : a ≠ b := hSpec.1
  have hPset : P = ({a, b} : Edge α) := hSpec.2
  let F := selectedCompletionPairGraph D
    (actualEligiblePairSlotVertices D Q) Q
  have hAdj : F.Adj a b :=
    (graph_edge_image_iff_adj F P hPcard).1 hParts.2
  have hRaw : (completionPairLinkGraph D Q).Adj a b := hAdj.1
  have haQ : a ∉ Q := hRaw.1
  have hbQ : b ∉ Q := hRaw.2.1
  have haGround : a ∈ D.ground := hRaw.2.2.1
  have hbGround : b ∈ D.ground := hRaw.2.2.2.1
  have hSlotA : a ∈ actualEligiblePairSlotVertices D Q := hAdj.2.1
  have hSlotB : b ∈ actualEligiblePairSlotVertices D Q := hAdj.2.2
  have hUnion : Q ∪ P = insert a (insert b Q) := by
    rw [hPset]
    ext x
    simp [or_comm, or_left_comm]
  have hE : Q ∪ P ∈ D.K := hUnion ▸ hRaw.2.2.2.2.2
  have hGround : Q ∪ P ⊆ D.ground := by
    intro x hx
    rw [hPset] at hx
    rcases Finset.mem_union.mp hx with hxQ | hxP
    · exact (Finset.mem_powersetCard.mp hQ).1 hxQ
    · rcases Finset.mem_insert.mp hxP with rfl | hxP
      · exact haGround
      · have : x = b := Finset.mem_singleton.mp hxP
        simpa [this] using hbGround
  have hEraseA : (Q ∪ P).erase a = insert b Q := by
    rw [hUnion]
    ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp [hxa, hxb, haQ, hbQ, hab]
  have hEraseB : (Q ∪ P).erase b = insert a Q := by
    rw [hUnion]
    ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp [hxa, hxb, haQ, hbQ, hab, hab.symm]
  have hRowA : a ∈ actualEdgeNonprivateRows D (Q ∪ P) := by
    apply Finset.mem_filter.mpr
    constructor
    · rw [hUnion]
      simp
    · rw [hEraseA]
      exact (Finset.mem_filter.mp hSlotB).2.2.1
  have hRowB : b ∈ actualEdgeNonprivateRows D (Q ∪ P) := by
    apply Finset.mem_filter.mpr
    constructor
    · rw [hUnion]
      simp
    · rw [hEraseB]
      exact (Finset.mem_filter.mp hSlotA).2.2.1
  have hPRows : P ∈
      (actualEdgeNonprivateRows D (Q ∪ P)).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      rw [hPset] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hRowA
      · have hxb : x = b := Finset.mem_singleton.mp hx
        simpa [hxb] using hRowB
    · exact hPcard
  have hDisj : Disjoint Q P := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxP
    rw [hPset] at hxP
    rcases Finset.mem_insert.mp hxP with rfl | hxP
    · exact haQ hxQ
    · have hxb : x = b := Finset.mem_singleton.mp hxP
      exact hbQ (hxb ▸ hxQ)
  have hBase : actualEdgePairBase (Q ∪ P) P = Q := by
    unfold actualEdgePairBase
    ext x
    constructor
    · intro hx
      have h := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp h.1 with hxQ | hxP
      · exact hxQ
      · exact False.elim (h.2 hxP)
    · intro hxQ
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inl hxQ),
          (Finset.disjoint_left.mp hDisj hxQ)⟩
  have hSelected : P ∈ actualEdgeSelectedOccurrences D (Q ∪ P) := by
    apply Finset.mem_filter.mpr
    refine ⟨hPRows, ?_⟩
    have hIff := actual_edge_pair_selected_iff
      D (Q ∪ P) P hE hGround hPRows
    exact hIff.mp (by simpa only [hBase] using hAdj)
  exact ⟨hE, hGround, hSelected, hBase⟩

/-- Selected row-pair occurrences indexed by their containing four-edge. -/
noncomputable def actualSelectedEdgePairOccurrences
    (D : FiniteCompletionCliqueData α) : Finset (Edge α × Edge α) := by
  classical
  exact (D.K.product ((Finset.univ : Finset α).powersetCard 2)).filter
    fun p => p.2 ∈ actualEdgeSelectedOccurrences D p.1

/-- A selected row pair at a four-edge determines the original base-pair
selected-link occurrence. -/
theorem actual_selected_edge_pair_occurrence_to_base
    (D : FiniteCompletionCliqueData α)
    (E P : Edge α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground)
    (hOcc : (E, P) ∈ actualSelectedEdgePairOccurrences D) :
    (actualEdgePairBase E P, P) ∈
      actualSelectedBasePairOccurrences D := by
  classical
  have hParts := Finset.mem_filter.mp hOcc
  have hProd := Finset.mem_product.mp hParts.1
  have hE : E ∈ D.K := hProd.1
  have hPSelected : P ∈ actualEdgeSelectedOccurrences D E := hParts.2
  have hPRows := (Finset.mem_filter.mp hPSelected).1
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hPRows).2
  let Q := actualEdgePairBase E P
  let a := (pairRootRep P hPcard).1
  let b := (pairRootRep P hPcard).2
  have hGeo := actual_edge_pair_base_geometry
    D E P hE (hGround E hE) hPRows
  have hQ : Q ∈ D.ground.powersetCard 2 := hGeo.1
  have hAdj : (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q).Adj a b :=
    (actual_edge_pair_selected_iff
      D E P hE (hGround E hE) hPRows).2
      (Finset.mem_filter.mp hPSelected).2
  have hImage : P ∈
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).edgeFinset.image
          Sym2.toFinset :=
    (graph_edge_image_iff_adj _ P hPcard).2 hAdj
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr
    ⟨hQ, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hPcard⟩⟩, hImage⟩

/-- The edge-indexed occurrence set has cardinality equal to the sum of
the local selected occurrence counts. -/
theorem actual_selected_edge_pair_occurrences_card
    (D : FiniteCompletionCliqueData α) :
    (actualSelectedEdgePairOccurrences D).card =
      ∑ E ∈ D.K, (actualEdgeSelectedOccurrences D E).card := by
  classical
  let A := actualSelectedEdgePairOccurrences D
  have hMaps : (A : Set (Edge α × Edge α)).MapsTo Prod.fst D.K := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro E hE
  have hSet : (A.filter fun p => p.1 = E) =
      ({E} : Finset (Edge α)).product
        (actualEdgeSelectedOccurrences D E) := by
    ext p
    rcases p with ⟨E', P⟩
    constructor
    · intro hp
      obtain ⟨hp, hEq⟩ := Finset.mem_filter.mp hp
      change E' = E at hEq
      subst E'
      have hMem := (Finset.mem_filter.mp hp).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr rfl, hMem⟩
    · intro hp
      obtain ⟨hEq, hP⟩ := Finset.mem_product.mp hp
      have hEq' : E' = E := Finset.mem_singleton.mp hEq
      subst E'
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨hE, Finset.mem_powersetCard.mpr
            ⟨Finset.subset_univ _,
              (Finset.mem_powersetCard.mp
                (Finset.mem_filter.mp hP).1).2⟩⟩, hP⟩
      · rfl
  rw [hSet]
  change (({E} : Finset (Edge α)) ×ˢ
    actualEdgeSelectedOccurrences D E).card = _
  simp

/-- Reindex selected pair-link edges by the four-edge they represent. -/
theorem actual_selected_base_pair_occurrences_card_eq_edge_pairs
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    (actualSelectedBasePairOccurrences D).card =
      (actualSelectedEdgePairOccurrences D).card := by
  classical
  have hSum :
      (∑ _p ∈ actualSelectedBasePairOccurrences D, (1 : ℕ)) =
        ∑ _p ∈ actualSelectedEdgePairOccurrences D, (1 : ℕ) := by
    refine Finset.sum_bij'
      (fun p _ => (p.1 ∪ p.2, p.2))
      (fun p _ => (actualEdgePairBase p.1 p.2, p.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hE, _, hSelected, _⟩ :=
        actual_selected_base_pair_occurrence_to_edge_rows
          D p.1 p.2 hp
      have hParts := Finset.mem_filter.mp hp
      have hPcard : p.2.card = 2 :=
        (Finset.mem_powersetCard.mp
          (Finset.mem_product.mp hParts.1).2).2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨hE, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, hPcard⟩⟩, hSelected⟩
    · intro p hp
      exact actual_selected_edge_pair_occurrence_to_base
        D p.1 p.2 hGround hp
    · intro p hp
      have hBase :=
        (actual_selected_base_pair_occurrence_to_edge_rows
          D p.1 p.2 hp).2.2.2
      exact Prod.ext hBase rfl
    · intro p hp
      have hSelected : p.2 ∈ actualEdgeSelectedOccurrences D p.1 :=
        (Finset.mem_filter.mp hp).2
      have hRows := (Finset.mem_filter.mp hSelected).1
      have hPsubE : p.2 ⊆ p.1 :=
        (Finset.mem_powersetCard.mp hRows).1.trans
          (Finset.filter_subset _ _)
      have hUnion : p.2 ∪ (p.1 \ p.2) = p.1 :=
        Finset.union_sdiff_of_subset hPsubE
      apply Prod.ext
      · simpa [actualEdgePairBase, Finset.union_comm] using hUnion
      · rfl
    · intro p hp
      rfl
  simpa using hSum

/-- The global selected edge count is the sum of the local `k_E` from
the exact row-pair inclusion and exclusion identity. -/
theorem actual_selected_edge_total_eq_sum_edge_occurrences
    (D : FiniteCompletionCliqueData α)
    (hGround : ∀ E ∈ D.K, E ⊆ D.ground) :
    actualSelectedEdgeTotal D =
      ∑ E ∈ D.K, (actualEdgeSelectedOccurrences D E).card := by
  rw [actual_selected_edge_total_eq_base_pair_occurrences,
    actual_selected_base_pair_occurrences_card_eq_edge_pairs
      D hGround,
    actual_selected_edge_pair_occurrences_card]

end JSP523.Rank4
