import JSP523.Rank4.GraphFacetLabelUniformity
import JSP523.Rank4.GraphCompletionData

/-!
# Actual selected pair-link vertices

For a cleaned completion system with unique common-root centers, the
manuscript's selected slot rule agrees with the pair-label witness
rule. The latter is used by the native excess ledger.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- The two actual presentations of an unselected pair link agree. -/
theorem completion_pair_link_eq_raw
    (D : FiniteCompletionCliqueData α) (Q : Edge α) :
    completionPairLinkGraph D Q =
      rawPairLinkGraph D.K D.ground Q := by
  rfl

omit [Fintype α] in
/-- A completion pair's label in the finite completion data equals the
canonical center selected from its actual nonempty common-root cell. -/
theorem actual_pair_label_eq_chosen_center
    (D : FiniteCompletionCliqueData α)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (a b : α) (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground) :
    D.label a b =
      chosenCommonRootLabel D.K D.ground fallback hCenters
        ({a, b} : Edge α) := by
  classical
  let P : Edge α := {a, b}
  have hPcard : P.card = 2 := Finset.card_pair hab
  let r := pairRootRep P hPcard
  have hSpec := pairRootRep_spec P hPcard
  have hRootLabel : D.label r.1 r.2 = D.label a b := by
    have hOrient := pair_finset_eq_oriented_eq hab hSpec.2.symm
    rcases hOrient with hSame | hSwap
    · rw [hSame.1, hSame.2]
    · rw [hSwap.1, hSwap.2]
      exact D.label_symm r.1 r.2
  have hDataCenter : ∀ ⦃T : Edge α⦄,
      T ∈ commonRootCell D.K D.ground P → D.label a b ∈ T := by
    intro T hT
    have hT' : T ∈ commonTripleCell D.K D.ground r.1 r.2 := by
      simpa only [commonRootCell, dite_eq_left hPcard] using hT
    rw [← hRootLabel]
    exact D.label_center r.1 r.2 hSpec.1 T hT'
  obtain ⟨z, hz, hUnique⟩ :=
    used_common_root_has_unique_center D.K D.ground hCenters P hUsed
  have hD : D.label a b = z := hUnique _ hDataCenter
  have hChosen :
      chosenCommonRootLabel D.K D.ground fallback hCenters P = z :=
    hUnique _ (by
      intro T hT
      exact chosen_common_root_label_center
        D.K D.ground fallback hCenters P hUsed T hT)
  exact hD.trans hChosen.symm

/-- Exactly the selected vertices specified in (III.B.8): the facet
Q+x is nonprivate and is either colored or monochromatic with its
center in Q. -/
noncomputable def actualEligiblePairSlotVertices
    (D : FiniteCompletionCliqueData α) (Q : Edge α) : Finset α :=
  by
    classical
    exact D.ground.filter fun x => x ∉ Q ∧
      FacetEligibleAtPair
        (graphFacetCompletions D.K D.ground (insert x Q))
        D.label Q

noncomputable instance actualEligiblePairLinkDecidableRel
    (D : FiniteCompletionCliqueData α) (Q : Edge α) :
    DecidableRel
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q).Adj :=
  Classical.decRel _

omit [Fintype α] in
/-- Adjacency to a slot vertex in the ordinary pair link is exactly
completion membership at the corresponding triple facet. -/
theorem raw_pair_link_slot_adj_iff_facet_completion
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (x a : α) (hxU : x ∈ D.ground) (hxQ : x ∉ Q) :
    (rawPairLinkGraph D.K D.ground Q).Adj x a ↔
      a ∈ graphFacetCompletions D.K D.ground (insert x Q) := by
  classical
  have hQcard : Q.card = 2 := (Finset.mem_powersetCard.mp hQ).2
  have hTcard : (insert x Q).card = 3 := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
  constructor
  · intro hAdj
    have hParts := (rawPairLinkGraph_adj D.K D.ground Q x a).mp hAdj
    exact Finset.mem_filter.mpr
      ⟨hParts.2.2.2.1, by
        simpa only [Finset.insert_comm] using hParts.2.2.2.2.2⟩
  · intro ha
    have ha' := Finset.mem_filter.mp ha
    have haNot : a ∉ insert x Q :=
      four_facet_completion_not_in_facet
        D.K D.uniform_four (insert x Q) hTcard a ha'.2
    have haQ : a ∉ Q := by
      intro haQ
      exact haNot (Finset.mem_insert_of_mem haQ)
    have hxa : x ≠ a := by
      intro h
      exact haNot (h.symm ▸ Finset.mem_insert_self x Q)
    exact (rawPairLinkGraph_adj D.K D.ground Q x a).2
      ⟨hxQ, haQ, hxU, ha'.1, hxa,
        by simpa only [Finset.insert_comm] using ha'.2⟩

omit [Fintype α] in
/-- The center of two completion neighbors at a selected base pair is
the same in the finite completion data and in the canonical root-cell
label function. -/
theorem raw_common_pair_data_label_eq_chosen
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (p q x : α)
    (hpU : p ∈ D.ground) (hqU : q ∈ D.ground)
    (hpq : p ≠ q)
    (hpx : (rawPairLinkGraph D.K D.ground Q).Adj p x)
    (hqx : (rawPairLinkGraph D.K D.ground Q).Adj q x) :
    D.label p q =
      chosenCommonRootLabel D.K D.ground fallback hCenters
        ({p, q} : Edge α) := by
  classical
  let P : Edge α := {p, q}
  have hCell := raw_pair_common_neighbor_gives_cell
    D.K D.ground Q D.uniform_four hQ p q x hpU hqU hpq hpx hqx
  have hP : P ∈ D.ground.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hpq⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hpU
    · exact (Finset.mem_singleton.mp ht) ▸ hqU
  have hUsed : P ∈ nonemptyCommonRoots D.K D.ground :=
    Finset.mem_filter.mpr
      ⟨hP, Finset.card_pos.mpr ⟨insert x Q, hCell⟩⟩
  exact actual_pair_label_eq_chosen_center
    D fallback hCenters p q hpq hUsed

/-- Under the actual centered completion data, the manuscript's
colored-or-monochromatic selected vertex set is exactly the pair-label
witness set. -/
theorem actual_eligible_pair_slot_vertices_eq_witness_slots
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    actualEligiblePairSlotVertices D Q =
      pairLabelWitnessSlots D.K D.ground Q fallback hCenters := by
  classical
  ext x
  let C := graphFacetCompletions D.K D.ground (insert x Q)
  have hQ' := Finset.mem_powersetCard.mp hQ
  constructor
  · intro hxActual
    have hxParts : x ∈ D.ground ∧ x ∉ Q ∧
        FacetEligibleAtPair C D.label Q := by
      simpa only [actualEligiblePairSlotVertices,
        Finset.mem_filter] using hxActual
    obtain ⟨hxU, hxQ, hEligible⟩ := hxParts
    have hTcard : (insert x Q).card = 3 := by
      rw [Finset.card_insert_of_notMem hxQ, hQ'.2]
    have hTsub : insert x Q ⊆ D.ground :=
      Finset.insert_subset hxU hQ'.1
    have hLabelFacet : ∀ a ∈ C, ∀ b ∈ C,
        a ≠ b → D.label a b ∈ insert x Q := by
      intro a ha b hb hab
      exact completion_pair_label_mem_facet D (insert x Q)
        hTcard hTsub a b ha hb hab
    obtain ⟨p, hp, q, hq, hpq, hLabelQ⟩ :=
      facet_eligible_implies_witness C D.label Q x
        hLabelFacet hEligible
    have hxp : (rawPairLinkGraph D.K D.ground Q).Adj x p :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x p hxU hxQ).2 hp
    have hxq : (rawPairLinkGraph D.K D.ground Q).Adj x q :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x q hxU hxQ).2 hq
    have hpU : p ∈ D.ground := (Finset.mem_filter.mp hp).1
    have hqU : q ∈ D.ground := (Finset.mem_filter.mp hq).1
    have hLabelEq := raw_common_pair_data_label_eq_chosen
      D Q hQ fallback hCenters p q x hpU hqU hpq
      hxp.symm hxq.symm
    exact (pair_label_witness_slots_mem
      D.K D.ground Q fallback hCenters x).2
      ⟨hxU, p, q, hpq, hxp, hxq, hLabelEq.symm ▸ hLabelQ⟩
  · intro hxWitness
    obtain ⟨hxU, p, q, hpq, hxp, hxq, hChosenQ⟩ :=
      (pair_label_witness_slots_mem
        D.K D.ground Q fallback hCenters x).mp hxWitness
    have hxQ : x ∉ Q :=
      ((rawPairLinkGraph_adj D.K D.ground Q x p).mp hxp).1
    have hp : p ∈ C :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x p hxU hxQ).1 hxp
    have hq : q ∈ C :=
      (raw_pair_link_slot_adj_iff_facet_completion
        D Q hQ x q hxU hxQ).1 hxq
    have hpU : p ∈ D.ground := (Finset.mem_filter.mp hp).1
    have hqU : q ∈ D.ground := (Finset.mem_filter.mp hq).1
    have hLabelEq := raw_common_pair_data_label_eq_chosen
      D Q hQ fallback hCenters p q x hpU hqU hpq
      hxp.symm hxq.symm
    have hLabelQ : D.label p q ∈ Q := hLabelEq ▸ hChosenQ
    have hEligible := facet_witness_implies_eligible
      C D.label Q D.label_symm p q hp hq hpq hLabelQ
    change x ∈ D.ground.filter fun y => y ∉ Q ∧
      FacetEligibleAtPair
        (graphFacetCompletions D.K D.ground (insert y Q))
        D.label Q
    exact Finset.mem_filter.mpr ⟨hxU, hxQ, hEligible⟩

/-- The selected graph formed with the manuscript's actual eligibility
rule is the witness-selected ordinary pair link. -/
theorem actual_eligible_pair_link_eq_witness_link
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    selectedCompletionPairGraph D (actualEligiblePairSlotVertices D Q) Q =
      selectedRawPairLinkGraph D.K D.ground Q
        (pairLabelWitnessSlots D.K D.ground Q fallback hCenters) := by
  rw [actual_eligible_pair_slot_vertices_eq_witness_slots
    D Q hQ fallback hCenters]
  rfl

/-- In an actual selected pair link, a used completion pair has no
positive common-neighbor excess at a base pair omitting its label. -/
theorem actual_eligible_pair_common_le_one_off_label
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (a b : α) (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hzQ : chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α) ∉ Q) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b ≤ 1 := by
  have hGraphEq := actual_eligible_pair_link_eq_witness_link
    D Q hQ fallback hCenters
  have hMultiplicity := graph_common_multiplicity_congr
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q)
    (selectedRawPairLinkGraph D.K D.ground Q
      (pairLabelWitnessSlots D.K D.ground Q fallback hCenters))
    (by intro x y; rw [hGraphEq]) a b
  rw [hMultiplicity]
  exact selected_raw_pair_common_multiplicity_le_one_off_label
    D.K D.ground Q
    (pairLabelWitnessSlots D.K D.ground Q fallback hCenters)
    D.uniform_four hQ a b
    (chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α))
    haU hbU hab hzQ
    (fun T hT => chosen_common_root_label_center
      D.K D.ground fallback hCenters
      ({a, b} : Edge α) hUsed T hT)

/-- At every on-label base pair, the manuscript's actual selected
pair-link excess equals the native vertex degree excess. -/
theorem actual_eligible_pair_common_excess_eq_native_excess
    (D : FiniteCompletionCliqueData α)
    (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (a b w : α)
    (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hwU : w ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hzw : chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α) ≠ w)
    (haQ : a ∉ ({chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α), w} : Edge α))
    (hbQ : b ∉ ({chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α), w} : Edge α)) :
    let z := chosenCommonRootLabel D.K D.ground fallback hCenters
      ({a, b} : Edge α)
    let Q : Edge α := {z, w}
    graphCommonMultiplicity
        (selectedCompletionPairGraph D
          (actualEligiblePairSlotVertices D Q) Q) a b - 1 =
      (nativeTailGraph D.K D.ground ({a, b} : Edge α) z).degree w - 1 := by
  dsimp
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters
    ({a, b} : Edge α)
  let Q : Edge α := {z, w}
  have hzU : z ∈ D.ground :=
    (chosen_common_root_label_valid D.K D.ground
      fallback hCenters ({a, b} : Edge α) hUsed).1
  have hQ : Q ∈ D.ground.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hzw⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hzU
    · exact (Finset.mem_singleton.mp ht) ▸ hwU
  have hGraphEq := actual_eligible_pair_link_eq_witness_link
    D Q hQ fallback hCenters
  have hMultiplicity := graph_common_multiplicity_congr
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q)
    (selectedRawPairLinkGraph D.K D.ground Q
      (pairLabelWitnessSlots D.K D.ground Q fallback hCenters))
    (by intro x y; rw [hGraphEq]) a b
  rw [hMultiplicity]
  exact witness_selected_pair_common_excess_eq_native_excess
    D.K D.ground fallback D.uniform_four hCenters
    a b z w haU hbU hzU hwU hab hzw haQ hbQ rfl

end JSP523.Rank4
