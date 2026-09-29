import JSP523.Rank4.GraphActualFullPayment

/-! # Native centers supplied by the completion labels

A common-root cell needs a designated common vertex, without uniqueness.
The completion system already provides this vertex through `label_center`.
-/

namespace JSP523.Rank4.AssignedNative

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A designated center for every nonempty common-root cell. -/
structure CenterAssignment (K : Family α) (U : Edge α) where
  label : Edge α → α
  center : ∀ P ∈ nonemptyCommonRoots K U, ∀ T ∈ commonRootCell K U P, label P ∈ T

/-- The fallback is retained in this interface for compatibility with the
native sum interfaces; the assignment itself specifies every label. -/
def chosenCommonRootLabel (K : Family α) (U : Edge α) (_fallback : α)
    (hCenters : CenterAssignment K U) : Edge α → α := hCenters.label

omit [Fintype α] in
theorem chosen_common_root_label_center
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : CenterAssignment K U)
    (P : Edge α) (hP : P ∈ nonemptyCommonRoots K U)
    (T : Edge α) (hT : T ∈ commonRootCell K U P) :
    chosenCommonRootLabel K U fallback hCenters P ∈ T :=
  hCenters.center P hP T hT

omit [Fintype α] in
/-- A selected center of a used pair is in the ground set and outside
the pair, as required by the native tail-graph support bound. -/
theorem chosen_common_root_label_valid
    (K : Family α) (U : Edge α) (fallback : α)
    (hCenters : CenterAssignment K U)
    (P : Edge α) (hP : P ∈ nonemptyCommonRoots K U) :
    chosenCommonRootLabel K U fallback hCenters P ∈ U ∧
      chosenCommonRootLabel K U fallback hCenters P ∉ P := by
  classical
  have hP' := Finset.mem_filter.mp hP
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hP'.1).2
  obtain ⟨T, hT⟩ := Finset.card_pos.mp hP'.2
  have hzT := chosen_common_root_label_center
    K U fallback hCenters P hP T hT
  have hT' : T ∈ commonTripleCell K U
      (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 := by
    simpa only [commonRootCell, dite_eq_left hPcard] using hT
  have hData := mem_common_triple_cell.mp hT'
  have hPairSpec := pair_root_rep_spec P hPcard
  have hDisj : Disjoint T P := by
    rw [hPairSpec.2]
    exact hData.2.2.1
  exact ⟨hData.1 hzT, fun hzP =>
    (Finset.disjoint_left.mp hDisj) hzT hzP⟩

/-- The completion label of an unordered root, with fallback off pairs. -/
noncomputable def dataRootLabel (D : FiniteCompletionCliqueData α)
    (fallback : α) (P : Edge α) : α :=
  if hP : P.card = 2 then
    D.label (pairRootRep P hP).1 (pairRootRep P hP).2
  else fallback

omit [Fintype α] in
theorem data_root_label_pair (D : FiniteCompletionCliqueData α)
    (fallback a b : α) (hab : a ≠ b) :
    dataRootLabel D fallback {a, b} = D.label a b := by
  classical
  have hc : ({a, b} : Edge α).card = 2 := Finset.card_pair hab
  unfold dataRootLabel
  rw [dite_eq_left hc]
  have hspec := (pair_root_rep_spec ({a, b} : Edge α) hc).2
  rcases pair_finset_eq_oriented_eq hab hspec.symm with h | h
  · exact congrArg₂ D.label h.1.symm h.2.symm
  · exact (congrArg₂ D.label h.2.symm h.1.symm).trans (D.label_symm b a)

omit [Fintype α] in
theorem data_root_label_center (D : FiniteCompletionCliqueData α)
    (fallback : α) (P : Edge α)
    (hP : P ∈ nonemptyCommonRoots D.K D.ground)
    (T : Edge α) (hT : T ∈ commonRootCell D.K D.ground P) :
    dataRootLabel D fallback P ∈ T := by
  classical
  have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  have hcell : T ∈ commonTripleCell D.K D.ground
      (pairRootRep P hc).1 (pairRootRep P hc).2 := by
    simpa only [commonRootCell, dite_eq_left hc] using hT
  simpa only [dataRootLabel, dite_eq_left hc] using
    D.label_center _ _ (pair_root_rep_spec P hc).1 T hcell

/-- The native assignment comes from the actual completion labels. -/
noncomputable def dataCenterAssignment (D : FiniteCompletionCliqueData α)
    (fallback : α) : CenterAssignment D.K D.ground where
  label := dataRootLabel D fallback
  center := data_root_label_center D fallback

omit [Fintype α] in
theorem data_root_label_valid (D : FiniteCompletionCliqueData α)
    (fallback : α) (P : Edge α)
    (hP : P ∈ nonemptyCommonRoots D.K D.ground) :
    dataRootLabel D fallback P ∈ D.ground ∧ dataRootLabel D fallback P ∉ P :=
  chosen_common_root_label_valid D.K D.ground fallback
    (dataCenterAssignment D fallback) P hP

/-- The sum of edge counts of the actual centered native graphs is
exactly the second facet-completion moment.  This is the edge-count
identity used in (III.B.8). -/
theorem native_tail_edges_eq_facet_pair_count
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : CenterAssignment K U) :
    (∑ P ∈ nonemptyCommonRoots K U,
      (nativeTailGraph K U P
        (chosenCommonRootLabel K U fallback hCenters P)).edgeFinset.card) =
      ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 := by
  classical
  calc
    (∑ P ∈ nonemptyCommonRoots K U,
      (nativeTailGraph K U P
        (chosenCommonRootLabel K U fallback hCenters P)).edgeFinset.card) =
      ∑ P ∈ nonemptyCommonRoots K U,
        (commonRootCell K U P).card := by
      apply Finset.sum_congr rfl
      intro P hP
      have hPcard : P.card = 2 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
      exact native_tail_edge_count_eq_common_root_cell K U P
        (chosenCommonRootLabel K U fallback hCenters P) hPcard
        (fun T hT => chosen_common_root_label_center
          K U fallback hCenters P hP T hT)
    _ = ∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2 :=
      used_common_root_facet_double_count K U hUniform

/-- The graph-internal degree ledger, summed over the actual labeled
common-root cells, gives the native side of (III.B.8). -/
theorem native_tail_degree_excess_facet_ledger
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : CenterAssignment K U) :
    nativeTailDegreeExcessTotal K U (nonemptyCommonRoots K U)
        (chosenCommonRootLabel K U fallback hCenters) +
      nativeTailVertexTotal K U (nonemptyCommonRoots K U)
        (chosenCommonRootLabel K U fallback hCenters) =
      2 * (∑ T ∈ U.powersetCard 3,
        (facetCompletions K U T).card.choose 2) := by
  classical
  let used := nonemptyCommonRoots K U
  let label := chosenCommonRootLabel K U fallback hCenters
  have hPoint (P : Edge α) (_hP : P ∈ used) :=
    native_degree_excess_identity (nativeTailGraph K U P (label P))
  have hSum := Finset.sum_congr rfl
    (fun P hP => hPoint P hP)
  unfold nativeTailDegreeExcessTotal nativeTailVertexTotal
  rw [Finset.sum_add_distrib] at hSum
  simp only [← Finset.mul_sum] at hSum
  rw [← native_tail_edges_eq_facet_pair_count
    K U fallback hUniform hCenters]
  simpa only [used, label] using hSum

/-- Two different common neighbors at Q force the chosen label of the
completion pair into Q. Otherwise the off-label multiplicity bound
would make those neighbors equal. -/
theorem raw_pair_two_common_neighbors_force_label_in_base
    (K : Family α) (U Q : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : CenterAssignment K U)
    (hQ : Q ∈ U.powersetCard 2)
    (a b x y : α)
    (haU : a ∈ U) (hbU : b ∈ U) (hab : a ≠ b)
    (hax : (rawPairLinkGraph K U Q).Adj a x)
    (hbx : (rawPairLinkGraph K U Q).Adj b x)
    (hay : (rawPairLinkGraph K U Q).Adj a y)
    (hby : (rawPairLinkGraph K U Q).Adj b y)
    (hxy : x ≠ y) :
    chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) ∈ Q := by
  classical
  let F := rawPairLinkGraph K U Q
  let P : Edge α := {a, b}
  have hP : P ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hab⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact haU
    · exact (Finset.mem_singleton.mp ht) ▸ hbU
  have hCell := raw_pair_common_neighbor_gives_cell
    K U Q hUniform hQ a b x haU hbU hab hax hbx
  have hUsed : P ∈ nonemptyCommonRoots K U :=
    Finset.mem_filter.mpr
      ⟨hP, Finset.card_pos.mpr ⟨insert x Q, hCell⟩⟩
  let z := chosenCommonRootLabel K U fallback hCenters P
  by_contra hzQ
  have hCenter : ∀ T ∈ commonRootCell K U P, z ∈ T := by
    intro T hT
    exact chosen_common_root_label_center
      K U fallback hCenters P hUsed T hT
  have hLe : graphCommonMultiplicity F a b ≤ 1 :=
    raw_pair_common_multiplicity_le_one_off_label
      K U Q hUniform hQ a b z haU hbU hab hzQ hCenter
  have hx : x ∈ (F.neighborFinset a).filter (fun t => F.Adj b t) :=
    Finset.mem_filter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hax, hbx⟩
  have hy : y ∈ (F.neighborFinset a).filter (fun t => F.Adj b t) :=
    Finset.mem_filter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hay, hby⟩
  exact hxy ((Finset.card_le_one.mp hLe) x hx y hy)

/-- The actual witness selection at a base pair Q. A selected vertex
has two actual completion neighbors whose pair label belongs to Q. -/
noncomputable def pairLabelWitnessSlots
    (K : Family α) (U Q : Edge α) (fallback : α)
    (hCenters : CenterAssignment K U) : Finset α :=
  U.filter fun x =>
    ∃ a b : α, a ≠ b ∧
      (rawPairLinkGraph K U Q).Adj x a ∧
      (rawPairLinkGraph K U Q).Adj x b ∧
      chosenCommonRootLabel K U fallback hCenters
        ({a, b} : Edge α) ∈ Q

theorem pair_label_witness_slots_mem
    (K : Family α) (U Q : Edge α) (fallback : α)
    (hCenters : CenterAssignment K U)
    (x : α) :
    x ∈ pairLabelWitnessSlots K U Q fallback hCenters ↔
      x ∈ U ∧ ∃ a b : α, a ≠ b ∧
        (rawPairLinkGraph K U Q).Adj x a ∧
        (rawPairLinkGraph K U Q).Adj x b ∧
        chosenCommonRootLabel K U fallback hCenters
          ({a, b} : Edge α) ∈ Q := by
  classical
  simp only [pairLabelWitnessSlots, Finset.mem_filter]

/-- At a native vertex of degree at least two, the actual pair-label
witness rule selects both completion endpoints and every common
neighbor in the corresponding pair link. -/
theorem native_high_degree_witness_slots_saturate
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : CenterAssignment K U)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α))
    (hLabel : chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) = z)
    (hHigh : 2 ≤
      (nativeTailGraph K U ({a, b} : Edge α) z).degree w) :
    let Q : Edge α := {z, w}
    let S := pairLabelWitnessSlots K U Q fallback hCenters
    a ∈ S ∧ b ∈ S ∧
      ∀ x,
        (rawPairLinkGraph K U Q).Adj a x →
        (rawPairLinkGraph K U Q).Adj b x → x ∈ S := by
  classical
  dsimp
  let Q : Edge α := {z, w}
  let S := pairLabelWitnessSlots K U Q fallback hCenters
  let F := rawPairLinkGraph K U Q
  let G := nativeTailGraph K U ({a, b} : Edge α) z
  have hQ : Q ∈ U.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hzw⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hzU
    · exact (Finset.mem_singleton.mp ht) ▸ hwU
  have hzQ : z ∈ Q := by simp [Q]
  have hCommonSelected (x : α) (hax : F.Adj a x)
      (hbx : F.Adj b x) : x ∈ S := by
    have hxU : x ∈ U :=
      ((rawPairLinkGraph_adj K U Q a x).mp hax).2.2.2.1
    exact (pair_label_witness_slots_mem K U Q fallback hCenters x).2
      ⟨hxU, a, b, hab, hax.symm, hbx.symm, by
        simpa only [hLabel] using hzQ⟩
  have hTwo : 1 < (G.neighborFinset w).card := hHigh
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hTwo
  have hGx : G.Adj w x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx
  have hGy : G.Adj w y := by
    simpa only [SimpleGraph.mem_neighborFinset] using hy
  have hCommonX : F.Adj a x ∧ F.Adj b x := by
    exact (raw_pair_common_neighbor_iff_native_neighbor
      K U hUniform a b z w x haU hbU hzU hwU
      hab hzw haQ hbQ).2 hGx
  have hCommonY : F.Adj a y ∧ F.Adj b y := by
    exact (raw_pair_common_neighbor_iff_native_neighbor
      K U hUniform a b z w y haU hbU hzU hwU
      hab hzw haQ hbQ).2 hGy
  have hxU : x ∈ U :=
    ((rawPairLinkGraph_adj K U Q a x).mp hCommonX.1).2.2.2.1
  have hyU : y ∈ U :=
    ((rawPairLinkGraph_adj K U Q a y).mp hCommonY.1).2.2.2.1
  have hxyLabel : chosenCommonRootLabel K U fallback hCenters
      ({x, y} : Edge α) ∈ Q :=
    raw_pair_two_common_neighbors_force_label_in_base
      K U Q fallback hUniform hCenters hQ x y a b
      hxU hyU hxy hCommonX.1.symm hCommonY.1.symm
      hCommonX.2.symm hCommonY.2.symm hab
  have haS : a ∈ S :=
    (pair_label_witness_slots_mem K U Q fallback hCenters a).2
      ⟨haU, x, y, hxy, hCommonX.1, hCommonY.1, hxyLabel⟩
  have hbS : b ∈ S :=
    (pair_label_witness_slots_mem K U Q fallback hCenters b).2
      ⟨hbU, x, y, hxy, hCommonX.2, hCommonY.2, hxyLabel⟩
  exact ⟨haS, hbS, hCommonSelected⟩

/-- The witness selection gives the exact local positive-excess identity
for every used completion pair and every on-label native vertex. -/
theorem witness_selected_pair_common_excess_eq_native_excess
    (K : Family α) (U : Edge α) (fallback : α)
    (hUniform : Uniform 4 K)
    (hCenters : CenterAssignment K U)
    (a b z w : α)
    (haU : a ∈ U) (hbU : b ∈ U)
    (hzU : z ∈ U) (hwU : w ∈ U)
    (hab : a ≠ b) (hzw : z ≠ w)
    (haQ : a ∉ ({z, w} : Edge α))
    (hbQ : b ∉ ({z, w} : Edge α))
    (hLabel : chosenCommonRootLabel K U fallback hCenters
      ({a, b} : Edge α) = z) :
    let Q : Edge α := {z, w}
    graphCommonMultiplicity
        (selectedRawPairLinkGraph K U Q
          (pairLabelWitnessSlots K U Q fallback hCenters)) a b - 1 =
      (nativeTailGraph K U ({a, b} : Edge α) z).degree w - 1 := by
  dsimp
  apply selected_raw_pair_common_excess_eq_native_excess
    K U (pairLabelWitnessSlots K U ({z, w} : Edge α)
      fallback hCenters) hUniform a b z w
    haU hbU hzU hwU hab hzw haQ hbQ
  intro hHigh
  exact native_high_degree_witness_slots_saturate
    K U fallback hUniform hCenters a b z w
    haU hbU hzU hwU hab hzw haQ hbQ hLabel hHigh

end JSP523.Rank4.AssignedNative
