import JSP523.Rank4.GraphAssignedNativeSlots

/-! # Native representation using the actual completion labels -/

namespace JSP523.Rank4.AssignedNative

variable {α : Type*} [Fintype α] [DecidableEq α]


/-- The selected pair-link excess at the on-label base pair determined
by a pair root and one tail vertex. Invalid pair roots have value zero. -/
noncomputable def selectedOnLabelPairExcess
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) (w : α) : ℕ :=
  if hP : P.card = 2 then
    let ab := pairRootRep P hP
    let z := dataRootLabel D fallback P
    let Q : Edge α := {z, w}
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) ab.1 ab.2 - 1
  else 0

/-- The on-label selected excess equals the native degree excess at
every possible tail outside the pair and its chosen center. -/
theorem selected_on_label_pair_excess_eq_native_degree_excess
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground)
    (w : α)
    (hw : w ∈ D.ground \ insert
      (dataRootLabel D fallback P) P) :
    selectedOnLabelPairExcess D fallback P w =
      (nativeTailGraph D.K D.ground P
        (dataRootLabel D fallback P)).degree w - 1 := by
  classical
  let z := dataRootLabel D fallback P
  have hP' := Finset.mem_filter.mp hUsed
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hP'.1).2
  let ab := pairRootRep P hPcard
  have hSpec := pair_root_rep_spec P hPcard
  have haP : ab.1 ∈ P := by
    rw [hSpec.2]
    simp [ab]
  have hbP : ab.2 ∈ P := by
    rw [hSpec.2]
    simp [ab]
  have haU : ab.1 ∈ D.ground :=
    (Finset.mem_powersetCard.mp hP'.1).1 haP
  have hbU : ab.2 ∈ D.ground :=
    (Finset.mem_powersetCard.mp hP'.1).1 hbP
  have hw' := Finset.mem_sdiff.mp hw
  have hwU : w ∈ D.ground := hw'.1
  have hwNot : w ∉ insert z P := hw'.2
  have hzP : z ∉ P := by
    exact (data_root_label_valid
      D fallback P hUsed).2
  have hzw : z ≠ w := by
    intro h
    exact hwNot (by simp [h])
  have haQ : ab.1 ∉ ({z, w} : Edge α) := by
    intro h
    rcases Finset.mem_insert.mp h with haz | haw
    · exact hzP (haz ▸ haP)
    · have haw' : ab.1 = w := Finset.mem_singleton.mp haw
      exact hwNot (Finset.mem_insert_of_mem (haw' ▸ haP))
  have hbQ : ab.2 ∉ ({z, w} : Edge α) := by
    intro h
    rcases Finset.mem_insert.mp h with hbz | hbw
    · exact hzP (hbz ▸ hbP)
    · have hbw' : ab.2 = w := Finset.mem_singleton.mp hbw
      exact hwNot (Finset.mem_insert_of_mem (hbw' ▸ hbP))
  have hUsedAB : ({ab.1, ab.2} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground := by
    rw [← hSpec.2]
    exact hUsed
  have hLabelPair : dataRootLabel D fallback
      ({ab.1, ab.2} : Edge α) = z := by
    rw [← hSpec.2]
  have hzwAB : dataRootLabel D fallback
      ({ab.1, ab.2} : Edge α) ≠ w := by
    rw [hLabelPair]
    exact hzw
  have haQAB : ab.1 ∉
      ({dataRootLabel D fallback
        ({ab.1, ab.2} : Edge α), w} : Edge α) := by
    rw [hLabelPair]
    exact haQ
  have hbQAB : ab.2 ∉
      ({dataRootLabel D fallback
        ({ab.1, ab.2} : Edge α), w} : Edge α) := by
    rw [hLabelPair]
    exact hbQ
  have hActual := actual_eligible_pair_common_excess_eq_native_excess
    D fallback ab.1 ab.2 w haU hbU hwU
    hSpec.1 hUsedAB hzwAB haQAB hbQAB
  dsimp only at hActual
  rw [hLabelPair] at hActual
  unfold selectedOnLabelPairExcess
  rw [dite_eq_left hPcard]
  change graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D ({z, w} : Edge α))
        ({z, w} : Edge α)) ab.1 ab.2 - 1 =
      (nativeTailGraph D.K D.ground P z).degree w - 1
  rw [hSpec.2]
  simpa only [ab] using hActual

/-- Nonisolated vertices of a used pair's native graph lie in the
finite set over which the on-label excess is summed. -/
theorem native_active_vertices_subset_on_label_tails
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground) :
    nativeActiveVertices
        (nativeTailGraph D.K D.ground P
          (dataRootLabel D fallback P)) ⊆
      D.ground \ insert
        (dataRootLabel D fallback P) P := by
  classical
  intro w hw
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).2
  obtain ⟨hwU, hwP, hwz⟩ :=
    native_tail_active_vertex_support D.K D.ground P
      (dataRootLabel D fallback P)
      w hPcard hw
  exact Finset.mem_sdiff.mpr
    ⟨hwU, by
      intro hIns
      rcases Finset.mem_insert.mp hIns with hwz' | hwP'
      · exact hwz hwz'
      · exact hwP hwP'⟩

/-- All on-label selected pair-link excess equals the actual native
degree-excess total, summed over every used pair. -/
theorem selected_on_label_excess_total_eq_native_degree_excess_total
    (D : FiniteCompletionCliqueData α) (fallback : α) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ w ∈ D.ground \ insert
        (dataRootLabel D fallback P) P,
        selectedOnLabelPairExcess D fallback P w) =
      nativeTailDegreeExcessTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) := by
  classical
  unfold nativeTailDegreeExcessTotal
  apply Finset.sum_congr rfl
  intro P hUsed
  let z := dataRootLabel D fallback P
  let G := nativeTailGraph D.K D.ground P z
  calc
    (∑ w ∈ D.ground \ insert z P,
      selectedOnLabelPairExcess D fallback P w) =
      ∑ w ∈ D.ground \ insert z P, (G.degree w - 1) := by
        have hPoint : ∀ w ∈ D.ground \ insert z P,
            selectedOnLabelPairExcess D fallback P w =
              G.degree w - 1 := by
          intro w hw
          exact selected_on_label_pair_excess_eq_native_degree_excess
            D fallback P hUsed w hw
        exact Finset.sum_congr rfl hPoint
    _ = (nativeActiveVertices G).sum (fun w => G.degree w - 1) := by
      have hSub := native_active_vertices_subset_on_label_tails
        D fallback P hUsed
      have hZeroOutside : ∀ w ∈ D.ground \ insert z P,
          w ∉ nativeActiveVertices G → G.degree w - 1 = 0 := by
        intro w hwTail hwNotActive
        have hZero : G.degree w = 0 := by
          have hNotPos : ¬ 0 < G.degree w := by
            intro hPos
            exact hwNotActive (Finset.mem_filter.mpr
              ⟨Finset.mem_univ w, hPos⟩)
          omega
        simp [hZero]
      have hSum := Finset.sum_subset hSub hZeroOutside
      simpa only [z, G] using hSum.symm

/-- The selected on-label excess and the active native vertices sum to
twice the actual completion-pair count over all triple facets. This is
the native side of (III.B.8) with the manuscript's selected graphs. -/
theorem selected_on_label_excess_facet_ledger
    (D : FiniteCompletionCliqueData α) (fallback : α) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ w ∈ D.ground \ insert
        (dataRootLabel D fallback P) P,
        selectedOnLabelPairExcess D fallback P w) +
      nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) =
      2 * (∑ T ∈ D.ground.powersetCard 3,
        (facetCompletions D.K D.ground T).card.choose 2) := by
  rw [selected_on_label_excess_total_eq_native_degree_excess_total
    D fallback]
  exact native_tail_degree_excess_facet_ledger
    D.K D.ground fallback D.uniform_four (dataCenterAssignment D fallback)


omit [Fintype α] in
/-- The base pairs containing the chosen label and disjoint from a used
completion pair are precisely the pairs obtained from admissible native
tail vertices. -/
theorem on_label_pair_bases_eq_tail_image
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground) :
    let z := dataRootLabel D fallback P
    (D.ground \ insert z P).image
      (fun w => ({z, w} : Edge α)) =
      (D.ground.powersetCard 2).filter
        (fun Q => z ∈ Q ∧ Disjoint Q P) := by
  classical
  dsimp only
  let z := dataRootLabel D fallback P
  change (D.ground \ insert z P).image
      (fun w => ({z, w} : Edge α)) =
    (D.ground.powersetCard 2).filter
      (fun Q => z ∈ Q ∧ Disjoint Q P)
  have hzU : z ∈ D.ground :=
    (data_root_label_valid
      D fallback P hUsed).1
  have hzP : z ∉ P :=
    (data_root_label_valid
      D fallback P hUsed).2
  ext Q
  constructor
  · intro hQ
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hQ
    have hw' := Finset.mem_sdiff.mp hw
    have hwU : w ∈ D.ground := hw'.1
    have hwz : w ≠ z := by
      intro h
      subst w
      exact hw'.2 (Finset.mem_insert_self z P)
    have hwP : w ∉ P := by
      intro h
      exact hw'.2 (Finset.mem_insert_of_mem h)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hwz.symm⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hzU
      · exact (Finset.mem_singleton.mp ht) ▸ hwU
    · constructor
      · exact Finset.mem_insert_self z _
      · apply Finset.disjoint_left.mpr
        intro t ht htP
        rcases Finset.mem_insert.mp ht with htz | htw
        · exact hzP (htz ▸ htP)
        · exact hwP ((Finset.mem_singleton.mp htw) ▸ htP)
  · intro hQ
    obtain ⟨hQpair, hzQ, hDisj⟩ := Finset.mem_filter.mp hQ
    have hQ' := Finset.mem_powersetCard.mp hQpair
    have hEraseCard : (Q.erase z).card = 1 := by
      rw [Finset.card_erase_of_mem hzQ, hQ'.2]
    obtain ⟨w, hwEq⟩ := Finset.card_eq_one.mp hEraseCard
    have hwErase : w ∈ Q.erase z := by simp [hwEq]
    have hwQ : w ∈ Q := (Finset.mem_erase.mp hwErase).2
    have hwz : w ≠ z := (Finset.mem_erase.mp hwErase).1
    have hwU : w ∈ D.ground := hQ'.1 hwQ
    have hwP : w ∉ P := by
      intro hwP
      exact (Finset.disjoint_left.mp hDisj) hwQ hwP
    have hwTail : w ∈ D.ground \ insert z P :=
      Finset.mem_sdiff.mpr
        ⟨hwU, by
          intro hIns
          rcases Finset.mem_insert.mp hIns with hwz' | hwP'
          · exact hwz hwz'
          · exact hwP hwP'⟩
    have hQeq : Q = ({z, w} : Edge α) := by
      calc
        Q = insert z (Q.erase z) := (Finset.insert_erase hzQ).symm
        _ = {z, w} := by rw [hwEq]
    apply Finset.mem_image.mpr
    exact ⟨w, hwTail, hQeq.symm⟩

omit [Fintype α] in
/-- The map from an admissible tail vertex to its on-label base pair is
injective on the finite tail set. -/
theorem on_label_tail_pair_map_inj_on
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) :
    let z := dataRootLabel D fallback P
    Set.InjOn (fun w => ({z, w} : Edge α))
      ((D.ground \ insert z P : Finset α) : Set α) := by
  classical
  dsimp only
  let z := dataRootLabel D fallback P
  change Set.InjOn (fun w => ({z, w} : Edge α))
    ((D.ground \ insert z P : Finset α) : Set α)
  intro w hw w' hw' hPairs
  have hwz : z ∉ ({w} : Edge α) := by
    intro h
    have hzw : z = w := Finset.mem_singleton.mp h
    exact (Finset.mem_sdiff.mp hw).2 (by simp [hzw])
  have hwz' : z ∉ ({w'} : Edge α) := by
    intro h
    have hzw' : z = w' := Finset.mem_singleton.mp h
    exact (Finset.mem_sdiff.mp hw').2 (by simp [hzw'])
  have hErase := congrArg (fun Q : Edge α => Q.erase z) hPairs
  simpa [Finset.erase_insert hwz, Finset.erase_insert hwz'] using hErase


omit [Fintype α] in
/-- Reindex any finite sum over on-label base pairs by its unique tail
vertex. -/
theorem on_label_pair_bases_sum_eq_tail_sum
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground)
    (f : Edge α → ℕ) :
    let z := dataRootLabel D fallback P
    ((D.ground.powersetCard 2).filter
      (fun Q => z ∈ Q ∧ Disjoint Q P)).sum f =
      (D.ground \ insert z P).sum
        (fun w => f ({z, w} : Edge α)) := by
  classical
  dsimp only
  let z := dataRootLabel D fallback P
  change ((D.ground.powersetCard 2).filter
      (fun Q => z ∈ Q ∧ Disjoint Q P)).sum f =
    (D.ground \ insert z P).sum
      (fun w => f ({z, w} : Edge α))
  rw [← on_label_pair_bases_eq_tail_image D fallback P hUsed]
  exact Finset.sum_image
    (on_label_tail_pair_map_inj_on D fallback P)


/-- Away from an on-label, disjoint base pair, actual selected common
multiplicity contributes zero positive excess. -/
theorem actual_selected_pair_excess_zero_off_support
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (a b : α) (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hOff : dataRootLabel D fallback
      ({a, b} : Edge α) ∉ Q ∨
      ¬ Disjoint Q ({a, b} : Edge α)) :
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b - 1 = 0 := by
  classical
  rcases hOff with hzQ | hInter
  · have hAtMost := actual_eligible_pair_common_le_one_off_label
      D Q hQ fallback a b haU hbU hab hUsed hzQ
    omega
  · obtain ⟨x, hxQ, hxP⟩ := Finset.not_disjoint_iff.mp hInter
    have hxPair : x = a ∨ x = b := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxP
    rcases hxPair with hxa | hxb
    · have haQ : a ∈ Q := hxa.symm ▸ hxQ
      rw [actual_selected_common_zero_of_left_mem_base D Q a b haQ]
    · have hbQ : b ∈ Q := hxb.symm ▸ hxQ
      rw [actual_selected_common_zero_of_right_mem_base D Q a b hbQ]

/-- The same support statement phrased with a positive excess:
the base pair must contain the label and omit both endpoints. -/
theorem actual_selected_pair_positive_excess_support
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (a b : α) (haU : a ∈ D.ground) (hbU : b ∈ D.ground)
    (hab : a ≠ b)
    (hUsed : ({a, b} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground)
    (hPos : 0 < graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) a b - 1) :
    dataRootLabel D fallback
      ({a, b} : Edge α) ∈ Q ∧
      Disjoint Q ({a, b} : Edge α) := by
  by_contra h
  have hOff : dataRootLabel D fallback
      ({a, b} : Edge α) ∉ Q ∨
      ¬ Disjoint Q ({a, b} : Edge α) := by
    exact not_and_or.mp h
  have hZero := actual_selected_pair_excess_zero_off_support
    D fallback Q hQ a b haU hbU hab hUsed hOff
  omega

/-- At a used completion pair, the selected excess over all valid base
pairs equals the sum of its on-label excess over admissible native tails. -/
theorem actual_selected_excess_over_bases_eq_on_label_tails
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground) :
    (D.ground.powersetCard 2).sum
      (fun Q => actualSelectedPairExcessAtBase D Q P) =
      (D.ground \ insert
        (dataRootLabel D fallback P) P).sum
        (fun w => selectedOnLabelPairExcess D fallback P w) := by
  classical
  let z := dataRootLabel D fallback P
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).2
  let ab := pairRootRep P hPcard
  have hSpec := pair_root_rep_spec P hPcard
  have haP : ab.1 ∈ P := by rw [hSpec.2]; simp [ab]
  have hbP : ab.2 ∈ P := by rw [hSpec.2]; simp [ab]
  have hPsub : P ⊆ D.ground :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).1
  have haU : ab.1 ∈ D.ground := hPsub haP
  have hbU : ab.2 ∈ D.ground := hPsub hbP
  have hUsedAB : ({ab.1, ab.2} : Edge α) ∈
      nonemptyCommonRoots D.K D.ground := by
    rw [← hSpec.2]
    exact hUsed
  let S := (D.ground.powersetCard 2).filter
    (fun Q => z ∈ Q ∧ Disjoint Q P)
  have hZeroOutside : ∀ Q ∈ D.ground.powersetCard 2,
      Q ∉ S → actualSelectedPairExcessAtBase D Q P = 0 := by
    intro Q hQ hNot
    have hOff : z ∉ Q ∨ ¬ Disjoint Q P := by
      by_contra h
      have hzQ : z ∈ Q := by
        by_contra hz
        exact h (Or.inl hz)
      have hDisj : Disjoint Q P := by
        by_contra hd
        exact h (Or.inr hd)
      exact hNot (Finset.mem_filter.mpr ⟨hQ, hzQ, hDisj⟩)
    have hZero := actual_selected_pair_excess_zero_off_support
      D fallback Q hQ ab.1 ab.2 haU hbU hSpec.1
      hUsedAB (by
        rw [← hSpec.2]
        exact hOff)
    unfold actualSelectedPairExcessAtBase
    rw [dite_eq_left hPcard]
    simpa only [ab] using hZero
  have hRestrict :
      S.sum (fun Q => actualSelectedPairExcessAtBase D Q P) =
        (D.ground.powersetCard 2).sum
          (fun Q => actualSelectedPairExcessAtBase D Q P) :=
    Finset.sum_subset (Finset.filter_subset _ _) hZeroOutside
  have hReindex := on_label_pair_bases_sum_eq_tail_sum
    D fallback P hUsed
      (fun Q => actualSelectedPairExcessAtBase D Q P)
  change S.sum (fun Q => actualSelectedPairExcessAtBase D Q P) =
    (D.ground \ insert z P).sum
      (fun w => actualSelectedPairExcessAtBase D ({z, w} : Edge α) P)
    at hReindex
  have hTail : (D.ground \ insert z P).sum
      (fun w => actualSelectedPairExcessAtBase D ({z, w} : Edge α) P) =
      (D.ground \ insert z P).sum
        (fun w => selectedOnLabelPairExcess D fallback P w) := by
    apply Finset.sum_congr rfl
    intro w _
    unfold actualSelectedPairExcessAtBase selectedOnLabelPairExcess
    rw [dite_eq_left hPcard]
  exact hRestrict.symm.trans (hReindex.trans hTail)


/-- The actual selected multiplicity excess, summed over used
completion pairs and all valid base pairs, is the native degree excess. -/
theorem actual_selected_excess_used_total_eq_native_degree_excess_total
    (D : FiniteCompletionCliqueData α) (fallback : α) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ Q ∈ D.ground.powersetCard 2,
        actualSelectedPairExcessAtBase D Q P) =
      nativeTailDegreeExcessTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) := by
  rw [← selected_on_label_excess_total_eq_native_degree_excess_total
    D fallback]
  apply Finset.sum_congr rfl
  intro P hUsed
  exact actual_selected_excess_over_bases_eq_on_label_tails
    D fallback P hUsed

/-- The actual selected excess plus the native active-vertex count is
twice the number of completion pairs over actual triple facets. -/
theorem actual_selected_excess_plus_native_vertices_eq_facet_pairs
    (D : FiniteCompletionCliqueData α) (fallback : α) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ Q ∈ D.ground.powersetCard 2,
        actualSelectedPairExcessAtBase D Q P) +
      nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) =
      2 * (∑ T ∈ D.ground.powersetCard 3,
        (facetCompletions D.K D.ground T).card.choose 2) := by
  rw [actual_selected_excess_used_total_eq_native_degree_excess_total
    D fallback]
  exact native_tail_degree_excess_facet_ledger
    D.K D.ground fallback D.uniform_four (dataCenterAssignment D fallback)

/-- The common-pair multiplicity excess in the actual selected links
is the native tail degree excess. -/
theorem actual_selected_common_excess_eq_native_tail_degree_excess
    (D : FiniteCompletionCliqueData α) (fallback : α) :
    actualSelectedCommonExcessTotal D =
      nativeTailDegreeExcessTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) := by
  classical
  calc
    actualSelectedCommonExcessTotal D =
        ∑ Q ∈ D.ground.powersetCard 2,
          ∑ P ∈ nonemptyCommonRoots D.K D.ground,
            actualSelectedPairExcessAtBase D Q P := by
      unfold actualSelectedCommonExcessTotal
      apply Finset.sum_congr rfl
      intro Q hQ
      exact actual_unordered_excess_eq_used_pair_sum D Q hQ
    _ = ∑ P ∈ nonemptyCommonRoots D.K D.ground,
          ∑ Q ∈ D.ground.powersetCard 2,
            actualSelectedPairExcessAtBase D Q P := by
      rw [Finset.sum_comm]
    _ = _ := actual_selected_excess_used_total_eq_native_degree_excess_total
      D fallback

/-- The exact finite native representation (III.B.8), in additive
form: `W+V = Σ_Q q(F_Q)+2R₃`. -/
theorem actual_native_representation_iii_b8
    (D : FiniteCompletionCliqueData α) (fallback : α) :
    actualSelectedDegreePairTotal D +
      nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (dataRootLabel D fallback) =
      actualSelectedCommonPairTotal D +
        2 * (∑ T ∈ D.ground.powersetCard 3,
          (facetCompletions D.K D.ground T).card.choose 2) := by
  classical
  have hGraph := actual_selected_degree_pairs_eq_common_pairs_add_excess D
  have hExcess := actual_selected_common_excess_eq_native_tail_degree_excess
    D fallback
  have hNative := native_tail_degree_excess_facet_ledger
    D.K D.ground fallback D.uniform_four (dataCenterAssignment D fallback)
  simp only [chosenCommonRootLabel, dataCenterAssignment] at hNative
  rw [hExcess] at hGraph
  omega

end JSP523.Rank4.AssignedNative
