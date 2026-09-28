import JSP523.Rank4.GraphActualEligibleSlots
import JSP523.Rank4.NativeFacetDoubleCount

/-!
# Summing selected on-label pair-link excess

The local selected/native degree identity can be summed over every
actual used completion pair and every possible native tail vertex.
Vertices with zero degree contribute zero on both sides.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The selected pair-link excess at the on-label base pair determined
by a pair root and one tail vertex. Invalid pair roots have value zero. -/
noncomputable def selectedOnLabelPairExcess
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) (w : α) : ℕ :=
  if hP : P.card = 2 then
    let ab := pairRootRep P hP
    let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
    let Q : Edge α := {z, w}
    graphCommonMultiplicity
      (selectedCompletionPairGraph D
        (actualEligiblePairSlotVertices D Q) Q) ab.1 ab.2 - 1
  else 0

/-- The on-label selected excess equals the native degree excess at
every possible tail outside the pair and its chosen center. -/
theorem selected_on_label_pair_excess_eq_native_degree_excess
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground)
    (w : α)
    (hw : w ∈ D.ground \ insert
      (chosenCommonRootLabel D.K D.ground fallback hCenters P) P) :
    selectedOnLabelPairExcess D fallback hCenters P w =
      (nativeTailGraph D.K D.ground P
        (chosenCommonRootLabel D.K D.ground fallback hCenters P)).degree w - 1 := by
  classical
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
  have hP' := Finset.mem_filter.mp hUsed
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp hP'.1).2
  let ab := pairRootRep P hPcard
  have hSpec := pairRootRep_spec P hPcard
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
    exact (chosen_common_root_label_valid
      D.K D.ground fallback hCenters P hUsed).2
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
  have hLabelPair : chosenCommonRootLabel D.K D.ground fallback hCenters
      ({ab.1, ab.2} : Edge α) = z := by
    rw [← hSpec.2]
  have hzwAB : chosenCommonRootLabel D.K D.ground fallback hCenters
      ({ab.1, ab.2} : Edge α) ≠ w := by
    rw [hLabelPair]
    exact hzw
  have haQAB : ab.1 ∉
      ({chosenCommonRootLabel D.K D.ground fallback hCenters
        ({ab.1, ab.2} : Edge α), w} : Edge α) := by
    rw [hLabelPair]
    exact haQ
  have hbQAB : ab.2 ∉
      ({chosenCommonRootLabel D.K D.ground fallback hCenters
        ({ab.1, ab.2} : Edge α), w} : Edge α) := by
    rw [hLabelPair]
    exact hbQ
  have hActual := actual_eligible_pair_common_excess_eq_native_excess
    D fallback hCenters ab.1 ab.2 w haU hbU hwU
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
    (hCenters : UniqueCommonRootCenters D.K D.ground)
    (P : Edge α) (hUsed : P ∈ nonemptyCommonRoots D.K D.ground) :
    nativeActiveVertices
        (nativeTailGraph D.K D.ground P
          (chosenCommonRootLabel D.K D.ground fallback hCenters P)) ⊆
      D.ground \ insert
        (chosenCommonRootLabel D.K D.ground fallback hCenters P) P := by
  classical
  intro w hw
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hUsed).1).2
  obtain ⟨hwU, hwP, hwz⟩ :=
    native_tail_active_vertex_support D.K D.ground P
      (chosenCommonRootLabel D.K D.ground fallback hCenters P)
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
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ w ∈ D.ground \ insert
        (chosenCommonRootLabel D.K D.ground fallback hCenters P) P,
        selectedOnLabelPairExcess D fallback hCenters P w) =
      nativeTailDegreeExcessTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) := by
  classical
  unfold nativeTailDegreeExcessTotal
  apply Finset.sum_congr rfl
  intro P hUsed
  let z := chosenCommonRootLabel D.K D.ground fallback hCenters P
  let G := nativeTailGraph D.K D.ground P z
  calc
    (∑ w ∈ D.ground \ insert z P,
      selectedOnLabelPairExcess D fallback hCenters P w) =
      ∑ w ∈ D.ground \ insert z P, (G.degree w - 1) := by
        have hPoint : ∀ w ∈ D.ground \ insert z P,
            selectedOnLabelPairExcess D fallback hCenters P w =
              G.degree w - 1 := by
          intro w hw
          exact selected_on_label_pair_excess_eq_native_degree_excess
            D fallback hCenters P hUsed w hw
        exact Finset.sum_congr rfl hPoint
    _ = (nativeActiveVertices G).sum (fun w => G.degree w - 1) := by
      have hSub := native_active_vertices_subset_on_label_tails
        D fallback hCenters P hUsed
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
    (D : FiniteCompletionCliqueData α) (fallback : α)
    (hCenters : UniqueCommonRootCenters D.K D.ground) :
    (∑ P ∈ nonemptyCommonRoots D.K D.ground,
      ∑ w ∈ D.ground \ insert
        (chosenCommonRootLabel D.K D.ground fallback hCenters P) P,
        selectedOnLabelPairExcess D fallback hCenters P w) +
      nativeTailVertexTotal D.K D.ground
        (nonemptyCommonRoots D.K D.ground)
        (chosenCommonRootLabel D.K D.ground fallback hCenters) =
      2 * (∑ T ∈ D.ground.powersetCard 3,
        (facetCompletions D.K D.ground T).card.choose 2) := by
  rw [selected_on_label_excess_total_eq_native_degree_excess_total
    D fallback hCenters]
  exact native_tail_degree_excess_facet_ledger
    D.K D.ground fallback D.uniform_four hCenters

end JSP523.Rank4
