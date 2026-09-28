import JSP523.Rank4.GraphActualColoredPayment
import JSP523.Rank4.GraphColoredActualRecords

/-!
# Unoriented unique-pair keys over actual base pairs

The graph record bound can be applied to a finite family of base pairs
without replacing the base-dependent selected graphs by one global
selected vertex set.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Removing any vertex from a facet gives an actual base pair. -/
theorem facet_erase_vertex_mem_ground_pairs
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (z : α) (hz : z ∈ T) :
    T.erase z ∈ D.ground.powersetCard 2 := by
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact (Finset.erase_subset z T).trans hTsub
  · rw [Finset.card_erase_of_mem hz, hTcard]

/-- An unoriented record key `(Q,P)` with a unique common neighbor in
the graph assigned to `Q` consumes two directed unique-pair records. -/
theorem finite_unique_unordered_keys_le_half_ordered
    (C : Finset (Edge α))
    (F : Edge α → SimpleGraph α)
    [∀ Q, DecidableRel (F Q).Adj]
    (R : Finset (Edge α × Edge α))
    (hOwner : ∀ p ∈ R, p.1 ∈ C)
    (hPairCard : ∀ p ∈ R, p.2.card = 2)
    (hUnique : ∀ (p : Edge α × Edge α) (hp : p ∈ R),
      graphCommonMultiplicity (F p.1)
        (pairRootRep p.2 (hPairCard p hp)).1
        (pairRootRep p.2 (hPairCard p hp)).2 = 1) :
    (R.card : ℚ) ≤
      (∑ Q ∈ C, orderedUniquePairCount (F Q)) / 2 := by
  classical
  let β := {Q : Edge α // Q ∈ C}
  let ρ := {p : Edge α × Edge α // p ∈ R}
  let G : β → SimpleGraph α := fun q => F q.1
  let owner : ρ → β := fun p => ⟨p.1.1, hOwner p.1 p.2⟩
  let ends : ρ → α × α := fun p =>
    pairRootRep p.1.2 (hPairCard p.1 p.2)
  have hNe : ∀ p : ρ, (ends p).1 ≠ (ends p).2 := by
    intro p
    exact (pair_root_rep_spec p.1.2 (hPairCard p.1 p.2)).1
  have hUni : ∀ p : ρ,
      graphCommonMultiplicity (G (owner p))
        (ends p).1 (ends p).2 = 1 := by
    intro p
    exact hUnique p.1 p.2
  have hOrient : Function.Injective (fun ro : ρ × Bool =>
      (owner ro.1, if ro.2 then (ends ro.1).swap else ends ro.1)) := by
    intro ⟨p, o⟩ ⟨q, o'⟩ h
    have hOwnerEq : owner p = owner q := congrArg Prod.fst h
    have hEnds : (if o then (ends p).swap else ends p) =
        (if o' then (ends q).swap else ends q) := congrArg Prod.snd h
    have hQ : p.1.1 = q.1.1 := congrArg Subtype.val hOwnerEq
    let pairSet : α × α → Edge α := fun ab => {ab.1, ab.2}
    have hSwap (ab : α × α) : pairSet ab = pairSet ab.swap := by
      ext x
      simp [pairSet, or_comm]
    have hLeft : pairSet (ends p) =
        pairSet (if o then (ends p).swap else ends p) := by
      cases o
      · rfl
      · exact hSwap (ends p)
    have hRight : pairSet (if o' then (ends q).swap else ends q) =
        pairSet (ends q) := by
      cases o'
      · rfl
      · exact (hSwap (ends q)).symm
    have hPair : p.1.2 = q.1.2 := by
      calc
        p.1.2 = pairSet (ends p) :=
          (pair_root_rep_spec p.1.2 (hPairCard p.1 p.2)).2
        _ = pairSet (ends q) := hLeft.trans ((congrArg pairSet hEnds).trans hRight)
        _ = q.1.2 :=
          (pair_root_rep_spec q.1.2 (hPairCard q.1 q.2)).2.symm
    have hpq : p = q := by
      apply Subtype.ext
      exact Prod.ext hQ hPair
    subst q
    have hoo : o = o' := by
      cases o <;> cases o'
      · rfl
      · have hEq := congrArg Prod.fst hEnds
        have hBad : (ends p).1 = (ends p).2 := by
          simpa [Prod.swap] using hEq
        exact (hNe p hBad).elim
      · have hEq := congrArg Prod.fst hEnds
        have hBad : (ends p).2 = (ends p).1 := by
          simpa [Prod.swap] using hEq
        exact (hNe p hBad.symm).elim
      · rfl
    exact congrArg (fun z : Bool => (p, z)) hoo
  have hBound := undirected_record_family_le_half_ordered_count
    G owner ends hNe hUni hOrient
  have hCard : Fintype.card ρ = R.card := by
    simp [ρ]
  have hSum : (∑ q : β, orderedUniquePairCount (G q)) =
      ∑ Q ∈ C, orderedUniquePairCount (F Q) := by
    exact (Finset.sum_subtype C (by intro Q; rfl)
      (fun Q => orderedUniquePairCount (F Q))).symm
  rw [hCard, hSum] at hBound
  exact hBound

/-- The actual unoriented unique-pair records, using the selected
vertex set belonging to each base pair separately. -/
noncomputable def actualUniquePairRecordKeys
    (D : FiniteCompletionCliqueData α) :
    Finset (Edge α × Edge α) := by
  classical
  exact ((D.ground.powersetCard 2).product
    ((Finset.univ : Finset α).powersetCard 2)).filter fun p =>
      if hP : p.2.card = 2 then
        graphCommonMultiplicity
          (selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D p.1) p.1)
          (pairRootRep p.2 hP).1 (pairRootRep p.2 hP).2 = 1
      else False

/-- The actual unoriented record set is paid by the directed unique
records counted in the graph-potential sum. -/
theorem actual_unique_pair_record_keys_card_le
    (D : FiniteCompletionCliqueData α) :
    ((actualUniquePairRecordKeys D).card : ℚ) ≤
      (∑ Q ∈ D.ground.powersetCard 2,
        orderedUniquePairCount
          (selectedCompletionPairGraph D
            (actualEligiblePairSlotVertices D Q) Q)) / 2 := by
  classical
  let C := D.ground.powersetCard 2
  let F : Edge α → SimpleGraph α := fun Q =>
    selectedCompletionPairGraph D (actualEligiblePairSlotVertices D Q) Q
  let R := actualUniquePairRecordKeys D
  have hOwner : ∀ p ∈ R, p.1 ∈ C := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hPairCard : ∀ p ∈ R, p.2.card = 2 := by
    intro p hp
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2).2
  have hUnique : ∀ (p : Edge α × Edge α) (hp : p ∈ R),
      graphCommonMultiplicity (F p.1)
        (pairRootRep p.2 (hPairCard p hp)).1
        (pairRootRep p.2 (hPairCard p hp)).2 = 1 := by
    intro p hp
    have hPred := (Finset.mem_filter.mp hp).2
    simpa [actualUniquePairRecordKeys, hPairCard p hp, F] using hPred
  exact finite_unique_unordered_keys_le_half_ordered
    C F R hOwner hPairCard hUnique

/-- Actual form of (III.B.10): the graph potentials pay half of all
unoriented unique-pair keys and the fully selected colored marks. -/
theorem actual_colored_unique_record_payment
    (D : FiniteCompletionCliqueData α) :
    ((actualUniquePairRecordKeys D).card : ℚ) / 2 +
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedThreeSlots D Q).card : ℚ)) / 2 +
      (∑ Q ∈ D.ground.powersetCard 2,
        ((actualColoredMarkedFourSlots D Q).card : ℚ)) ≤
    actualSelectedPotentialTotal D := by
  have hRecord := actual_unique_pair_record_keys_card_le D
  have hGraph := actual_colored_marked_total_payment D
  linarith

/-- A completion record selected at its own base pair belongs to the
base-dependent actual unique-pair ledger. -/
theorem selected_record_at_own_base_mem_actual_unique
    (D : FiniteCompletionCliqueData α)
    (Q P : Edge α)
    (hQ : Q ∈ D.ground.powersetCard 2)
    (hSelected : (Q, P) ∈
      selectedUndirectedCompletionRecordKeys D
        (actualEligiblePairSlotVertices D Q)) :
    (Q, P) ∈ actualUniquePairRecordKeys D := by
  classical
  let S := actualEligiblePairSlotVertices D Q
  obtain ⟨key, hKey, hKeyEq⟩ := Finset.mem_image.mp hSelected
  obtain ⟨i, _hi, hRecEq⟩ := Finset.mem_image.mp hKey
  have hOwnerEq :
      i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2) = Q := by
    have h1 := congrArg Prod.fst hRecEq
    have h2 := congrArg Prod.fst hKeyEq
    exact h1.trans h2
  have hEndsEq : i.val.val.2 = key.2 := by
    simpa [actualCompletionRecord] using congrArg Prod.snd hRecEq
  have hPairEq :
      ({i.val.val.2.1, i.val.val.2.2} : Edge α) = P := by
    calc
      ({i.val.val.2.1, i.val.val.2.2} : Edge α) =
          ({key.2.1, key.2.2} : Edge α) := by rw [hEndsEq]
      _ = P := congrArg Prod.snd hKeyEq
  have hPcard : P.card = 2 := by
    rw [← hPairEq]
    exact Finset.card_pair i.val.property.2.2.2.2
  have hUniqueAt := actual_selected_completion_record_unique
    D i.val S i.property.1 i.property.2.1 i.property.2.2
  rw [hOwnerEq] at hUniqueAt
  change graphCommonMultiplicity (selectedCompletionPairGraph D S Q)
    i.val.val.2.1 i.val.val.2.2 = 1 at hUniqueAt
  have hRepSpec := pair_root_rep_spec P hPcard
  have hOrient := pair_finset_eq_oriented_eq hRepSpec.1
    (hPairEq.trans hRepSpec.2)
  have hUniqueRep : graphCommonMultiplicity
      (selectedCompletionPairGraph D S Q)
      (pairRootRep P hPcard).1 (pairRootRep P hPcard).2 = 1 := by
    rcases hOrient with hSame | hSwap
    · rw [hSame.1, hSame.2]
      exact hUniqueAt
    · rw [hSwap.1, hSwap.2, graph_common_multiplicity_symm]
      exact hUniqueAt
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr
    ⟨hQ, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hPcard⟩⟩, ?_⟩
  simpa [actualUniquePairRecordKeys, hPcard, S] using hUniqueRep

/-- Any finite collection of selected records all owned by the same
base pair embeds into the actual base-dependent unique ledger. -/
theorem selected_own_base_records_subset_actual_unique
    (D : FiniteCompletionCliqueData α)
    (Q : Edge α) (hQ : Q ∈ D.ground.powersetCard 2)
    (R : Finset (Edge α × Edge α))
    (hSelected : R ⊆ selectedUndirectedCompletionRecordKeys D
      (actualEligiblePairSlotVertices D Q))
    (hBase : ∀ r ∈ R, r.1 = Q) :
    R ⊆ actualUniquePairRecordKeys D := by
  intro r hr
  obtain ⟨Q', P⟩ := r
  have hQ' := hBase (Q', P) hr
  change Q' = Q at hQ'
  subst Q'
  exact selected_record_at_own_base_mem_actual_unique
    D Q P hQ (hSelected hr)

/-- Surviving triangle color-slot records enter the actual unique
ledger for their own base pair. -/
theorem selected_triangle_color_records_subset_actual_unique
    (D : FiniteCompletionCliqueData α)
    (T Q : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (x : CliqueColor)
    (S₀ : Finset (Fin 3))
    (hQ : Q ∈ D.ground.powersetCard 2)
    (hBase : T.erase (mark x) = Q)
    (hMark : mark x ∈ actualEligiblePairSlotVertices D Q)
    (hSelected : ∀ i ∈ S₀,
      v i ∈ actualEligiblePairSlotVertices D Q)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    selectedActualTriangleUndirectedColorSlotRecords
      D T v mark x S₀ ⊆ actualUniquePairRecordKeys D := by
  classical
  let R := selectedActualTriangleUndirectedColorSlotRecords D T v mark x S₀
  have hRselected : R ⊆ selectedUndirectedCompletionRecordKeys D
      (actualEligiblePairSlotVertices D Q) :=
    selected_actual_triangle_undirected_records_subset_global
      D T v mark x (actualEligiblePairSlotVertices D Q) S₀
        hMark hSelected hTcard hTsub hCompletion hv
  have hRbase : ∀ r ∈ R, r.1 = Q := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hLabel := (Finset.mem_filter.mp hi).2.1
    simp [actualTriangleUndirectedRecordKey,
      completionTriangleRecordKeys, completionPairRecord,
      completionRecordForgetOrientation, hLabel, hBase]
  exact selected_own_base_records_subset_actual_unique
    D Q hQ R hRselected hRbase

/-- Surviving proper-K4 color-slot records enter the actual unique
ledger for their own base pair. -/
theorem selected_k4_color_records_subset_actual_unique
    (D : FiniteCompletionCliqueData α)
    (T Q : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (x : CliqueColor)
    (S₀ : Finset (Fin 4))
    (hQ : Q ∈ D.ground.powersetCard 2)
    (hBase : T.erase (mark x) = Q)
    (hMark : mark x ∈ actualEligiblePairSlotVertices D Q)
    (hSelected : ∀ i ∈ S₀,
      v i ∈ actualEligiblePairSlotVertices D Q)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    selectedActualK4UndirectedColorSlotRecords
      D T v mark x S₀ ⊆ actualUniquePairRecordKeys D := by
  classical
  let R := selectedActualK4UndirectedColorSlotRecords D T v mark x S₀
  have hRselected : R ⊆ selectedUndirectedCompletionRecordKeys D
      (actualEligiblePairSlotVertices D Q) :=
    selected_actual_k4_undirected_records_subset_global
      D T v mark x (actualEligiblePairSlotVertices D Q) S₀
        hMark hSelected hTcard hTsub hCompletion hv
  have hRbase : ∀ r ∈ R, r.1 = Q := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hLabel := (Finset.mem_filter.mp hi).2.1
    simp [actualK4UndirectedRecordKey,
      completionK4RecordKeys, completionPairRecord,
      completionRecordForgetOrientation, hLabel, hBase]
  exact selected_own_base_records_subset_actual_unique
    D Q hQ R hRselected hRbase

end JSP523.Rank4
