import JSP523.Rank4.GraphActualAlgebra
import JSP523.Rank4.GraphReciprocalAccounting

/-!
# Selected pair-link occurrences at a four-edge

The edgewise part of (III.B.9) is inclusion and exclusion on the two
eligible slots offered by each pair of nonprivate opposite facets.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem pair_occurrence_inclusion_exclusion
    {β : Type*} [DecidableEq β]
    (R : Finset β) (A B : Finset β → Prop)
    [DecidablePred A] [DecidablePred B] :
    ((R.powersetCard 2).filter fun P => ¬ A P ∧ ¬ B P).card +
      (∑ P ∈ R.powersetCard 2,
        ((if A P then 1 else 0) + (if B P then 1 else 0))) =
      R.card.choose 2 +
        ((R.powersetCard 2).filter fun P => A P ∧ B P).card := by
  classical
  let F := R.powersetCard 2
  have hPoint (P : Finset β) :
      (if ¬ A P ∧ ¬ B P then 1 else 0) +
        ((if A P then 1 else 0) + (if B P then 1 else 0)) =
      1 + (if A P ∧ B P then 1 else 0) := by
    by_cases hA : A P <;> by_cases hB : B P <;> simp [hA, hB]
  have hSum :
      (∑ P ∈ F,
        ((if ¬ A P ∧ ¬ B P then 1 else 0) +
          ((if A P then 1 else 0) + (if B P then 1 else 0)))) =
        ∑ P ∈ F, (1 + (if A P ∧ B P then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro P _
    exact hPoint P
  simpa only [F, Finset.sum_add_distrib,
    ← Finset.card_filter, Finset.sum_const_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_powersetCard, Nat.cast_id] using hSum

/-- Nonprivate opposite facets of an actual four-edge, indexed by the
vertex missing from each facet. -/
def actualEdgeNonprivateRows
    (D : FiniteCompletionCliqueData α) (E : Edge α) : Finset α :=
  E.filter fun a =>
    2 ≤ (graphFacetCompletions D.K D.ground (E.erase a)).card

/-- The base pair of a two-row occurrence is the complementary pair in
the four-edge. -/
def actualEdgePairBase (E P : Edge α) : Edge α := E \ P

/-- Failure of the first selected slot for a pair of nonprivate rows. -/
noncomputable def actualEdgeFirstSlotExcluded
    (D : FiniteCompletionCliqueData α) (E P : Edge α) : Prop :=
  if hP : P.card = 2 then
    (pairRootRep P hP).1 ∉
      actualEligiblePairSlotVertices D (actualEdgePairBase E P)
  else False

/-- Failure of the second selected slot for a pair of nonprivate rows. -/
noncomputable def actualEdgeSecondSlotExcluded
    (D : FiniteCompletionCliqueData α) (E P : Edge α) : Prop :=
  if hP : P.card = 2 then
    (pairRootRep P hP).2 ∉
      actualEligiblePairSlotVertices D (actualEdgePairBase E P)
  else False

/-- Retained pair-link occurrences contributed by an actual edge. -/
noncomputable def actualEdgeSelectedOccurrences
    (D : FiniteCompletionCliqueData α) (E : Edge α) : Family α := by
  classical
  exact (actualEdgeNonprivateRows D E).powersetCard 2 |>.filter fun P =>
    ¬ actualEdgeFirstSlotExcluded D E P ∧
      ¬ actualEdgeSecondSlotExcluded D E P

/-- Number of excluded directed row slots, with reciprocal exclusions
counted twice. -/
noncomputable def actualEdgeExcludedSlots
    (D : FiniteCompletionCliqueData α) (E : Edge α) : ℕ := by
  classical
  exact ∑ P ∈ (actualEdgeNonprivateRows D E).powersetCard 2,
    ((if actualEdgeFirstSlotExcluded D E P then 1 else 0) +
      (if actualEdgeSecondSlotExcluded D E P then 1 else 0))

/-- Pairs whose two selected slots are both excluded. -/
noncomputable def actualEdgeReciprocalExclusions
    (D : FiniteCompletionCliqueData α) (E : Edge α) : Family α := by
  classical
  exact (actualEdgeNonprivateRows D E).powersetCard 2 |>.filter fun P =>
    actualEdgeFirstSlotExcluded D E P ∧
      actualEdgeSecondSlotExcluded D E P

omit [Fintype α] in
/-- The exact local occurrence identity before interpreting exclusions
as monochromatic arrows and reciprocal pairs. -/
theorem actual_edge_selected_occurrence_identity
    (D : FiniteCompletionCliqueData α) (E : Edge α) :
    (actualEdgeSelectedOccurrences D E).card +
      actualEdgeExcludedSlots D E =
      (actualEdgeNonprivateRows D E).card.choose 2 +
        (actualEdgeReciprocalExclusions D E).card := by
  classical
  exact pair_occurrence_inclusion_exclusion
    (actualEdgeNonprivateRows D E)
    (actualEdgeFirstSlotExcluded D E)
    (actualEdgeSecondSlotExcluded D E)

omit [Fintype α] in
/-- A pair of opposite rows in a four-edge determines a complementary
base pair and the original four-edge is its pair-link edge. -/
theorem actual_edge_pair_base_geometry
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K)
    (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let a := (pairRootRep P (Finset.mem_powersetCard.mp hP).2).1
    let b := (pairRootRep P (Finset.mem_powersetCard.mp hP).2).2
    let Q := actualEdgePairBase E P
    Q ∈ D.ground.powersetCard 2 ∧
      (completionPairLinkGraph D Q).Adj a b := by
  classical
  have hPparts := Finset.mem_powersetCard.mp hP
  have hPsubE : P ⊆ E :=
    hPparts.1.trans (Finset.filter_subset _ _)
  let a := (pairRootRep P hPparts.2).1
  let b := (pairRootRep P hPparts.2).2
  let Q := actualEdgePairBase E P
  have hab : a ≠ b := (pair_root_rep_spec P hPparts.2).1
  have hPair : P = ({a, b} : Edge α) :=
    (pair_root_rep_spec P hPparts.2).2
  have hQcard : Q.card = 2 := by
    dsimp [Q, actualEdgePairBase]
    rw [Finset.card_sdiff_of_subset hPsubE,
      D.uniform_four hE, hPparts.2]
  have hQsub : Q ⊆ D.ground := by
    intro x hx
    exact hGround ((Finset.mem_sdiff.mp hx).1)
  have hQmem : Q ∈ D.ground.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hQsub, hQcard⟩
  have haE : a ∈ E := hPsubE (hPair ▸ (by simp : a ∈ ({a, b} : Edge α)))
  have hbE : b ∈ E := hPsubE (hPair ▸ (by simp : b ∈ ({a, b} : Edge α)))
  have haQ : a ∉ Q := by
    intro hx
    exact (Finset.mem_sdiff.mp hx).2
      (hPair ▸ (by simp : a ∈ ({a, b} : Edge α)))
  have hbQ : b ∉ Q := by
    intro hx
    exact (Finset.mem_sdiff.mp hx).2
      (hPair ▸ (by simp : b ∈ ({a, b} : Edge α)))
  have hDecomp : E = insert a (insert b Q) := by
    have hUnion : P ∪ Q = E := by
      simpa [Q, actualEdgePairBase] using
        (Finset.union_sdiff_of_subset hPsubE)
    rw [← hUnion, hPair]
    ext x
    simp [Finset.mem_insert, or_comm, or_left_comm]
  refine ⟨hQmem, ?_⟩
  change a ∉ Q ∧ b ∉ Q ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b Q) ∈ D.K
  exact ⟨haQ, hbQ, hGround haE, hGround hbE, hab, hDecomp ▸ hE⟩

omit [Fintype α] in
/-- A local retained occurrence is exactly adjacency of the complementary
pair in the actual selected pair link. -/
theorem actual_edge_pair_selected_iff
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    let Q := actualEdgePairBase E P
    (selectedCompletionPairGraph D
      (actualEligiblePairSlotVertices D Q) Q).Adj a b ↔
      ¬ actualEdgeFirstSlotExcluded D E P ∧
        ¬ actualEdgeSecondSlotExcluded D E P := by
  classical
  have hPcard := (Finset.mem_powersetCard.mp hP).2
  let a := (pairRootRep P hPcard).1
  let b := (pairRootRep P hPcard).2
  let Q := actualEdgePairBase E P
  have hRaw := (actual_edge_pair_base_geometry D E P hE hGround hP).2
  change (completionPairLinkGraph D Q).Adj a b at hRaw
  change (completionPairLinkGraph D Q).Adj a b ∧
      a ∈ actualEligiblePairSlotVertices D Q ∧
      b ∈ actualEligiblePairSlotVertices D Q ↔
    ¬ actualEdgeFirstSlotExcluded D E P ∧
      ¬ actualEdgeSecondSlotExcluded D E P
  simp only [actualEdgeFirstSlotExcluded,
    actualEdgeSecondSlotExcluded, dite_eq_left hPcard,
    not_not]
  simpa only [a, b, Q] using
    (and_iff_right hRaw :
      ((completionPairLinkGraph D Q).Adj a b ∧
        a ∈ actualEligiblePairSlotVertices D Q ∧
        b ∈ actualEligiblePairSlotVertices D Q) ↔
        a ∈ actualEligiblePairSlotVertices D Q ∧
          b ∈ actualEligiblePairSlotVertices D Q)

omit [Fintype α] in
/-- The two slots of a pair of rows are precisely the opposite facets
of those rows in the four-edge. -/
theorem actual_edge_pair_opposite_facets
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    let Q := actualEdgePairBase E P
    insert a Q = E.erase b ∧ insert b Q = E.erase a := by
  classical
  have hPparts := Finset.mem_powersetCard.mp hP
  let a := (pairRootRep P hPparts.2).1
  let b := (pairRootRep P hPparts.2).2
  let Q := actualEdgePairBase E P
  have hab : a ≠ b := (pair_root_rep_spec P hPparts.2).1
  have hPair : P = ({a, b} : Edge α) :=
    (pair_root_rep_spec P hPparts.2).2
  have hPsubE : P ⊆ E :=
    hPparts.1.trans (Finset.filter_subset _ _)
  have haE : a ∈ E :=
    hPsubE (hPair ▸ (by simp : a ∈ ({a, b} : Edge α)))
  have hbE : b ∈ E :=
    hPsubE (hPair ▸ (by simp : b ∈ ({a, b} : Edge α)))
  have hQ : Q = E \ ({a, b} : Edge α) := by
    simp only [Q, actualEdgePairBase, hPair]
  change insert a Q = E.erase b ∧ insert b Q = E.erase a
  constructor
  · ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp [hQ, hxa, hxb, haE, hbE, hab, hab.symm]
  · ext x
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
      simp [hQ, hxa, hxb, haE, hbE, hab, hab.symm]

omit [Fintype α] in
/-- A nonprivate facet is excluded from a base pair exactly when all its
completion-pair labels equal the lone facet vertex outside that base pair. -/
theorem facet_slot_excluded_iff_external_monochromatic
    (C : Finset α) (label : α → α → α)
    (Q : Edge α) (x : α)
    (hCard : 2 ≤ C.card)
    (hSymm : ∀ u v, label u v = label v u)
    (hLabels : ∀ u ∈ C, ∀ v ∈ C,
      u ≠ v → label u v ∈ insert x Q)
    (hxQ : x ∉ Q) :
    ¬ FacetEligibleAtPair C label Q ↔
      ∀ u ∈ C, ∀ v ∈ C, u ≠ v → label u v = x := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hCard
  constructor
  · intro hExcluded
    have hNoDiv : ¬ FacetHasDivergentLabels C label := by
      intro hDiv
      exact hExcluded ⟨hCard, Or.inl hDiv⟩
    have hMono := facet_pair_labels_constant_of_no_divergence
      C label hSymm hNoDiv u v hu hv huv
    have hz := hLabels u hu v hv huv
    rcases Finset.mem_insert.mp hz with hzX | hzQ
    · intro a ha b hb hab
      exact (hMono a ha b hb hab).trans hzX
    · exact False.elim (hExcluded
        ⟨hCard, Or.inr ⟨label u v, hzQ, hMono⟩⟩)
  · intro hMono hEligible
    rcases hEligible.2 with hDiv | ⟨z, hzQ, hConst⟩
    · obtain ⟨a, ha, b, hb, c, hc,
        hab, hac, _hbc, hDiff⟩ := hDiv
      exact hDiff ((hMono a ha b hb hab).trans
        (hMono a ha c hc hac).symm)
    · have hxz : x = z :=
        (hMono u hu v hv huv).symm.trans (hConst u hu v hv huv)
      exact hxQ (hxz ▸ hzQ)

omit [Fintype α] in
/-- The slot-to-arrow equivalence with explicitly oriented opposite rows.
It is used for the second slot and for reciprocal recognition. -/
theorem actual_edge_slot_excluded_iff_mono_arrow
    (D : FiniteCompletionCliqueData α) (E : Edge α) (x y : α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hxRow : x ∈ actualEdgeNonprivateRows D E)
    (hyRow : y ∈ actualEdgeNonprivateRows D E)
    (hxy : x ≠ y) :
    let Q : Edge α := E \ {x, y}
    x ∉ actualEligiblePairSlotVertices D Q ↔
      ∀ u ∈ graphFacetCompletions D.K D.ground (E.erase y),
        ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase y),
          u ≠ v → D.label u v = x := by
  classical
  let Q : Edge α := E \ {x, y}
  have hxE : x ∈ E := (Finset.mem_filter.mp hxRow).1
  have hyE : y ∈ E := (Finset.mem_filter.mp hyRow).1
  have hxGround : x ∈ D.ground := hGround hxE
  have hxQ : x ∉ Q := by
    intro hx
    exact (Finset.mem_sdiff.mp hx).2 (by simp)
  have hCard : 2 ≤
      (graphFacetCompletions D.K D.ground (E.erase y)).card :=
    (Finset.mem_filter.mp hyRow).2
  have hTcard : (E.erase y).card = 3 := by
    rw [Finset.card_erase_of_mem hyE, D.uniform_four hE]
  have hTsub : E.erase y ⊆ D.ground := by
    intro z hz
    exact hGround (Finset.mem_erase.mp hz).2
  have hFacet : insert x Q = E.erase y := by
    ext z
    by_cases hzx : z = x <;> by_cases hzy : z = y <;>
      simp [Q, hzx, hzy, hxE, hyE, hxy, hxy.symm]
  have hLabels : ∀ u ∈ graphFacetCompletions D.K D.ground (E.erase y),
      ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase y),
        u ≠ v → D.label u v ∈ insert x Q := by
    intro u hu v hv huv
    rw [hFacet]
    exact completion_pair_label_mem_facet D (E.erase y)
      hTcard hTsub u v hu hv huv
  have hSlot : x ∉ actualEligiblePairSlotVertices D Q ↔
      ¬ FacetEligibleAtPair
        (graphFacetCompletions D.K D.ground (E.erase y)) D.label Q := by
    rw [← hFacet]
    simp [actualEligiblePairSlotVertices, hxGround, hxQ]
  exact hSlot.trans
    (facet_slot_excluded_iff_external_monochromatic
      (graphFacetCompletions D.K D.ground (E.erase y))
      D.label Q x hCard D.label_symm hLabels hxQ)

omit [Fintype α] in
/-- The first failed slot is the monochromatic arrow from the second
opposite facet toward the first row. -/
theorem actual_edge_first_slot_excluded_iff_mono_arrow
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    actualEdgeFirstSlotExcluded D E P ↔
      ∀ u ∈ graphFacetCompletions D.K D.ground (E.erase b),
        ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase b),
          u ≠ v → D.label u v = a := by
  classical
  have hPparts := Finset.mem_powersetCard.mp hP
  let a := (pairRootRep P hPparts.2).1
  let b := (pairRootRep P hPparts.2).2
  have hPair : P = ({a, b} : Edge α) :=
    (pair_root_rep_spec P hPparts.2).2
  have haRow : a ∈ actualEdgeNonprivateRows D E :=
    hPparts.1 (hPair ▸ (by simp : a ∈ ({a, b} : Edge α)))
  have hbRow : b ∈ actualEdgeNonprivateRows D E :=
    hPparts.1 (hPair ▸ (by simp : b ∈ ({a, b} : Edge α)))
  have hab := (pair_root_rep_spec P hPparts.2).1
  have hGeneric := actual_edge_slot_excluded_iff_mono_arrow
    D E a b hE hGround haRow hbRow hab
  change a ∉ actualEligiblePairSlotVertices D (E \ {a, b}) ↔
    (∀ u ∈ graphFacetCompletions D.K D.ground (E.erase b),
      ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase b),
        u ≠ v → D.label u v = a) at hGeneric
  simp only [actualEdgeFirstSlotExcluded, dite_eq_left hPparts.2]
  change a ∉ actualEligiblePairSlotVertices D (actualEdgePairBase E P) ↔
    (∀ u ∈ graphFacetCompletions D.K D.ground (E.erase b),
      ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase b),
        u ≠ v → D.label u v = a)
  rw [actualEdgePairBase, hPair]
  exact hGeneric

omit [Fintype α] in
/-- The second failed slot is the monochromatic arrow from the first
opposite facet toward the second row. -/
theorem actual_edge_second_slot_excluded_iff_mono_arrow
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    actualEdgeSecondSlotExcluded D E P ↔
      ∀ u ∈ graphFacetCompletions D.K D.ground (E.erase a),
        ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase a),
          u ≠ v → D.label u v = b := by
  classical
  have hPparts := Finset.mem_powersetCard.mp hP
  let a := (pairRootRep P hPparts.2).1
  let b := (pairRootRep P hPparts.2).2
  have hPair : P = ({a, b} : Edge α) :=
    (pair_root_rep_spec P hPparts.2).2
  have haRow : a ∈ actualEdgeNonprivateRows D E :=
    hPparts.1 (hPair ▸ (by simp : a ∈ ({a, b} : Edge α)))
  have hbRow : b ∈ actualEdgeNonprivateRows D E :=
    hPparts.1 (hPair ▸ (by simp : b ∈ ({a, b} : Edge α)))
  have hba := (pair_root_rep_spec P hPparts.2).1.symm
  have hGeneric := actual_edge_slot_excluded_iff_mono_arrow
    D E b a hE hGround hbRow haRow hba
  change b ∉ actualEligiblePairSlotVertices D (E \ {b, a}) ↔
    (∀ u ∈ graphFacetCompletions D.K D.ground (E.erase a),
      ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase a),
        u ≠ v → D.label u v = b) at hGeneric
  simp only [actualEdgeSecondSlotExcluded, dite_eq_left hPparts.2]
  change b ∉ actualEligiblePairSlotVertices D (actualEdgePairBase E P) ↔
    (∀ u ∈ graphFacetCompletions D.K D.ground (E.erase a),
      ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase a),
        u ≠ v → D.label u v = b)
  rw [actualEdgePairBase, hPair, Finset.pair_comm]
  exact hGeneric

/-- A nonprivate opposite facet carries a monochromatic arrow from its
missing vertex to the common label of its completion pairs. -/
def actualEdgeMonochromaticArrow
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (source target : α) : Prop :=
  ∀ u ∈ graphFacetCompletions D.K D.ground (E.erase source),
    ∀ v ∈ graphFacetCompletions D.K D.ground (E.erase source),
      u ≠ v → D.label u v = target

omit [Fintype α] in
theorem actual_edge_first_exclusion_iff_monochromatic_arrow
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    actualEdgeFirstSlotExcluded D E P ↔
      actualEdgeMonochromaticArrow D E b a :=
  actual_edge_first_slot_excluded_iff_mono_arrow D E P hE hGround hP

omit [Fintype α] in
theorem actual_edge_second_exclusion_iff_monochromatic_arrow
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    actualEdgeSecondSlotExcluded D E P ↔
      actualEdgeMonochromaticArrow D E a b :=
  actual_edge_second_slot_excluded_iff_mono_arrow D E P hE hGround hP

/-- Number of monochromatic arrows between nonprivate opposite rows,
counting both directions of a reciprocal pair. -/
noncomputable def actualEdgeMonochromaticArrowCount
    (D : FiniteCompletionCliqueData α) (E : Edge α) : ℕ := by
  classical
  exact ∑ P ∈ (actualEdgeNonprivateRows D E).powersetCard 2,
    (if hP : P.card = 2 then
      let ab := pairRootRep P hP
      (if actualEdgeMonochromaticArrow D E ab.2 ab.1 then 1 else 0) +
        (if actualEdgeMonochromaticArrow D E ab.1 ab.2 then 1 else 0)
    else 0)

omit [Fintype α] in
/-- The excluded-slot count is exactly the count of monochromatic
arrows whose two endpoint rows are nonprivate. -/
theorem actual_edge_excluded_slots_eq_monochromatic_arrow_sum
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground) :
    actualEdgeExcludedSlots D E =
      actualEdgeMonochromaticArrowCount D E := by
  classical
  unfold actualEdgeExcludedSlots actualEdgeMonochromaticArrowCount
  apply Finset.sum_congr rfl
  intro P hP
  have hPcard := (Finset.mem_powersetCard.mp hP).2
  simp only [dite_eq_left hPcard]
  rw [if_congr (actual_edge_first_exclusion_iff_monochromatic_arrow
      D E P hE hGround hP) (by rfl) (by rfl),
    if_congr (actual_edge_second_exclusion_iff_monochromatic_arrow
      D E P hE hGround hP) (by rfl) (by rfl)]

omit [Fintype α] in
/-- Both local exclusions occur exactly at a mutually directed pair of
monochromatic nonprivate rows. -/
theorem actual_edge_reciprocal_exclusion_iff_mono_arrows
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2) :
    let hPcard := (Finset.mem_powersetCard.mp hP).2
    let a := (pairRootRep P hPcard).1
    let b := (pairRootRep P hPcard).2
    P ∈ actualEdgeReciprocalExclusions D E ↔
      actualEdgeMonochromaticArrow D E a b ∧
        actualEdgeMonochromaticArrow D E b a := by
  classical
  simp only [actualEdgeReciprocalExclusions, Finset.mem_filter, hP,
    true_and]
  exact and_congr
    (actual_edge_first_exclusion_iff_monochromatic_arrow
      D E P hE hGround hP)
    (actual_edge_second_exclusion_iff_monochromatic_arrow
      D E P hE hGround hP) |>.trans (and_comm)

omit [Fintype α] in
/-- A monochromatic arrow at a nonprivate opposite facet has an actual
second completion witnessing the arrow relation. -/
theorem actual_edge_monochromatic_arrow_implies_reciprocal_arrow
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (source target : α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hSource : source ∈ actualEdgeNonprivateRows D E)
    (hTarget : target ∈ E) (hNe : source ≠ target)
    (hMono : actualEdgeMonochromaticArrow D E source target) :
    actualReciprocalArrow D E source target := by
  classical
  let C := graphFacetCompletions D.K D.ground (E.erase source)
  have hSourceE : source ∈ E := (Finset.mem_filter.mp hSource).1
  have hCard : 2 ≤ C.card := (Finset.mem_filter.mp hSource).2
  have hSourceC : source ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨hGround hSourceE, ?_⟩
    simpa [Finset.insert_erase hSourceE] using hE
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hCard
  have hOther : ∃ x ∈ C, x ≠ source := by
    by_cases hus : u = source
    · refine ⟨v, hv, ?_⟩
      intro hvs
      exact huv (hus.trans hvs.symm)
    · exact ⟨u, hu, hus⟩
  obtain ⟨x, hx, hxs⟩ := hOther
  refine ⟨hSourceE, hTarget, hNe, x, hx, hxs, ?_⟩
  exact hMono source hSourceC x hx hxs.symm

omit [Fintype α] in
/-- At completion degree two, an actual arrow determines the entire
monochromatic facet label. -/
theorem actual_reciprocal_arrow_degree_two_implies_monochromatic
    (D : FiniteCompletionCliqueData α) (E : Edge α)
    (source target : α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hArrow : actualReciprocalArrow D E source target)
    (hDegree :
      (graphFacetCompletions D.K D.ground (E.erase source)).card = 2) :
    actualEdgeMonochromaticArrow D E source target := by
  classical
  let C := graphFacetCompletions D.K D.ground (E.erase source)
  change C.card = 2 at hDegree
  obtain ⟨hSourceE, _hTargetE, _hNe, x, hx, hxs, hLabel⟩ := hArrow
  have hSourceC : source ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨hGround hSourceE, ?_⟩
    simpa [Finset.insert_erase hSourceE] using hE
  have hNoDiv : ¬ FacetHasDivergentLabels C D.label := by
    rintro ⟨u, hu, v, hv, w, hw, huv, huw, hvw, _⟩
    have hThree : ({u, v, w} : Finset α).card = 3 := by
      simp [huv, huw, hvw]
    have hSub : ({u, v, w} : Finset α) ⊆ C := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hu
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hv
      exact Finset.mem_singleton.mp hz ▸ hw
    have hBound := Finset.card_le_card hSub
    omega
  have hConst := facet_pair_labels_constant_of_no_divergence
    C D.label D.label_symm hNoDiv source x hSourceC hx hxs.symm
  intro u hu v hv huv
  exact (hConst u hu v hv huv).trans hLabel

omit [Fintype α] in
/-- A pair excluded at both selected slots is an actual reciprocal pair
in the containing four-edge. -/
theorem actual_edge_reciprocal_exclusion_implies_actual_reciprocal
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ actualEdgeReciprocalExclusions D E) :
    (E, P) ∈ actualReciprocalUnorderedOccurrences D := by
  classical
  have hProws : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2 :=
    (Finset.mem_filter.mp hP).1
  have hPparts := Finset.mem_powersetCard.mp hProws
  let a := (pairRootRep P hPparts.2).1
  let b := (pairRootRep P hPparts.2).2
  have hPair : P = ({a, b} : Edge α) :=
    (pair_root_rep_spec P hPparts.2).2
  have hab : a ≠ b := (pair_root_rep_spec P hPparts.2).1
  have haRow : a ∈ actualEdgeNonprivateRows D E :=
    hPparts.1 (hPair ▸ (by simp : a ∈ ({a, b} : Edge α)))
  have hbRow : b ∈ actualEdgeNonprivateRows D E :=
    hPparts.1 (hPair ▸ (by simp : b ∈ ({a, b} : Edge α)))
  have haE : a ∈ E := (Finset.mem_filter.mp haRow).1
  have hbE : b ∈ E := (Finset.mem_filter.mp hbRow).1
  have hMono := (actual_edge_reciprocal_exclusion_iff_mono_arrows
    D E P hE hGround hProws).1 hP
  have hAB := actual_edge_monochromatic_arrow_implies_reciprocal_arrow
    D E a b hE hGround haRow hbE hab hMono.1
  have hBA := actual_edge_monochromatic_arrow_implies_reciprocal_arrow
    D E b a hE hGround hbRow haE hab.symm hMono.2
  have hDir : (E, (a, b)) ∈ actualReciprocalDirectedOccurrences D := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨hE, Finset.mem_product.mpr
        ⟨hGround haE, hGround hbE⟩⟩, hAB, hBA⟩
  apply Finset.mem_image.mpr
  refine ⟨(E, (a, b)), hDir, ?_⟩
  simp [actualReciprocalUnorderedKey, hPair]

omit [Fintype α] in
/-- Once reciprocal opposite facets have degree two, every actual
reciprocal pair is a double slot exclusion. -/
theorem actual_reciprocal_implies_edge_reciprocal_exclusion
    (D : FiniteCompletionCliqueData α) (E P : Edge α)
    (hE : E ∈ D.K) (hGround : E ⊆ D.ground)
    (hP : P ∈ (actualEdgeNonprivateRows D E).powersetCard 2)
    (hDegree : ∀ p ∈ actualReciprocalDirectedOccurrences D,
      (graphFacetCompletions D.K D.ground
        (p.1.erase p.2.1)).card = 2)
    (hReciprocal : (E, P) ∈ actualReciprocalUnorderedOccurrences D) :
    P ∈ actualEdgeReciprocalExclusions D E := by
  classical
  have hPparts := Finset.mem_powersetCard.mp hP
  let a := (pairRootRep P hPparts.2).1
  let b := (pairRootRep P hPparts.2).2
  have hPair : P = ({a, b} : Edge α) :=
    (pair_root_rep_spec P hPparts.2).2
  have hab : a ≠ b := (pair_root_rep_spec P hPparts.2).1
  obtain ⟨p, hp, hpEq⟩ := Finset.mem_image.mp hReciprocal
  change (p.1, ({p.2.1, p.2.2} : Edge α)) = (E, P) at hpEq
  have hpEdge : p.1 = E := congrArg Prod.fst hpEq
  have hpPair : ({p.2.1, p.2.2} : Edge α) = P :=
    congrArg Prod.snd hpEq
  have hParts := (Finset.mem_filter.mp hp).2
  have hpSwap := actual_reciprocal_swap_mem D p hp
  have hDegreeP := hDegree p hp
  have hDegreeSwap := hDegree (actualReciprocalSwap p) hpSwap
  have hOrient := pair_finset_eq_oriented_eq hab (hpPair.trans hPair)
  have hData :
      actualReciprocalArrow D E a b ∧
        actualReciprocalArrow D E b a ∧
        (graphFacetCompletions D.K D.ground (E.erase a)).card = 2 ∧
        (graphFacetCompletions D.K D.ground (E.erase b)).card = 2 := by
    rcases hOrient with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hpEdge, hpa, hpb] using hParts.1
      · simpa [hpEdge, hpa, hpb] using hParts.2
      · simpa [hpEdge, hpa] using hDegreeP
      · simpa [actualReciprocalSwap, hpEdge, hpb] using hDegreeSwap
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hpEdge, hpa, hpb] using hParts.2
      · simpa [hpEdge, hpa, hpb] using hParts.1
      · simpa [actualReciprocalSwap, hpEdge, hpb] using hDegreeSwap
      · simpa [hpEdge, hpa] using hDegreeP
  apply (actual_edge_reciprocal_exclusion_iff_mono_arrows
    D E P hE hGround hP).2
  exact ⟨actual_reciprocal_arrow_degree_two_implies_monochromatic
      D E a b hE hGround hData.1 hData.2.2.1,
    actual_reciprocal_arrow_degree_two_implies_monochromatic
      D E b a hE hGround hData.2.1 hData.2.2.2⟩

end JSP523.Rank4
