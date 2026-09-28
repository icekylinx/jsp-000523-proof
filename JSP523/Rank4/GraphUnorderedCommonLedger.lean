import JSP523.Rank4.GraphActualExcessGlobal

/-!
# Unordered common-neighbor multiplicity and degree pairs

The manuscript's `W` is a sum of binomial degree terms. Counting the
same length-two wedges by their unordered endpoint pair identifies
`W` with total common-neighbor multiplicity over two-element finsets.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Common-neighbor multiplicity for an unordered two-element finset.
The value is zero for other finsets. -/
noncomputable def graphCommonMultiplicityAtPair
    (F : SimpleGraph α) [DecidableRel F.Adj] (P : Edge α) : ℕ :=
  if hP : P.card = 2 then
    let ab := pairRootRep P hP
    graphCommonMultiplicity F ab.1 ab.2
  else 0

/-- A common neighbor of a pair is precisely a vertex whose
neighborhood contains that pair. -/
theorem graph_common_multiplicity_at_pair_eq_support_card
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (P : Edge α) (hP : P.card = 2) :
    graphCommonMultiplicityAtPair F P =
      (Finset.univ.filter fun x => P ⊆ F.neighborFinset x).card := by
  classical
  let ab := pairRootRep P hP
  have hSpec := pairRootRep_spec P hP
  unfold graphCommonMultiplicityAtPair
  rw [dite_eq_left hP]
  change graphCommonMultiplicity F ab.1 ab.2 = _
  rw [graphCommonMultiplicity_eq_inter]
  congr 1
  ext x
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hSpec.2]
  constructor
  · rintro ⟨hax, hbx⟩ y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [SimpleGraph.mem_neighborFinset] using hax.symm
    · simpa only [SimpleGraph.mem_neighborFinset] using
        ((Finset.mem_singleton.mp hy) ▸ hbx.symm)
  · intro h
    constructor
    · have hxa : F.Adj x ab.1 := by
        simpa only [SimpleGraph.mem_neighborFinset] using
          h (Finset.mem_insert_self _ _)
      exact hxa.symm
    · have hxb : F.Adj x ab.2 := by
        simpa only [SimpleGraph.mem_neighborFinset] using h (by simp [ab])
      exact hxb.symm

/-- Exact unordered wedge count: summing multiplicity over all
two-element vertex pairs gives the degree-binomial sum. -/
theorem graph_unordered_common_multiplicity_eq_degree_pairs
    (F : SimpleGraph α) [DecidableRel F.Adj] :
    (∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
      graphCommonMultiplicityAtPair F P) =
      ∑ x : α, (F.degree x).choose 2 := by
  classical
  have hAt (P : Edge α)
      (hP : P ∈ (Finset.univ : Finset α).powersetCard 2) :
      graphCommonMultiplicityAtPair F P =
        (Finset.univ.filter fun x => P ⊆ F.neighborFinset x).card :=
    graph_common_multiplicity_at_pair_eq_support_card F P
      (Finset.mem_powersetCard.mp hP).2
  calc
    (∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
      graphCommonMultiplicityAtPair F P) =
        ∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
          (Finset.univ.filter fun x => P ⊆ F.neighborFinset x).card := by
            apply Finset.sum_congr rfl
            intro P hP
            exact hAt P hP
    _ = ∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
          ∑ x : α, if P ⊆ F.neighborFinset x then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro P _
            exact Finset.card_filter _ _
    _ = ∑ x : α, ∑ P ∈ (Finset.univ : Finset α).powersetCard 2,
          if P ⊆ F.neighborFinset x then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ x : α, (F.degree x).choose 2 := by
          apply Finset.sum_congr rfl
          intro x _
          have hFilter : ((Finset.univ : Finset α).powersetCard 2).filter
              (fun P => P ⊆ F.neighborFinset x) =
              (F.neighborFinset x).powersetCard 2 := by
            ext P
            constructor
            · intro h
              have h' := Finset.mem_filter.mp h
              have hcard := (Finset.mem_powersetCard.mp h'.1).2
              exact Finset.mem_powersetCard.mpr ⟨h'.2, hcard⟩
            · intro h
              have h' := Finset.mem_powersetCard.mp h
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_powersetCard.mpr
                  ⟨Finset.subset_univ _, h'.2⟩, h'.1⟩
          rw [← Finset.card_filter, hFilter, Finset.card_powersetCard]
          rfl

end JSP523.Rank4
