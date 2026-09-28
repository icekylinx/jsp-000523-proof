import JSP523.Rank5.OverlapPartnerBudget
import JSP523.Rank5.RepeatedCenterActual

/-!
# Rank-five facet inheritance witnesses

This file records the finite witness family in the facet case of IV.9.3.
The lower count is stated using the two retained-degree guarantees needed in
the manuscript.  Its upper count requires a separate pinned-center reindexing
argument; the witness set below keeps every root and label visible for that
step.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- A bad facet incidence records its parent, shared four-face and deleted
    vertex. -/
noncomputable def facetBadIncidences
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α) :
    Finset ((Edge α × Edge α) × α) := by
  classical
  exact ((K ×ˢ V.powersetCard 4) ×ˢ V).filter fun i =>
    i.1.2 ⊆ i.1.1 ∧ i.1.2 ∈ sharedFourShadow K ∧
      i.2 ∈ i.1.2 ∧ i.2 ≠ facetCenter i.1.2 ∧
        tripleLabel (i.1.2.erase i.2) ≠ facetCenter i.1.2

/-- The triple core and the first completion root reconstructed from a bad
    incidence. -/
def facetWitnessCore (i : (Edge α × Edge α) × α) : Edge α :=
  i.1.2.erase i.2

def facetWitnessRoot (i : (Edge α × Edge α) × α) : Edge α :=
  i.1.1 \ facetWitnessCore i

/-- Retained second roots meeting the first completion root exactly at the
    deleted vertex. -/
noncomputable def facetWitnessSecondRoots
    (K : Family α) (V : Edge α) (i : (Edge α × Edge α) × α) :
    Family α := by
  classical
  exact (parentPairLink K V (facetWitnessCore i)).filter fun R₁ =>
    facetWitnessRoot i ∩ R₁ = {i.2}

/-- Third roots forming actual strong pairs with both first roots, with the
    same lower-core label.  The two strong-pair conditions are those needed
    to invoke the pinned bound (IV.7.2) in the upper count. -/
noncomputable def facetWitnessThirdRoots
    (H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) (R₁ : Edge α) : Family α := by
  classical
  let B := facetWitnessCore i
  let R₀ := facetWitnessRoot i
  exact (parentPairLink H V B).filter fun T =>
    Disjoint T (R₀ ∪ R₁) ∧
      ActualStrongPartner H V R₀ T 2 3 t (tripleLabel B) ∧
      ActualStrongPartner H V R₁ T 2 3 t (tripleLabel B)

/-- All concrete `(second root, third root)` witnesses of one bad incidence. -/
noncomputable def facetWitnessesFor
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) :
    Finset ((_R₁ : Edge α) × Edge α) := by
  classical
  exact (facetWitnessSecondRoots K V i).sigma
    (facetWitnessThirdRoots H V t tripleLabel i)

/-- The full retained bad-incidence/witness relation. -/
noncomputable def facetInheritanceWitnesses
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α) :
    Finset ((_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) := by
  classical
  exact I.sigma (facetWitnessesFor K H V t tripleLabel)

/-- Reindex a witness by the data retained in the pinned count: lower core,
    both first roots, third root and the common vertex. -/
def facetWitnessTuple
    (w : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) :
    ((Edge α × Edge α) × (Edge α × Edge α)) × α :=
  (((facetWitnessCore w.1, facetWitnessRoot w.1),
    (w.2.1, w.2.2)), w.1.2)

/-- The pinned tuple determines the bad incidence: recover
    `A = B ∪ {a}` and `E = B ∪ R₀`.  Thus witness reindexing introduces no
    multiplicity before the pinned upper count. -/
theorem facet_witness_tuple_injective
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel) :
    Set.InjOn facetWitnessTuple
      (facetInheritanceWitnesses I K H V t tripleLabel :
        Set ((_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))) := by
  classical
  intro w hw w' hw' hTuple
  have hBad (x : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))
      (hx : x ∈ facetInheritanceWitnesses I K H V t tripleLabel) :
      x.1.1.2 ⊆ x.1.1.1 ∧ x.1.2 ∈ x.1.1.2 := by
    have hxI : x.1 ∈ I := (Finset.mem_sigma.mp hx).1
    have hxBad := hI hxI
    change x.1 ∈ ((K ×ˢ V.powersetCard 4) ×ˢ V).filter _ at hxBad
    have hParts := (Finset.mem_filter.mp hxBad).2
    exact ⟨hParts.1, hParts.2.2.1⟩
  have hRecon (x : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))
      (hx : x ∈ facetInheritanceWitnesses I K H V t tripleLabel) :
      x.1.1.1 = facetWitnessCore x.1 ∪ facetWitnessRoot x.1 ∧
      x.1.1.2 = facetWitnessCore x.1 ∪ {x.1.2} := by
    obtain ⟨hAE, haA⟩ := hBad x hx
    have hBE : facetWitnessCore x.1 ⊆ x.1.1.1 :=
      (Finset.erase_subset x.1.2 x.1.1.2).trans hAE
    constructor
    · simpa [facetWitnessRoot, Finset.union_comm] using
        (Finset.sdiff_union_of_subset hBE).symm
    · simp [facetWitnessCore, Finset.union_singleton,
        Finset.insert_erase haA]
  have hB : facetWitnessCore w.1 = facetWitnessCore w'.1 :=
    congrArg (fun q => q.1.1.1) hTuple
  have hR : facetWitnessRoot w.1 = facetWitnessRoot w'.1 :=
    congrArg (fun q => q.1.1.2) hTuple
  have hR₁ : w.2.1 = w'.2.1 := congrArg (fun q => q.1.2.1) hTuple
  have hT : w.2.2 = w'.2.2 := congrArg (fun q => q.1.2.2) hTuple
  have ha : w.1.2 = w'.1.2 := congrArg (fun q => q.2) hTuple
  have hRw := hRecon w hw
  have hRw' := hRecon w' hw'
  have hi : w.1 = w'.1 := by
    apply Prod.ext
    · apply Prod.ext
      · calc
          w.1.1.1 = facetWitnessCore w.1 ∪ facetWitnessRoot w.1 := hRw.1
          _ = facetWitnessCore w'.1 ∪ facetWitnessRoot w'.1 := by rw [hB, hR]
          _ = w'.1.1.1 := hRw'.1.symm
      · calc
          w.1.1.2 = facetWitnessCore w.1 ∪ {w.1.2} := hRw.2
          _ = facetWitnessCore w'.1 ∪ {w'.1.2} := by rw [hB, ha]
          _ = w'.1.1.2 := hRw'.2.symm
    · exact ha
  cases w with
  | mk i p =>
    cases w' with
    | mk j p' =>
      dsimp at hi hR₁ hT
      cases hi
      cases p with
      | mk R₁ T =>
        cases p' with
        | mk R₁' T' =>
          dsimp at hR₁ hT
          cases hR₁
          cases hT
          rfl

theorem facet_witness_tuple_image_card
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel) :
    ((facetInheritanceWitnesses I K H V t tripleLabel).image
      facetWitnessTuple).card =
      (facetInheritanceWitnesses I K H V t tripleLabel).card := by
  classical
  exact Finset.card_image_of_injOn
    (facet_witness_tuple_injective I K H V t facetCenter tripleLabel hI)

/-- The finite lower half of IV.9.3.  The first retained-degree guarantee
    supplies at least half of the facet completions as second roots.  For
    every such root, the second guarantee supplies at least half of the
    lower-core completions as common strong third roots. -/
theorem facet_inheritance_weighted_witness_lower_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (hFirst : ∀ i ∈ I,
      (facetParents K i.1.2).card ≤
        2 * (facetWitnessSecondRoots K V i).card)
    (hThird : ∀ i ∈ I, ∀ R₁ ∈ facetWitnessSecondRoots K V i,
      (parentPairLink K V (facetWitnessCore i)).card ≤
        2 * (facetWitnessThirdRoots H V t tripleLabel i R₁).card) :
    (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      4 * (facetInheritanceWitnesses I K H V t tripleLabel).card := by
  classical
  have hOne : ∀ i ∈ I,
      (facetParents K i.1.2).card *
          (parentPairLink K V (facetWitnessCore i)).card ≤
        4 * (facetWitnessesFor K H V t tripleLabel i).card := by
    intro i hi
    let F := facetWitnessSecondRoots K V i
    let d := (parentPairLink K V (facetWitnessCore i)).card
    let T := facetWitnessThirdRoots H V t tripleLabel i
    have hSum : F.card * d ≤
        2 * ∑ R₁ ∈ F, (T R₁).card := by
      calc
        F.card * d = ∑ _R₁ ∈ F, d := by simp [mul_comm]
        _ ≤ ∑ R₁ ∈ F, 2 * (T R₁).card := by
          apply Finset.sum_le_sum
          intro R₁ hR₁
          exact hThird i hi R₁ hR₁
        _ = 2 * ∑ R₁ ∈ F, (T R₁).card := by
          rw [Finset.mul_sum]
    have hFirst' := hFirst i hi
    have hCard : (facetWitnessesFor K H V t tripleLabel i).card =
        ∑ R₁ ∈ F, (T R₁).card := by
      simp [facetWitnessesFor, F, T, Finset.card_sigma]
    rw [hCard]
    nlinarith
  calc
    (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
        ∑ i ∈ I, 4 * (facetWitnessesFor K H V t tripleLabel i).card :=
      Finset.sum_le_sum hOne
    _ = 4 * ∑ i ∈ I,
          (facetWitnessesFor K H V t tripleLabel i).card := by
      rw [Finset.mul_sum]
    _ = 4 * (facetInheritanceWitnesses I K H V t tripleLabel).card := by
      simp [facetInheritanceWitnesses, Finset.card_sigma]

end JSP523.Rank5
