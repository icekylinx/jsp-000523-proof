import JSP523.Rank4.NativeWitnessSlots

/-!
# Witness labels and monochromatic completion facets

For a complete graph on the completion vertices, if no two edge labels
at one vertex differ, every edge has the same label. Thus a nonprivate
facet is eligible exactly when some completion pair has its label in
the chosen base pair: a colored facet supplies such a pair, while a
monochromatic facet does so precisely when its center is in the pair.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The completion facet has two incident pair labels that differ. -/
def FacetHasDivergentLabels
    (C : Finset α) (label : α → α → α) : Prop :=
  ∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ label a b ≠ label a c

/-- In the absence of a divergent triple, all pair labels on a
nonprivate completion clique agree. -/
theorem facet_pair_labels_constant_of_no_divergence
    (C : Finset α) (label : α → α → α)
    (hSymm : ∀ a b, label a b = label b a)
    (hNo : ¬ FacetHasDivergentLabels C label)
    (p q : α) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∀ a ∈ C, ∀ b ∈ C, a ≠ b →
      label a b = label p q := by
  have hAt (x y z : α) (hx : x ∈ C) (hy : y ∈ C)
      (hz : z ∈ C) (hxy : x ≠ y) (hxz : x ≠ z)
      (hyz : y ≠ z) : label x y = label x z := by
    by_contra hDiff
    exact hNo ⟨x, hx, y, hy, z, hz,
      hxy, hxz, hyz, hDiff⟩
  intro a ha b hb hab
  by_cases hap : a = p
  · subst a
    by_cases hbq : b = q
    · subst b
      rfl
    · exact hAt p b q hp hb hq hab hpq hbq
  · by_cases haq : a = q
    · subst a
      by_cases hbp : b = p
      · subst b
        exact hSymm q p
      · exact (hAt q b p hq hb hp hab hpq.symm hbp).trans
          (hSymm q p)
    have hPa : label p a = label p q :=
      hAt p a q hp ha hq (by intro h; exact hap h.symm)
        hpq haq
    have hAp : label a p = label p q := by
      rw [hSymm a p]
      exact hPa
    by_cases hbp : b = p
    · subst b
      exact hAp
    · exact (hAt a b p ha hb hp hab hap hbp).trans hAp

/-- The manuscript's selected-slot criterion for a nonprivate facet:
colored, or monochromatic with its center in the base pair. -/
def FacetEligibleAtPair
    (C : Finset α) (label : α → α → α) (Q : Finset α) : Prop :=
  2 ≤ C.card ∧
    (FacetHasDivergentLabels C label ∨
      ∃ z ∈ Q, ∀ a ∈ C, ∀ b ∈ C,
        a ≠ b → label a b = z)

/-- Every witness label in Q makes the facet eligible. A facet with no
divergent labels must have that witness as its monochromatic center. -/
theorem facet_witness_implies_eligible
    (C : Finset α) (label : α → α → α) (Q : Finset α)
    (hSymm : ∀ a b, label a b = label b a)
    (p q : α) (hp : p ∈ C) (hq : q ∈ C)
    (hpq : p ≠ q) (hLabel : label p q ∈ Q) :
    FacetEligibleAtPair C label Q := by
  have hCard : 2 ≤ C.card :=
    (Finset.one_lt_card.mpr ⟨p, hp, q, hq, hpq⟩)
  refine ⟨hCard, ?_⟩
  by_cases hDivergent : FacetHasDivergentLabels C label
  · exact Or.inl hDivergent
  · exact Or.inr ⟨label p q, hLabel,
      facet_pair_labels_constant_of_no_divergence
        C label hSymm hDivergent p q hp hq hpq⟩

/-- If all pair labels lie in the three-element facet Q+x, every
eligible slot has some pair label in Q. For a colored facet, two
different labels cannot both be the lone vertex x outside Q. -/
theorem facet_eligible_implies_witness
    (C : Finset α) (label : α → α → α)
    (Q : Finset α) (x : α)
    (hLabelFacet : ∀ a ∈ C, ∀ b ∈ C,
      a ≠ b → label a b ∈ insert x Q)
    (hEligible : FacetEligibleAtPair C label Q) :
    ∃ a ∈ C, ∃ b ∈ C,
      a ≠ b ∧ label a b ∈ Q := by
  rcases hEligible with ⟨hCard, hColored | hMono⟩
  · obtain ⟨a, ha, b, hb, c, hc,
        hab, hac, _hbc, hDiff⟩ := hColored
    by_cases habQ : label a b ∈ Q
    · exact ⟨a, ha, b, hb, hab, habQ⟩
    · have hAB := hLabelFacet a ha b hb hab
      have hAC := hLabelFacet a ha c hc hac
      have hABx : label a b = x := by
        rcases Finset.mem_insert.mp hAB with h | h
        · exact h
        · exact False.elim (habQ h)
      have hACQ : label a c ∈ Q := by
        rcases Finset.mem_insert.mp hAC with h | h
        · exact False.elim (hDiff (hABx.trans h.symm))
        · exact h
      exact ⟨a, ha, c, hc, hac, hACQ⟩
  · obtain ⟨z, hzQ, hMono⟩ := hMono
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hCard
    exact ⟨a, ha, b, hb, hab, (hMono a ha b hb hab) ▸ hzQ⟩

end JSP523.Rank4
