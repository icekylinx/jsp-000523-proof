import JSP523.Rank5.UpperFacetInheritance

/-!
# The rank-five shadow ledger after facet inheritance repair

This is the actual-family bridge from IV.9 to IV.A.  The same family that
survives the facet-to-triple repair enters the private-facet count.  The
edge loss is charged to the finite bad-incidence set.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Shadow inclusion for a subfamily, used when restoring the original
    family's shadow after inheritance repair. -/
theorem four_shadow_mono {K L : Family α} (hLK : L ⊆ K) :
    fourShadow L ⊆ fourShadow K := by
  intro A hA
  obtain ⟨E, hEL, hAE, hAc⟩ := (mem_four_shadow_iff_parent L A).mp hA
  exact (mem_four_shadow_iff_parent K A).mpr
    ⟨E, hLK hEL, hAE, hAc⟩

/-- The exact number of edges removed by the IV.9 shared-facet repair is
    the size of its bad-parent set. -/
theorem shared_facet_repair_loss_eq_bad_parent_edges
    (K : Family α) (facetCenter tripleLabel : Edge α → α) :
    K.card =
      (repairSharedFacetInheritance K facetCenter tripleLabel).card +
        (badFacetParentEdges K facetCenter tripleLabel).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := K) (HasBadFacetTripleIncidence K facetCenter tripleLabel)
  simpa only [repairSharedFacetInheritance, badFacetParentEdges,
    Nat.add_comm] using h.symm

/-- IV.A.3 with the actual IV.9 deletion charged to bad incidences.
    The rooted term belongs to the repaired family, exactly as required
    for the subsequent assigned-prefix argument. -/
theorem four_shadow_bound_after_facet_incidence_repair
    [Nonempty α]
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hFacetCenters : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A) :
    2 * K.card ≤ (fourShadow K).card +
      2 * (rootedEdges
        (repairSharedFacetInheritance K facetCenter tripleLabel)
        tripleLabel).card +
      2 * (facetBadIncidences K V facetCenter tripleLabel).card := by
  classical
  let L := repairSharedFacetInheritance K facetCenter tripleLabel
  have hLK : L ⊆ K := Finset.filter_subset _ _
  have hShadow : (fourShadow L).card ≤ (fourShadow K).card :=
    Finset.card_le_card (four_shadow_mono hLK)
  have hLoss := shared_facet_repair_loss_eq_bad_parent_edges
    K facetCenter tripleLabel
  have hBad := bad_facet_parent_edges_card_le_incidences
    K V facetCenter tripleLabel hAmbient
  have hRepaired := four_shadow_bound_after_shared_facet_repair
    K facetCenter tripleLabel hUniform hFacetCenters
  dsimp [L] at hShadow
  omega

/-- The scaled IV.A.3 inequality after substituting any IV.9 incidence
    estimate.  The interface exposes the repaired rooted subfamily, which
    is the one sent to the assigned-prefix argument. -/
theorem four_shadow_bound_from_facet_incidence_budget
    [Nonempty α]
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (Q M W : ℕ)
    (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hFacetCenters : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hBad : Q * M *
      (facetBadIncidences K V facetCenter tripleLabel).card ≤ W) :
    Q * M * (2 * K.card) ≤
      Q * M * (fourShadow K).card +
      2 * Q * M *
        (rootedEdges
          (repairSharedFacetInheritance K facetCenter tripleLabel)
          tripleLabel).card + 2 * W := by
  have hShadow := four_shadow_bound_after_facet_incidence_repair
    K V facetCenter tripleLabel hUniform hAmbient hFacetCenters
  have hScaled := Nat.mul_le_mul_left (Q * M) hShadow
  nlinarith

end JSP523.Rank5
