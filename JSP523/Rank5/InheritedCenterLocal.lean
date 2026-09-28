import JSP523.Rank5.CoherenceDefect
import JSP523.Rank5.HereditaryCenterExtension
import JSP523.Counting.PrefixCommonSystem
import Mathlib.Data.Finset.Prod

/-!
# Centers on shared four-faces from inherited triple centers

The rank-five shadow argument asks for a center on each shared four-face
whose triples containing that center keep the same triple label.  This is
already forced locally by the noncenter-deletion inheritance law on actual
triples.  This file packages that implication as the interface consumed by
`CoherenceDefect`.
-/

namespace JSP523.Rank5

section InheritedCenterLocal

variable {α : Type*} [DecidableEq α]

/-- Triple labels obey the hereditary law on every triple occurring inside
    an edge of `all`. -/
def ActualTripleCenterInheritance (all : Family α) (z : Edge α → α) : Prop :=
  ∀ S : Edge α, (∃ E ∈ all, S ⊆ E) → S.card = 3 →
    z S ∈ S ∧ ∀ a ∈ S, a ≠ z S → z (S.erase a) = z S

/-- The label assignment chooses an actual vertex on every triple contained
    in a parent edge.  This is the uncleaned label condition in §IV.7. -/
def ActualTripleLabels (all : Family α) (z : Edge α → α) : Prop :=
  ∀ S : Edge α, (∃ E ∈ all, S ⊆ E) → S.card = 3 → z S ∈ S

/-- A parent edge is dirty at triple level if one of its actual triples
    violates inheritance when a noncenter vertex is deleted. -/
def HasBadTripleDeletion (z : Edge α → α)
    (E : Edge α) : Prop :=
  ∃ S : Edge α, S ⊆ E ∧ S.card = 3 ∧
    ∃ a ∈ S, a ≠ z S ∧ z (S.erase a) ≠ z S

/-- The finite set of bad `(triple, deleted vertex)` witnesses inside one
    parent edge. -/
def badTripleDeletionWitnesses (z : Edge α → α) (E : Edge α) :
    Finset (Edge α × α) :=
  ((E.powersetCard 3).product E).filter (fun p =>
    p.2 ∈ p.1 ∧ p.2 ≠ z p.1 ∧ z (p.1.erase p.2) ≠ z p.1)

/-- Keep the parent edge with each witness, so witnesses from distinct
    parents remain distinct incidences. -/
def badTripleDeletionIncidences (all : Family α) (z : Edge α → α) :
    Finset ((_E : Edge α) × Edge α × α) :=
  all.sigma (fun E => badTripleDeletionWitnesses z E)

theorem badTripleDeletionWitnesses_nonempty_of_bad
    (z : Edge α → α) {E : Edge α}
    (hbad : HasBadTripleDeletion z E) :
    (badTripleDeletionWitnesses z E).Nonempty := by
  classical
  obtain ⟨S, hSE, hSc, a, ha, hna, hneq⟩ := hbad
  have haE : a ∈ E := hSE ha
  refine ⟨(S, a), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hSE, hSc⟩, haE⟩
  · exact ⟨ha, hna, hneq⟩

/-- Auxiliary triple-to-pair cleanup: remove every parent edge touched by a
    bad triple-deletion incidence.  This is not the rank-five §IV.9 repair,
    whose bad core is a shared four-face. -/
noncomputable def repairTripleInheritance (all : Family α) (z : Edge α → α) : Family α := by
  classical
  exact all.filter (fun E => ¬ HasBadTripleDeletion z E)

noncomputable def badTripleParentEdges (all : Family α) (z : Edge α → α) : Family α := by
  classical
  exact all.filter (HasBadTripleDeletion z)

/-- Once every edge incident with a bad triple deletion is removed, all
    triples that still occur inherit their center after noncenter deletion.
    This is the local, rank-three instance of (9.6). -/
theorem actualTripleCenterInheritance_of_repair
    (all : Family α) (z : Edge α → α)
    (hLabels : ActualTripleLabels all z) :
    ActualTripleCenterInheritance (repairTripleInheritance all z) z := by
  intro S hOcc hSc
  classical
  obtain ⟨E, hE, hSE⟩ := hOcc
  change E ∈ all.filter (fun E => ¬ HasBadTripleDeletion z E) at hE
  have hEparts := Finset.mem_filter.mp hE
  have hEall : E ∈ all := hEparts.1
  have hSall : ∃ F ∈ all, S ⊆ F := ⟨E, hEall, hSE⟩
  refine ⟨hLabels S hSall hSc, ?_⟩
  intro a ha hna
  by_contra hneq
  have hbad : HasBadTripleDeletion z E := by
    exact ⟨S, hSE, hSc, a, ha, hna, hneq⟩
  exact hEparts.2 hbad

/-- Every removed edge can be assigned one of its bad deletion witnesses;
    the assignment is injective because the incidence remembers its parent. -/
theorem removed_edges_le_bad_triple_incidences
    (all : Family α) (z : Edge α → α) [Nonempty α] :
    (badTripleParentEdges all z).card ≤
      (badTripleDeletionIncidences all z).card := by
  classical
  let removed := badTripleParentEdges all z
  let pick : Edge α → (E : Edge α) × Edge α × α := fun E =>
    ⟨E, if h : HasBadTripleDeletion z E then
      Classical.choose (badTripleDeletionWitnesses_nonempty_of_bad z h)
      else (∅, Classical.choice inferInstance)⟩
  apply Finset.card_le_card_of_injOn pick
  · intro E hE
    have hE' : E ∈ all ∧ HasBadTripleDeletion z E := by
      simpa [removed, badTripleParentEdges] using hE
    have hw := Classical.choose_spec
      (badTripleDeletionWitnesses_nonempty_of_bad z hE'.2)
    change pick E ∈ all.sigma (fun E => badTripleDeletionWitnesses z E)
    rw [Finset.mem_sigma]
    refine ⟨hE'.1, ?_⟩
    simpa [pick, hE'.2] using hw
  · intro E hE F hF hEq
    exact congrArg Sigma.fst hEq

/-- Exact deletion accounting: the repaired family loses precisely its bad
    parent edges, so the witness injection bounds the actual loss. -/
theorem repairTripleInheritance_loss_le_bad_incidences
    (all : Family α) (z : Edge α → α) [Nonempty α] :
    all.card - (repairTripleInheritance all z).card ≤
      (badTripleDeletionIncidences all z).card := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := all) (HasBadTripleDeletion z)
  have hbad : (badTripleParentEdges all z).card +
      (repairTripleInheritance all z).card = all.card := by
    simpa [badTripleParentEdges, repairTripleInheritance] using hpartition
  have hbound := removed_edges_le_bad_triple_incidences all z
  omega

/-- A four-face of an actual five-edge has a unique center compatible with
    all of its triple labels. -/
theorem actual_four_face_center_existsUnique
    (all : Family α) (z : Edge α → α)
    (hTriple : ActualTripleCenterInheritance all z)
    {A : Edge α} (hA : A ∈ fourShadow all) :
    ∃! v : α, v ∈ A ∧ ∀ S : Edge α, S ⊆ A → S.card = 3 →
      v ∈ S → z S = v := by
  obtain ⟨E, hE, hAE, hAc⟩ :=
    (mem_fourShadow_iff_parent all A).mp hA
  have hcardA : A.card = 4 := hAc
  have hHereditary : HereditaryDeletionCenters A z := by
    constructor
    · intro a ha
      have hSub : A.erase a ⊆ E := by
        exact Finset.Subset.trans (Finset.erase_subset a A) hAE
      exact (hTriple (A.erase a) ⟨E, hE, hSub⟩ (by
        have hErase := Finset.card_erase_add_one ha
        omega)).1
    · intro a ha b hb hbn
      have hFace : (A.erase a).card = 3 := by
        have hErase := Finset.card_erase_add_one ha
        omega
      have hSub : A.erase a ⊆ E :=
        Finset.Subset.trans (Finset.erase_subset a A) hAE
      have hLocal := (hTriple (A.erase a) ⟨E, hE, hSub⟩ hFace).2
      have hEq : z ((A.erase a).erase b) = z (A.erase a) :=
        hLocal b hb hbn
      exact hEq
  obtain ⟨v, hvA, hvFaces⟩ :=
    (hereditary_center_existsUnique (by omega : 4 ≤ A.card) hHereditary).exists
  refine ⟨v, ?_, ?_⟩
  · refine ⟨hvA, ?_⟩
    intro S hSA hSc hVS
    obtain ⟨a, ha, hna⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : S.card < A.card)
    have hsub : S ⊆ A.erase a := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun hxa => hna (hxa ▸ hx), hSA hx⟩
    have hEq : S = A.erase a :=
      Finset.eq_of_subset_of_card_le hsub (by
        have hErase := Finset.card_erase_add_one ha
        omega)
    have hav : a ≠ v := by
      intro hav
      subst a
      exact hna hVS
    rw [hEq]
    exact hvFaces a ha hav
  · intro w hw
    apply (hereditary_center_agrees_with_existing
      (by omega : 4 ≤ A.card) hvFaces ?_).symm
    intro a ha haw
    have hS : A.erase a ⊆ A := Finset.erase_subset a A
    have hSc : (A.erase a).card = 3 := by
      have hErase := Finset.card_erase_add_one ha
      omega
    have hwS : w ∈ A.erase a := Finset.mem_erase.mpr ⟨haw.symm, hw.1⟩
    exact hw.2 (A.erase a) hS hSc hwS

/-- Choose compatible centers for all actual shared four-faces from the
    inherited law on actual triples. -/
noncomputable def inheritedFourFaceCenter
    (all : Family α) (z : Edge α → α)
    [Nonempty α]
    (hTriple : ActualTripleCenterInheritance all z) : Edge α → α :=
  fun A => if hA : A ∈ sharedFourShadow all then
    Classical.choose
      (actual_four_face_center_existsUnique all z hTriple
        ((Finset.mem_filter.mp hA).1)).exists
  else Classical.choice inferInstance

theorem inheritedFourFaceCenter_spec
    (all : Family α) (z : Edge α → α)
    [Nonempty α]
    (hTriple : ActualTripleCenterInheritance all z) :
    SharedFacetCenterInheritance all z (inheritedFourFaceCenter all z hTriple) := by
  intro A hA
  dsimp [inheritedFourFaceCenter]
  rw [dite_eq_left hA]
  exact Classical.choose_spec
    (actual_four_face_center_existsUnique all z hTriple
      ((Finset.mem_filter.mp hA).1)).exists

/-- Auxiliary shadow estimate from triple-to-pair cleanup.  This stronger
    lower-rank inheritance route is separate from the §IV.9 repair below. -/
theorem four_shadow_bound_after_triple_repair
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    [Nonempty α]
    (hLabels : ActualTripleLabels all z) :
    2 * (repairTripleInheritance all z).card +
      (sharedFourShadow (repairTripleInheritance all z)).card ≤
      (fourShadow (repairTripleInheritance all z)).card +
        2 * (rootedEdges (repairTripleInheritance all z) z).card := by
  classical
  have hUniformRepair : Uniform 5 (repairTripleInheritance all z) := by
    intro E hE
    exact hUniform (Finset.mem_filter.mp hE).1
  exact four_shadow_bound_of_shared_facet_inheritance
    (repairTripleInheritance all z) z
    (inheritedFourFaceCenter (repairTripleInheritance all z) z
      (actualTripleCenterInheritance_of_repair all z hLabels))
    hUniformRepair
    (inheritedFourFaceCenter_spec (repairTripleInheritance all z) z
      (actualTripleCenterInheritance_of_repair all z hLabels))

/-- The coherence defect vanishes when the triple labels already satisfy
    actual noncenter-deletion inheritance. -/
theorem four_shadow_bound_of_actual_triple_inheritance
    (all : Family α) (z : Edge α → α)
    (hUniform : Uniform 5 all)
    [Nonempty α]
    (hTriple : ActualTripleCenterInheritance all z) :
    2 * all.card + (sharedFourShadow all).card ≤
      (fourShadow all).card + 2 * (rootedEdges all z).card := by
  exact four_shadow_bound_of_shared_facet_inheritance all z
    (inheritedFourFaceCenter all z hTriple) hUniform
    (inheritedFourFaceCenter_spec all z hTriple)

/-- The manuscript's rank-five bad incidence: a parent edge contains a
    shared four-face `A`, and deleting a noncenter vertex gives a triple
    whose fixed parent label disagrees with the facet center. -/
def HasBadFacetTripleIncidence
    (all : Family α) (facetCenter : Edge α → α) (tripleLabel : Edge α → α)
    (E : Edge α) : Prop :=
  ∃ A : Edge α, A ⊆ E ∧ A ∈ sharedFourShadow all ∧
    ∃ a ∈ A, a ≠ facetCenter A ∧
      tripleLabel (A.erase a) ≠ facetCenter A

/-- Delete every retained parent edge touched by a rank-five IV.9
    facet-to-triple inheritance failure. -/
noncomputable def repairSharedFacetInheritance
    (all : Family α) (facetCenter : Edge α → α)
    (tripleLabel : Edge α → α) : Family α := by
  classical
  exact all.filter (fun E => ¬ HasBadFacetTripleIncidence all facetCenter tripleLabel E)

/-- The actual rank-five inheritance repaired by (IV.9): after removing all
    parent edges touched by a bad shared-facet incidence, each surviving
    shared facet keeps its center on every triple containing that center. -/
theorem shared_facet_inheritance_of_repair
    (all : Family α) (facetCenter tripleLabel : Edge α → α)
    (hFacetCenters : ∀ A ∈ sharedFourShadow all, facetCenter A ∈ A) :
    SharedFacetCenterInheritance
      (repairSharedFacetInheritance all facetCenter tripleLabel)
      tripleLabel facetCenter := by
  classical
  intro A hARepair
  have hAshadowRepair : A ∈ fourShadow
      (repairSharedFacetInheritance all facetCenter tripleLabel) :=
    (Finset.mem_filter.mp hARepair).1
  have hAparent := (mem_fourShadow_iff_parent
    (repairSharedFacetInheritance all facetCenter tripleLabel) A).mp hAshadowRepair
  obtain ⟨E, hERepair, hAE, hAcard⟩ := hAparent
  have hEparts := Finset.mem_filter.mp hERepair
  have hEall : E ∈ all := hEparts.1
  have hAshadowAll : A ∈ fourShadow all :=
    (mem_fourShadow_iff_parent all A).mpr ⟨E, hEall, hAE, hAcard⟩
  have hParentsMono : facetParents
      (repairSharedFacetInheritance all facetCenter tripleLabel) A ⊆
        facetParents all A := by
    intro F hF
    have hFparts := Finset.mem_filter.mp hF
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hFparts.1).1, hFparts.2⟩
  have hManyRepair : 2 ≤ (facetParents
      (repairSharedFacetInheritance all facetCenter tripleLabel) A).card :=
    (Finset.mem_filter.mp hARepair).2
  have hManyAll : 2 ≤ (facetParents all A).card :=
    le_trans hManyRepair (Finset.card_le_card hParentsMono)
  have hASharedAll : A ∈ sharedFourShadow all :=
    Finset.mem_filter.mpr ⟨hAshadowAll, hManyAll⟩
  refine ⟨hFacetCenters A hASharedAll, ?_⟩
  intro S hSA hSc hCenterS
  obtain ⟨a, haA, hnaS⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (by omega : S.card < A.card)
  have hSsub : S ⊆ A.erase a := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxa => hnaS (hxa ▸ hx), hSA hx⟩
  have hSeq : S = A.erase a :=
    Finset.eq_of_subset_of_card_le hSsub (by
      have hErase := Finset.card_erase_add_one haA
      omega)
  have hAnoncenter : a ≠ facetCenter A := by
    intro haCenter
    subst a
    exact hnaS hCenterS
  have hAgree : tripleLabel (A.erase a) = facetCenter A := by
    by_contra hneq
    exact hEparts.2 ⟨A, hAE, hASharedAll, a, haA, hAnoncenter, hneq⟩
  simpa [hSeq] using hAgree

/-- Thus the rank-five shadow bound applies to the repaired family from
    facet-center membership alone; (IV.9) supplies the small-loss estimate
    separately. -/
theorem four_shadow_bound_after_shared_facet_repair
    (all : Family α) (facetCenter tripleLabel : Edge α → α)
    (hUniform : Uniform 5 all)
    (hFacetCenters : ∀ A ∈ sharedFourShadow all, facetCenter A ∈ A) :
    2 * (repairSharedFacetInheritance all facetCenter tripleLabel).card +
      (sharedFourShadow
        (repairSharedFacetInheritance all facetCenter tripleLabel)).card ≤
      (fourShadow
        (repairSharedFacetInheritance all facetCenter tripleLabel)).card +
        2 * (rootedEdges
          (repairSharedFacetInheritance all facetCenter tripleLabel) tripleLabel).card := by
  classical
  have hUniformRepair : Uniform 5
      (repairSharedFacetInheritance all facetCenter tripleLabel) := by
    intro E hE
    exact hUniform (Finset.mem_filter.mp hE).1
  exact four_shadow_bound_of_shared_facet_inheritance
    (repairSharedFacetInheritance all facetCenter tripleLabel)
    tripleLabel facetCenter hUniformRepair
    (shared_facet_inheritance_of_repair all facetCenter tripleLabel hFacetCenters)

/-- In the parent pair-link used in §IV.9, overlapping retained roots are
    precisely bad partners whenever a good partner is required to be
    disjoint. -/
theorem overlapping_parent_roots_are_badPartners
    {H : Family α} {V B R T : Edge α}
    (good : Edge α → Edge α → Edge α → Prop)
    (hT : T ∈ parentPairLink H V B)
    (a : α) (haR : a ∈ R) (haT : a ∈ T)
    (hGoodDisjoint : ∀ B R T, good B R T → Disjoint R T) :
    T ∈ badParentPartners H V B R good := by
  classical
  change T ∈ (parentPairLink H V B).filter
    (fun T => ¬ good B R T)
  apply Finset.mem_filter.mpr
  refine ⟨hT, ?_⟩
  intro hgood
  exact (Finset.disjoint_left.mp (hGoodDisjoint B R T hgood)) haR haT

/-- Distinct two-point completion roots sharing `a` can intersect nowhere
    else, or they would define the same five-edge parent. -/
theorem shared_facet_completion_roots_intersect
    {R T : Edge α} {a : α}
    (hRcard : R.card = 2) (hTcard : T.card = 2)
    (haR : a ∈ R) (haT : a ∈ T) (hRT : R ≠ T) :
    R ∩ T = {a} := by
  ext x
  constructor
  · intro hx
    have hxR : x ∈ R := (Finset.mem_inter.mp hx).1
    have hxT : x ∈ T := (Finset.mem_inter.mp hx).2
    by_cases hxa : x = a
    · simp [hxa]
    · have hax : a ≠ x := fun h => hxa h.symm
      have hRpair : ({a, x} : Edge α) = R := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact haR
          · exact hxR
        · have hp : ({a, x} : Edge α).card = 2 := by simp [hax]
          rw [hRcard, hp]
      have hTpair : ({a, x} : Edge α) = T := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact haT
          · exact hxT
        · have hp : ({a, x} : Edge α).card = 2 := by simp [hax]
          rw [hTcard, hp]
      exact False.elim (hRT (hRpair.symm.trans hTpair))
  · intro hx
    have hxa : x = a := Finset.mem_singleton.mp hx
    subst x
    exact Finset.mem_inter.mpr ⟨haR, haT⟩

/-- The concrete IV.9 partner map for rank five.  From two retained
    five-edge parents `B ∪ R` and `B ∪ T` of the shared facet `B ∪ {a}`,
    the second completion root `T` is an actual bad partner of `R` at the
    triple core `B`, because the two roots overlap at `a`. -/
theorem shared_facet_second_parent_is_badPartner
    {K H : Family α} {V A E F : Edge α} {a : α}
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hE : E ∈ K) (hF : F ∈ K)
    (hAcard : A.card = 4) (hAE : A ⊆ E) (hAF : A ⊆ F)
    (ha : a ∈ A) (hEF : E ≠ F)
    (hAmbient : ∀ G ∈ K, G ⊆ V)
    (good : Edge α → Edge α → Edge α → Prop)
    (hGoodDisjoint : ∀ B R T, good B R T → Disjoint R T) :
    let B := A.erase a
    let R := E \ B
    let T := F \ B
    T ∈ badParentPartners H V B R good ∧ R ≠ T ∧ R ∩ T = {a} := by
  classical
  dsimp
  have hBcard : (A.erase a).card = 3 := by
    have hErase := Finset.card_erase_add_one ha
    omega
  have hBE : A.erase a ⊆ E :=
    (Finset.erase_subset a A).trans hAE
  have hBF : A.erase a ⊆ F :=
    (Finset.erase_subset a A).trans hAF
  have hEcard := hUniform hE
  have hFcard := hUniform hF
  have hRcard : (E \ A.erase a).card = 2 := by
    rw [Finset.card_sdiff_of_subset hBE, hEcard, hBcard]
  have hTcard : (F \ A.erase a).card = 2 := by
    rw [Finset.card_sdiff_of_subset hBF, hFcard, hBcard]
  have hRsub : E \ A.erase a ⊆ V :=
    Finset.sdiff_subset.trans (hAmbient E hE)
  have hTsub : F \ A.erase a ⊆ V :=
    Finset.sdiff_subset.trans (hAmbient F hF)
  have hRdisj : Disjoint (E \ A.erase a) (A.erase a) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 hxB
  have hTdisj : Disjoint (F \ A.erase a) (A.erase a) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    exact (Finset.mem_sdiff.mp hx).2 hxB
  have hEdgeE : A.erase a ∪ (E \ A.erase a) ∈ H := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hBE]
    exact hKH hE
  have hEdgeF : A.erase a ∪ (F \ A.erase a) ∈ H := by
    rw [Finset.union_comm, Finset.sdiff_union_of_subset hBF]
    exact hKH hF
  have hRlink : E \ A.erase a ∈ parentPairLink H V (A.erase a) :=
    mem_parentPairLink.mpr
      ⟨hRsub, hRcard, hRdisj, hEdgeE⟩
  have hTlink : F \ A.erase a ∈ parentPairLink H V (A.erase a) :=
    mem_parentPairLink.mpr
      ⟨hTsub, hTcard, hTdisj, hEdgeF⟩
  have haR : a ∈ E \ A.erase a := by
    refine Finset.mem_sdiff.mpr ⟨hAE ha, ?_⟩
    intro hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  have haT : a ∈ F \ A.erase a := by
    refine Finset.mem_sdiff.mpr ⟨hAF ha, ?_⟩
    intro hmem
    exact (Finset.mem_erase.mp hmem).1 rfl
  have hRT : E \ A.erase a ≠ F \ A.erase a := by
    intro hEq
    apply hEF
    calc
      E = E \ A.erase a ∪ A.erase a :=
        (Finset.sdiff_union_of_subset hBE).symm
      _ = F \ A.erase a ∪ A.erase a := by rw [hEq]
      _ = F := Finset.sdiff_union_of_subset hBF
  refine ⟨overlapping_parent_roots_are_badPartners
      good hTlink a haR haT hGoodDisjoint, hRT, ?_⟩
  exact shared_facet_completion_roots_intersect hRcard hTcard haR haT hRT

/-- For a fixed parent root, distinct deleted vertices on shared facets
    select distinct second roots.  Together with the preceding lemma each
    selected root is an actual bad parent-link partner. -/
theorem shared_facet_partner_choice_injective
    {R T T' : Edge α} {a a' : α}
    (hRT : R ∩ T = {a}) (hRT' : R ∩ T' = {a'})
    (hTT' : T = T') : a = a' := by
  have ha' : a' ∈ R ∩ T := by
    have hmem : a' ∈ R ∩ T' := by rw [hRT']; simp
    simpa [hTT'] using hmem
  exact (Finset.mem_singleton.mp (hRT ▸ ha')).symm

/-- For a fixed retained root, bad facet incidences indexed by their
    deleted vertex inject into the actual bad parent-partner set.  This is a
    finite upper bound, not a separately assumed incidence estimate. -/
theorem bad_deleted_vertices_le_bad_parentPartners
    {H : Family α} {V B R : Edge α}
    (good : Edge α → Edge α → Edge α → Prop)
    (A : Finset α) (T : α → Edge α)
    (hPartner : ∀ a ∈ A, T a ∈ badParentPartners H V B R good)
    (hRootIntersection : ∀ a ∈ A, R ∩ T a = {a}) :
    A.card ≤ (badParentPartners H V B R good).card := by
  classical
  apply Finset.card_le_card_of_injOn T
  · intro a ha
    exact hPartner a (Finset.mem_coe.mp ha)
  · intro a ha b hb hEq
    have hbmem : b ∈ R ∩ T b := by
      rw [hRootIntersection b (Finset.mem_coe.mp hb)]
      simp
    have hbmem' : b ∈ R ∩ T a := by simpa [hEq] using hbmem
    have hba : b = a :=
      Finset.mem_singleton.mp
        ((hRootIntersection a (Finset.mem_coe.mp ha)).symm ▸ hbmem')
    exact hba.symm

/-- Finite rank-five form of the witness-to-partner count.  Fix a parent
    edge `E` through a triple core `B`; for each bad deletion vertex `a`,
    a distinct retained completion of `B ∪ {a}` supplies a bad partner of
    the root `E \ B`.  Distinct `a`s give distinct partners, hence the
    incidence count is bounded by the actual bad-partner count. -/
theorem shared_facet_bad_vertices_le_parentPartners
    {K H : Family α} {V B E : Edge α}
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hE : E ∈ K) (hBcard : B.card = 3) (hBE : B ⊆ E)
    (hAmbient : ∀ G ∈ K, G ⊆ V)
    (badVertices : Finset α)
    (hbadSub : ∀ a ∈ badVertices, a ∈ E \ B)
    (hAltParent : ∀ a ∈ badVertices,
      ∃ F ∈ K, F ≠ E ∧ B ∪ {a} ⊆ F)
    (good : Edge α → Edge α → Edge α → Prop)
    (hGoodDisjoint : ∀ B R T, good B R T → Disjoint R T) :
    badVertices.card ≤
      (badParentPartners H V B (E \ B) good).card := by
  classical
  let T : α → Edge α := fun a =>
    if ha : a ∈ badVertices then
      Classical.choose (hAltParent a ha) \ B
    else ∅
  have hPartner : ∀ a ∈ badVertices,
      T a ∈ badParentPartners H V B (E \ B) good := by
    intro a ha
    have hAlt := Classical.choose_spec (hAltParent a ha)
    rcases hAlt with ⟨hF, hFE, hAF⟩
    have haE : a ∈ E := (Finset.mem_sdiff.mp (hbadSub a ha)).1
    have haNotB : a ∉ B := (Finset.mem_sdiff.mp (hbadSub a ha)).2
    have hAcard : (B ∪ {a}).card = 4 := by
      have hdisj : Disjoint B ({a} : Edge α) := by
        apply Finset.disjoint_left.mpr
        intro x hx hxSing
        have hxEq : x = a := Finset.mem_singleton.mp hxSing
        subst x
        exact haNotB hx
      rw [Finset.card_union_of_disjoint hdisj]
      simp [hBcard]
    have hAE : B ∪ {a} ⊆ E := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxB | hxA
      · exact hBE hxB
      · have : x = a := Finset.mem_singleton.mp hxA
        simpa [this] using haE
    have hAT : B ∪ {a} ⊆ Classical.choose (hAltParent a ha) := hAF
    have hTspec := shared_facet_second_parent_is_badPartner
      (K := K) (H := H) (V := V) (A := B ∪ {a}) (E := E)
      (F := Classical.choose (hAltParent a ha)) (a := a)
      hKH hUniform hE hF hAcard hAE hAT (by simp) hFE.symm hAmbient
      good hGoodDisjoint
    simpa [T, ha, haNotB] using hTspec.1
  have hIntersection : ∀ a ∈ badVertices, E \ B ∩ T a = {a} := by
    intro a ha
    have hAlt := Classical.choose_spec (hAltParent a ha)
    rcases hAlt with ⟨hF, hFE, hAF⟩
    have haE : a ∈ E := (Finset.mem_sdiff.mp (hbadSub a ha)).1
    have haNotB : a ∉ B := (Finset.mem_sdiff.mp (hbadSub a ha)).2
    have hAcard : (B ∪ {a}).card = 4 := by
      have hdisj : Disjoint B ({a} : Edge α) := by
        apply Finset.disjoint_left.mpr
        intro x hx hxSing
        have hxEq : x = a := Finset.mem_singleton.mp hxSing
        subst x
        exact haNotB hx
      rw [Finset.card_union_of_disjoint hdisj]
      simp [hBcard]
    have hAE : B ∪ {a} ⊆ E := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxB | hxA
      · exact hBE hxB
      · have : x = a := Finset.mem_singleton.mp hxA
        simpa [this] using haE
    have hAT : B ∪ {a} ⊆ Classical.choose (hAltParent a ha) := hAF
    have hRoot := shared_facet_second_parent_is_badPartner
      (K := K) (H := H) (V := V) (A := B ∪ {a}) (E := E)
      (F := Classical.choose (hAltParent a ha)) (a := a)
      hKH hUniform hE hF hAcard hAE hAT (by simp) hFE.symm hAmbient
      good hGoodDisjoint
    simpa [T, ha, haNotB] using hRoot.2.2
  exact bad_deleted_vertices_le_bad_parentPartners good badVertices T
    hPartner hIntersection

end InheritedCenterLocal

end JSP523.Rank5
