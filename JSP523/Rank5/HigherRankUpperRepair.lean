import JSP523.Rank5.HigherRankUpperLabel
import JSP523.Rank5.HigherRankCleanup

/-! # Actual shared-facet inheritance repair at arbitrary rank

The parent pair colors are constructed by IV.8 cleanup. Removing actual
bad shared-facet incidences makes those colors agree with the unique
facet extension of the lower-rank inherited centers.
-/
namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α]

noncomputable def sharedFacets (K : Family α) (V : Edge α) (n : ℕ) : Family α := by
  classical
  exact (V.powersetCard n).filter fun A =>
    2 ≤ (V.filter fun x => x ∉ A ∧ insert x A ∈ K).card

theorem shared_facets_mono {K L : Family α} {V : Edge α} {n : ℕ}
    (hLK : L ⊆ K) : sharedFacets L V n ⊆ sharedFacets K V n := by
  classical
  intro A hA
  have h := Finset.mem_filter.mp hA
  refine Finset.mem_filter.mpr ⟨h.1, h.2.trans (Finset.card_le_card ?_)⟩
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx'.1, hx'.2.1, hLK hx'.2.2⟩

theorem shared_facet_of_two_completions
    (K : Family α) (V A : Edge α) (n : ℕ)
    (hAV : A ⊆ V) (hAc : A.card = n)
    {x y : α} (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    (hxA : x ∉ A) (hyA : y ∉ A)
    (hEx : insert x A ∈ K) (hEy : insert y A ∈ K) :
    A ∈ sharedFacets K V n := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hAV, hAc⟩, ?_⟩
  have hSub : ({x, y} : Edge α) ⊆
      V.filter (fun x => x ∉ A ∧ insert x A ∈ K) := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_filter.mpr ⟨hx, hxA, hEx⟩
    · have hay := Finset.mem_singleton.mp ha
      subst a
      exact Finset.mem_filter.mpr ⟨hy, hyA, hEy⟩
  simpa only [Finset.card_pair hxy] using Finset.card_le_card hSub

noncomputable def facetColorCenter [Nonempty α]
    (K H : Family α) (V : Edge α) (n t : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (upperFacetColorCleanupEdges n H V t))
    (A : Edge α) : α := by
  classical
  if hA : A ∈ sharedFacets K V n then
    have hp := Finset.mem_filter.mp hA
    have hs := Finset.mem_powersetCard.mp hp.1
    exact Classical.choose (upper_facet_color_center_exists_of_cleanup
      n K H V A t hKH hSurvive hs.1 hs.2 hp.2)
  else exact Classical.choice inferInstance

theorem facet_color_center_spec [Nonempty α]
    (K H : Family α) (V : Edge α) (n t : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (upperFacetColorCleanupEdges n H V t))
    {A : Edge α} (hA : A ∈ sharedFacets K V n) :
    facetColorCenter K H V n t hKH hSurvive A ∈ A ∧
      ∀ x ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
      ∀ y ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
      x ≠ y → upperSingletonPairColor n H V t x y =
        some (facetColorCenter K H V n t hKH hSurvive A) := by
  classical
  unfold facetColorCenter
  rw [dite_eq_left hA]
  exact Classical.choose_spec (upper_facet_color_center_exists_of_cleanup
    n K H V A t hKH hSurvive
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).1
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
    (Finset.mem_filter.mp hA).2)

def HasBadSharedFacetDeletion (K : Family α) (V : Edge α) (n : ℕ)
    (center lower : Edge α → α) (E : Edge α) : Prop :=
  ∃ A ∈ sharedFacets K V n, A ⊆ E ∧
    ∃ a ∈ A, a ≠ center A ∧ lower (A.erase a) ≠ center A

noncomputable def repairSharedFacet (K : Family α) (V : Edge α) (n : ℕ)
    (center lower : Edge α → α) : Family α := by
  classical
  exact K.filter fun E => ¬ HasBadSharedFacetDeletion K V n center lower E

theorem repair_shared_facet_subset
    (K : Family α) (V : Edge α) (n : ℕ) (center lower : Edge α → α) :
    repairSharedFacet K V n center lower ⊆ K := by
  classical
  exact Finset.filter_subset _ _

/-- Surviving occurrences inherit every original shared-facet center. -/
theorem repair_shared_facet_inheritance
    (K : Family α) (V : Edge α) (n : ℕ) (center lower : Edge α → α)
    {A : Edge α} (hA : A ∈ sharedFacets K V n)
    (hOcc : ∃ E ∈ repairSharedFacet K V n center lower, A ⊆ E) :
    ∀ a ∈ A, a ≠ center A → lower (A.erase a) = center A := by
  classical
  obtain ⟨E, hE, hAE⟩ := hOcc
  intro a ha hna
  by_contra hBad
  exact (Finset.mem_filter.mp hE).2 ⟨A, hA, hAE, a, ha, hna, hBad⟩

/-- Lower-rank inheritance survives further deletion of parent edges. -/
theorem family_rank_center_inheritance_mono
    {K L : Family α} {n : ℕ} {z : Edge α → α}
    (hLK : L ⊆ K) (hRank : FamilyRankCenterInheritance K n z) :
    FamilyRankCenterInheritance L n z := by
  intro A hOcc hAc
  obtain ⟨E, hE, hAE⟩ := hOcc
  exact hRank A ⟨E, hLK hE, hAE⟩ hAc

/-- The extension's center equals the actual original parent color on
    every facet still shared after the explicit incidence repair. -/
theorem extended_facet_center_eq_parent_color [Nonempty α]
    (K H : Family α) (V : Edge α) (n t : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (upperFacetColorCleanupEdges n H V t))
    (lower : Edge α → α) (hn : 4 ≤ n)
    (hBase : FamilyRankCenterInheritance K (n - 1) lower)
    {A : Edge α}
    (hA : A ∈ sharedFacets
      (repairSharedFacet K V n (facetColorCenter K H V n t hKH hSurvive) lower)
      V n) :
    extendFamilyRankCenter
      (repairSharedFacet K V n (facetColorCenter K H V n t hKH hSurvive) lower)
      (n - 1) lower
      (family_rank_center_inheritance_mono
        (repair_shared_facet_subset K V n _ lower) hBase)
      (by omega) A = facetColorCenter K H V n t hKH hSurvive A := by
  classical
  let center := facetColorCenter K H V n t hKH hSurvive
  let L := repairSharedFacet K V n center lower
  have hLK : L ⊆ K := Finset.filter_subset _ _
  have hAK : A ∈ sharedFacets K V n := shared_facets_mono hLK hA
  have hAc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
  have hS : 2 ≤ (V.filter fun x => x ∉ A ∧ insert x A ∈ L).card :=
    (Finset.mem_filter.mp hA).2
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
    0 < (V.filter fun x => x ∉ A ∧ insert x A ∈ L).card)
  have hOcc : ∃ E ∈ L, A ⊆ E :=
    ⟨insert x A, (Finset.mem_filter.mp hx).2.2, Finset.subset_insert _ _⟩
  apply extend_family_rank_center_agrees_with_existing
    (family_rank_center_inheritance_mono hLK hBase) (by omega) (by omega) hOcc
  exact repair_shared_facet_inheritance K V n center lower hAK hOcc

/-- Actual unordered completion-pair labels agree with the canonically
    extended facet centers on every pair of surviving completions. -/
theorem upper_pair_label_eq_extended_facet_center [Nonempty α]
    (K H : Family α) (V : Edge α) (n t : ℕ)
    (hKH : K ⊆ H) (hUniform : Uniform (n + 1) K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K (upperFacetColorCleanupEdges n H V t))
    (lower : Edge α → α) (hn : 4 ≤ n)
    (hBase : FamilyRankCenterInheritance K (n - 1) lower)
    {A : Edge α} (hAc : A.card = n) {x y : α} (hxy : x ≠ y)
    (hx : insert x A ∈ repairSharedFacet K V n
      (facetColorCenter K H V n t hKH hSurvive) lower)
    (hy : insert y A ∈ repairSharedFacet K V n
      (facetColorCenter K H V n t hKH hSurvive) lower) :
    upperUnorderedPairLabel n H V t {x, y} =
      extendFamilyRankCenter
        (repairSharedFacet K V n (facetColorCenter K H V n t hKH hSurvive) lower)
        (n - 1) lower
        (family_rank_center_inheritance_mono
          (repair_shared_facet_subset K V n _ lower) hBase)
        (by omega) A := by
  classical
  let center := facetColorCenter K H V n t hKH hSurvive
  let L := repairSharedFacet K V n center lower
  have hLK : L ⊆ K := repair_shared_facet_subset K V n center lower
  have hxK := hLK hx
  have hyK := hLK hy
  have hxV := hAmbient _ hxK (Finset.mem_insert_self x A)
  have hyV := hAmbient _ hyK (Finset.mem_insert_self y A)
  have hxA : x ∉ A := by
    intro hxA
    have hc := hUniform hxK
    rw [Finset.insert_eq_of_mem hxA, hAc] at hc
    omega
  have hyA : y ∉ A := by
    intro hyA
    have hc := hUniform hyK
    rw [Finset.insert_eq_of_mem hyA, hAc] at hc
    omega
  have hAV : A ⊆ V := (Finset.subset_insert x A).trans (hAmbient _ hxK)
  have hShared := shared_facet_of_two_completions L V A n
    hAV hAc hxV hyV hxy hxA hyA hx hy
  have hSharedK := shared_facets_mono hLK hShared
  have hColor := (facet_color_center_spec K H V n t hKH hSurvive hSharedK).2
    x (Finset.mem_filter.mpr ⟨hxV, hxA, hxK⟩)
    y (Finset.mem_filter.mpr ⟨hyV, hyA, hyK⟩) hxy
  rw [upper_unordered_pair_label_eq n H V t hxy hColor]
  exact (extended_facet_center_eq_parent_color K H V n t
    hKH hSurvive lower hn hBase hShared).symm

/-- The actual IV.9 parent/facet/deleted-vertex incidences. -/
noncomputable def facetBadIncidences
    (K : Family α) (V : Edge α) (n : ℕ)
    (center lower : Edge α → α) : Finset ((Edge α × Edge α) × α) := by
  classical
  exact ((K ×ˢ V.powersetCard n) ×ˢ V).filter fun i =>
    i.1.2 ⊆ i.1.1 ∧ i.1.2 ∈ sharedFacets K V n ∧
      i.2 ∈ i.1.2 ∧ i.2 ≠ center i.1.2 ∧ lower (i.1.2.erase i.2) ≠ center i.1.2

/-- Every edge removed by shared-facet repair has its own bad incidence. -/
theorem shared_facet_repair_loss_le_bad_incidences [Nonempty α]
    (K : Family α) (V : Edge α) (n : ℕ) (center lower : Edge α → α) :
    K.card - (repairSharedFacet K V n center lower).card ≤
      (facetBadIncidences K V n center lower).card := by
  classical
  let bad := K.filter (HasBadSharedFacetDeletion K V n center lower)
  have hWitness : ∀ E ∈ bad, ∃ w : (Edge α × Edge α) × α,
      w ∈ facetBadIncidences K V n center lower ∧ w.1.1 = E := by
    intro E hE
    obtain ⟨hEK, A, hA, hAE, a, ha, hna, hneq⟩ := Finset.mem_filter.mp hE
    have hAPow := (Finset.mem_filter.mp hA).1
    have haV := (Finset.mem_powersetCard.mp hAPow).1 ha
    exact ⟨((E, A), a), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hEK, hAPow⟩, haV⟩,
        hAE, hA, ha, hna, hneq⟩, rfl⟩
  let pick : Edge α → (Edge α × Edge α) × α := fun E =>
    if hE : E ∈ bad then Classical.choose (hWitness E hE)
    else ((E, ∅), Classical.choice inferInstance)
  have hPick : ∀ E ∈ bad,
      pick E ∈ facetBadIncidences K V n center lower ∧ (pick E).1.1 = E := by
    intro E hE
    simpa only [pick, dite_eq_left hE] using Classical.choose_spec (hWitness E hE)
  have hCount : bad.card ≤ (facetBadIncidences K V n center lower).card := by
    apply Finset.card_le_card_of_injOn pick
    · intro E hE
      exact (hPick E hE).1
    · intro E hE F hF hEq
      have h := congrArg (fun w : (Edge α × Edge α) × α => w.1.1) hEq
      simpa only [(hPick E hE).2, (hPick F hF).2] using h
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := K) (HasBadSharedFacetDeletion K V n center lower)
  change bad.card + (repairSharedFacet K V n center lower).card = K.card at hPartition
  omega

end JSP523.Rank5.HigherRankUpper
