import JSP523.Rank5.OverlapPartnerBudget
import JSP523.Rank5.RepeatedCenterActual
import JSP523.Rank5.MultilevelCleanup

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

theorem actual_core_link_two_eq_parent_pair_link
    (H : Family α) (V B : Edge α) :
    actualCoreLink H V B 2 = parentPairLink H V B := by
  ext R
  rw [mem_actual_core_link, mem_parent_pair_link]

theorem common_prefix_tails_comm
    (H : Family α) (V P Q : Edge α) (k : ℕ) :
    commonPrefixTails H V P Q k = commonPrefixTails H V Q P k := by
  ext A
  constructor
  · intro hA
    obtain ⟨hAV, hAc, hDisj, hPA, hQA⟩ := mem_common_prefix_tails.mp hA
    exact mem_common_prefix_tails.mpr
      ⟨hAV, hAc, by simpa [Finset.union_comm] using hDisj, hQA, hPA⟩
  · intro hA
    obtain ⟨hAV, hAc, hDisj, hQA, hPA⟩ := mem_common_prefix_tails.mp hA
    exact mem_common_prefix_tails.mpr
      ⟨hAV, hAc, by simpa [Finset.union_comm] using hDisj, hPA, hQA⟩

/-- A strong pair can be read with either root as the pinned prefix. -/
theorem actual_strong_partner_symm
    (H : Family α) (V P Q : Edge α) (k t : ℕ) (z : α)
    (hP : P ∈ V.powersetCard 2)
    (hStrong : ActualStrongPartner H V P Q 2 k t z) :
    ActualStrongPartner H V Q P 2 k t z := by
  have hCell := common_prefix_tails_comm H V P Q k
  refine ⟨hP, hStrong.2.1.symm, ?_, ?_⟩
  · rw [← hCell]
    exact hStrong.2.2.1
  · rw [← hCell]
    exact hStrong.2.2.2

/-- A fixed strong completion pair has a unique parent label. -/
theorem actual_strong_partner_center_unique
    (H : Family α) (V P Q : Edge α) (s k t : ℕ)
    {z z' : α}
    (hz : ActualStrongPartner H V P Q s k t z)
    (hz' : ActualStrongPartner H V P Q s k t z') :
    z = z' := by
  exact (hz.2.2.2.2 z' hz'.2.2.2.1).symm

/-- The IV.7 retained-tail guarantee, specialized to the actual rank-five
    parent pair link and to strong partners with one fixed center. -/
theorem retained_strong_bad_parent_partners_le
    (H : Family α) (V B R : Edge α) (t u q : ℕ) (z : α)
    (hR : R ∈ actualCoreLink H V B 2)
    (hLarge : u ≤ (actualCoreLink H V B 2).card)
    (hKeep : R ∉ cleanupTails H V B 2 u q
      (fun _ P T => ¬ ActualStrongPartner H V P T 2 3 t z)) :
    (badParentPartners H V B R
      (fun _ P T => ActualStrongPartner H V P T 2 3 t z)).card ≤ q := by
  classical
  have h := retained_tail_exception_degree_le H V B R 2 u q
    (fun _ P T => ¬ ActualStrongPartner H V P T 2 3 t z)
    hR hLarge hKeep
  simpa [actualBadPartnerDegree, badParentPartners,
    actual_core_link_two_eq_parent_pair_link] using h

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

/-- In the facet case every second retained completion gives a distinct
    intersecting pair root.  At least half of the shared-facet completions
    therefore occur as second roots, without a color or partner premise. -/
theorem facet_bad_incidence_second_roots_half
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V facetCenter tripleLabel) :
    (facetParents K i.1.2).card ≤
      2 * (facetWitnessSecondRoots K V i).card := by
  classical
  let E := i.1.1
  let A := i.1.2
  let a := i.2
  let B := facetWitnessCore i
  let R₀ := facetWitnessRoot i
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : E ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : A.card = 4 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hParts := (Finset.mem_filter.mp hi).2
  have hAE : A ⊆ E := hParts.1
  have hShared : A ∈ sharedFourShadow K := hParts.2.1
  have ha : a ∈ A := hParts.2.2.1
  have hParent : E ∈ facetParents K A :=
    Finset.mem_filter.mpr ⟨hE, hAE⟩
  let other := (facetParents K A).erase E
  have hMap : ∀ F ∈ other,
      F \ B ∈ facetWitnessSecondRoots K V i := by
    intro F hF
    have hFparent : F ∈ facetParents K A := Finset.mem_of_mem_erase hF
    have hFparts := Finset.mem_filter.mp hFparent
    have hFE : F ≠ E := Finset.ne_of_mem_erase hF
    have hPartner := shared_facet_second_parent_is_bad_partner
      (K := K) (H := K) (V := V) (A := A) (E := E) (F := F)
      (a := a) (Finset.Subset.rfl) hUniform hE hFparts.1
      hAcard hAE hFparts.2 ha hFE.symm hAmbient
      (fun _ R T => Disjoint R T) (by intros; assumption)
    have hBF : B ⊆ F := (Finset.erase_subset a A).trans hFparts.2
    have hRcard : (F \ B).card = 2 := by
      rw [Finset.card_sdiff_of_subset hBF, hUniform hFparts.1]
      have hBcard : B.card = 3 := by
        have herase := Finset.card_erase_add_one ha
        change (A.erase a).card = 3
        omega
      omega
    have hDisj : Disjoint (F \ B) B := by
      apply Finset.disjoint_left.mpr
      intro x hx hxB
      exact (Finset.mem_sdiff.mp hx).2 hxB
    have hEdge : B ∪ (F \ B) ∈ K := by
      rw [Finset.union_comm, Finset.sdiff_union_of_subset hBF]
      exact hFparts.1
    have hLink : F \ B ∈ parentPairLink K V B :=
      mem_parent_pair_link.mpr
        ⟨Finset.sdiff_subset.trans (hAmbient F hFparts.1),
          hRcard, hDisj, hEdge⟩
    exact Finset.mem_filter.mpr ⟨hLink, hPartner.2.2⟩
  have hInj : Set.InjOn (fun F : Edge α => F \ B) (other : Set (Edge α)) := by
    intro F hF G hG hEq
    have hFB : B ⊆ F :=
      (Finset.erase_subset a A).trans
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hF)).2
    have hGB : B ⊆ G :=
      (Finset.erase_subset a A).trans
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase hG)).2
    calc
      F = (F \ B) ∪ B := (Finset.sdiff_union_of_subset hFB).symm
      _ = (G \ B) ∪ B := congrArg (fun X : Edge α => X ∪ B) hEq
      _ = G := Finset.sdiff_union_of_subset hGB
  have hOtherLe : other.card ≤ (facetWitnessSecondRoots K V i).card :=
    Finset.card_le_card_of_injOn (fun F : Edge α => F \ B) hMap hInj
  have hErase : other.card + 1 = (facetParents K A).card :=
    Finset.card_erase_add_one hParent
  have hMany : 2 ≤ (facetParents K A).card :=
    (Finset.mem_filter.mp hShared).2
  change (facetParents K A).card ≤
    2 * (facetWitnessSecondRoots K V i).card
  omega

/-- The two distinct labels of a bad facet incidence both lie in its
    triple core.  This is the four-set pinned for the final codegree count. -/
theorem facet_bad_incidence_labels_in_core
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hFacetCenter : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V facetCenter tripleLabel) :
    facetCenter i.1.2 ∈ facetWitnessCore i ∧
      tripleLabel (facetWitnessCore i) ∈ facetWitnessCore i ∧
      facetCenter i.1.2 ≠ tripleLabel (facetWitnessCore i) := by
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : i.1.2.card = 4 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hParts := (Finset.mem_filter.mp hi).2
  have hAE : i.1.2 ⊆ i.1.1 := hParts.1
  have hShared : i.1.2 ∈ sharedFourShadow K := hParts.2.1
  have ha : i.2 ∈ i.1.2 := hParts.2.2.1
  have hNotCenter : i.2 ≠ facetCenter i.1.2 := hParts.2.2.2.1
  have hMismatch : tripleLabel (i.1.2.erase i.2) ≠
      facetCenter i.1.2 := hParts.2.2.2.2
  have hBcard : (facetWitnessCore i).card = 3 := by
    have herase := Finset.card_erase_add_one ha
    change (i.1.2.erase i.2).card = 3
    omega
  have hBE : facetWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans hAE
  refine ⟨?_, hTripleLabels (facetWitnessCore i)
    ⟨i.1.1, hE, hBE⟩ hBcard, ?_⟩
  · exact Finset.mem_erase.mpr
      ⟨hNotCenter.symm, hFacetCenter i.1.2 hShared⟩
  · exact hMismatch.symm

theorem facet_bad_incidence_core_eq_parent_sdiff_root
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V facetCenter tripleLabel) :
    facetWitnessCore i = i.1.1 \ facetWitnessRoot i := by
  have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hi).2.1
  have hBE : facetWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans hAE
  exact (Finset.sdiff_sdiff_eq_self hBE).symm

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

/-- Two actual retained-partner guarantees at a triple core leave at least
    half of its retained roots as common strong third roots. -/
theorem facet_third_roots_half_of_retained_partner_bounds
    (K H : Family α) (V : Edge α) (t q : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H)
    (i : (Edge α × Edge α) × α) (R₁ : Edge α)
    (hLarge : 4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hBad₀ : (badParentPartners H V (facetWitnessCore i)
      (facetWitnessRoot i)
      (fun B P T => ActualStrongPartner H V P T 2 3 t (tripleLabel B))).card ≤ q)
    (hBad₁ : (badParentPartners H V (facetWitnessCore i) R₁
      (fun B P T => ActualStrongPartner H V P T 2 3 t (tripleLabel B))).card ≤ q) :
    (parentPairLink K V (facetWitnessCore i)).card ≤
      2 * (facetWitnessThirdRoots H V t tripleLabel i R₁).card := by
  classical
  let B := facetWitnessCore i
  let R₀ := facetWitnessRoot i
  let L := parentPairLink K V B
  let strong₀ : Edge α → Prop := fun T =>
    ActualStrongPartner H V R₀ T 2 3 t (tripleLabel B)
  let strong₁ : Edge α → Prop := fun T =>
    ActualStrongPartner H V R₁ T 2 3 t (tripleLabel B)
  let bad₀ := L.filter fun T => ¬ strong₀ T
  let bad₁ := L.filter fun T => ¬ strong₁ T
  let both := L.filter fun T => strong₀ T ∧ strong₁ T
  have hLinkH : ∀ T ∈ L, T ∈ parentPairLink H V B := by
    intro T hT
    have hParts := mem_parent_pair_link.mp hT
    exact mem_parent_pair_link.mpr
      ⟨hParts.1, hParts.2.1, hParts.2.2.1, hKH hParts.2.2.2⟩
  have hBad₀Sub : bad₀ ⊆ badParentPartners H V B R₀
      (fun B P T => ActualStrongPartner H V P T 2 3 t (tripleLabel B)) := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    change T ∈ (parentPairLink H V B).filter (fun T => ¬ strong₀ T)
    exact Finset.mem_filter.mpr ⟨hLinkH T hParts.1, hParts.2⟩
  have hBad₁Sub : bad₁ ⊆ badParentPartners H V B R₁
      (fun B P T => ActualStrongPartner H V P T 2 3 t (tripleLabel B)) := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    change T ∈ (parentPairLink H V B).filter (fun T => ¬ strong₁ T)
    exact Finset.mem_filter.mpr ⟨hLinkH T hParts.1, hParts.2⟩
  have hBad₀Card : bad₀.card ≤ q :=
    (Finset.card_le_card hBad₀Sub).trans hBad₀
  have hBad₁Card : bad₁.card ≤ q :=
    (Finset.card_le_card hBad₁Sub).trans hBad₁
  have hCover : L ⊆ bad₀ ∪ bad₁ ∪ both := by
    intro T hT
    by_cases h₀ : strong₀ T
    · by_cases h₁ : strong₁ T
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hT, h₀, h₁⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hT, h₁⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hT, h₀⟩))
  have hCard : L.card ≤ bad₀.card + bad₁.card + both.card := by
    have hUnion := Finset.card_le_card hCover
    have hU₀ := Finset.card_union_le bad₀ bad₁
    have hU₁ := Finset.card_union_le (bad₀ ∪ bad₁) both
    omega
  have hBothSub : both ⊆ facetWitnessThirdRoots H V t tripleLabel i R₁ := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    have hStrong₀ : strong₀ T := hParts.2.1
    have hStrong₁ : strong₁ T := hParts.2.2
    have hDisj : Disjoint T (R₀ ∪ R₁) := by
      apply Finset.disjoint_left.mpr
      intro x hxT hxU
      rcases Finset.mem_union.mp hxU with hx₀ | hx₁
      · exact (Finset.disjoint_left.mp hStrong₀.2.1) hx₀ hxT
      · exact (Finset.disjoint_left.mp hStrong₁.2.1) hx₁ hxT
    change T ∈ (parentPairLink H V B).filter
      (fun T => Disjoint T (R₀ ∪ R₁) ∧ strong₀ T ∧ strong₁ T)
    exact Finset.mem_filter.mpr
      ⟨hLinkH T hParts.1, hDisj, hStrong₀, hStrong₁⟩
  have hBothCard := Finset.card_le_card hBothSub
  change 4 * q ≤ L.card at hLarge
  change L.card ≤ 2 * (facetWitnessThirdRoots H V t tripleLabel i R₁).card
  omega

/-- The second-root fiber above a fixed third root. -/
noncomputable def facetPinnedSecondRoots
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) (T : Edge α) : Family α := by
  classical
  exact (facetWitnessSecondRoots K V i).filter fun R₁ =>
    T ∈ facetWitnessThirdRoots H V t tripleLabel i R₁

/-- The pinned IV.7.2 bound applies to every fixed-third-root witness
    fiber.  The unique lower-core center is outside `T` because it occurs in
    a common tail disjoint from `T`. -/
theorem facet_pinned_second_roots_bound
    (K H : Family α) (V : Edge α) (t D₃ D₄ : ℕ)
    (tripleLabel : Edge α → α)
    (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (i : (Edge α × Edge α) × α) (T : Edge α) :
    t * (facetPinnedSecondRoots K H V t tripleLabel i T).card ≤
      D₃ * D₄ := by
  classical
  let F := facetPinnedSecondRoots K H V t tripleLabel i T
  by_cases hEmpty : F = ∅
  · change t * F.card ≤ D₃ * D₄
    simp [hEmpty]
  have hNonempty : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨R₁, hR₁⟩ := hNonempty
  have hThird : T ∈ facetWitnessThirdRoots H V t tripleLabel i R₁ :=
    (Finset.mem_filter.mp hR₁).2
  have hThirdParts := Finset.mem_filter.mp hThird
  have hTlink : T ∈ parentPairLink H V (facetWitnessCore i) :=
    hThirdParts.1
  have hTcard : T.card = 2 := (mem_parent_pair_link.mp hTlink).2.1
  let z := tripleLabel (facetWitnessCore i)
  have hStrong₀ : ActualStrongPartner H V (facetWitnessRoot i) T 2 3 t z :=
    hThirdParts.2.2.1
  have hzNotT : z ∉ T := by
    have hCellPos : 0 <
        (commonPrefixTails H V (facetWitnessRoot i) T 3).card := by
      have hThreshold := hStrong₀.2.2.1
      omega
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hCellPos
    have hzC : z ∈ C := hStrong₀.2.2.2.1 C hC
    have hDisjCT : Disjoint C T :=
      (Finset.disjoint_union_right.mp
        (mem_common_prefix_tails.mp hC).2.2.1).2
    intro hzT
    exact (Finset.disjoint_left.mp hDisjCT) hzC hzT
  have hSub : F ⊆ actualCenterPartners H V T 2 3 t z {i.2} := by
    intro R hR
    have hSecond : R ∈ facetWitnessSecondRoots K V i :=
      (Finset.mem_filter.mp hR).1
    have hInter : facetWitnessRoot i ∩ R = {i.2} :=
      (Finset.mem_filter.mp hSecond).2
    have haR : i.2 ∈ R := by
      have haInter : i.2 ∈ facetWitnessRoot i ∩ R := by
        rw [hInter]
        simp
      exact (Finset.mem_inter.mp haInter).2
    have hRlink : R ∈ parentPairLink K V (facetWitnessCore i) :=
      (Finset.mem_filter.mp hSecond).1
    have hRpow : R ∈ V.powersetCard 2 := by
      exact Finset.mem_powersetCard.mpr
        ⟨(mem_parent_pair_link.mp hRlink).1,
          (mem_parent_pair_link.mp hRlink).2.1⟩
    have hThirdR : T ∈ facetWitnessThirdRoots H V t tripleLabel i R :=
      (Finset.mem_filter.mp hR).2
    have hStrongR : ActualStrongPartner H V R T 2 3 t z :=
      (Finset.mem_filter.mp hThirdR).2.2.2
    have hSymm := actual_strong_partner_symm H V R T 3 t z hRpow hStrongR
    change R ∈ (V.powersetCard 2).filter
      (fun Q => ActualStrongPartner H V T Q 2 3 t z ∧ {i.2} ⊆ Q)
    exact Finset.mem_filter.mpr
      ⟨hRpow, hSymm, Finset.singleton_subset_iff.mpr haR⟩
  have hPinned := repeated_center_partner_bound_from_codegrees
    H V T 2 3 t z {i.2} 1 D₃ D₄
    hTcard hzNotT (by simp) hD₃ hD₄
  have hCard := Finset.card_le_card hSub
  exact (Nat.mul_le_mul_left t hCard).trans hPinned

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

/-- The full IV.9.2 witness relation also records the upper shared-facet
    color on the two singleton completion roots. -/
noncomputable def facetUpperStrongWitnesses
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter : Edge α → α) (tripleLabel : Edge α → α) := by
  classical
  exact (facetInheritanceWitnesses I K H V tLower tripleLabel).filter fun w =>
    ActualStrongPartner H V
      ((facetWitnessRoot w.1).erase w.1.2)
      (w.2.1.erase w.1.2) 1 4 tUpper
      (facetCenter w.1.1.2)

/-- IV.8's actual shared-facet color guarantee makes the additional upper
    strong-pair test automatic on all retained second roots. -/
theorem facet_upper_strong_witnesses_eq
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter : Edge α → α) (tripleLabel : Edge α → α)
    (hFacetStrong : ∀ i ∈ I,
      ∀ R₁ ∈ facetWitnessSecondRoots K V i,
        ActualStrongPartner H V
          ((facetWitnessRoot i).erase i.2) (R₁.erase i.2)
          1 4 tUpper (facetCenter i.1.2)) :
    facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel =
      facetInheritanceWitnesses I K H V tLower tripleLabel := by
  classical
  ext w
  constructor
  · intro hw
    exact (Finset.mem_filter.mp hw).1
  · intro hw
    have hi : w.1 ∈ I := (Finset.mem_sigma.mp hw).1
    have hR₁ : w.2.1 ∈ facetWitnessSecondRoots K V w.1 :=
      (Finset.mem_sigma.mp (Finset.mem_sigma.mp hw).2).1
    exact Finset.mem_filter.mpr
      ⟨hw, hFacetStrong w.1 hi w.2.1 hR₁⟩

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

/-- Data fixed before the two color and codegree counts in IV.9.3. -/
def facetWitnessPinnedKey
    (w : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) :
    (((Edge α × Edge α) × α) × Edge α) :=
  (((facetWitnessRoot w.1, w.2.2), w.1.2), w.2.1)

/-- Within one pinned-key fiber, mapping a witness to its parent edge is
    injective; the key already fixes the two roots and the deleted vertex. -/
theorem facet_upper_witness_parent_injective_on_key
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (key : (((Edge α × Edge α) × α) × Edge α)) :
    Set.InjOn (fun w : (_i : (Edge α × Edge α) × α) ×
        ((_R₁ : Edge α) × Edge α) => w.1.1.1)
      ((facetUpperStrongWitnesses I K H V tLower tUpper
        facetCenter tripleLabel).filter
          (fun w => facetWitnessPinnedKey w = key) :
        Set ((_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))) := by
  classical
  intro w hw w' hw' hE
  have hW : w ∈ facetInheritanceWitnesses I K H V tLower tripleLabel :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have hW' : w' ∈ facetInheritanceWitnesses I K H V tLower tripleLabel :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw').1).1
  have hKey : facetWitnessPinnedKey w = facetWitnessPinnedKey w' :=
    (Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hw').2.symm
  have hR₀ : facetWitnessRoot w.1 = facetWitnessRoot w'.1 :=
    congrArg (fun x => x.1.1.1) hKey
  have hT : w.2.2 = w'.2.2 := congrArg (fun x => x.1.1.2) hKey
  have ha : w.1.2 = w'.1.2 := congrArg (fun x => x.1.2) hKey
  have hR₁ : w.2.1 = w'.2.1 := congrArg (fun x => x.2) hKey
  have hBad : w.1 ∈ facetBadIncidences K V facetCenter tripleLabel :=
    hI (Finset.mem_sigma.mp hW).1
  have hBad' : w'.1 ∈ facetBadIncidences K V facetCenter tripleLabel :=
    hI (Finset.mem_sigma.mp hW').1
  have hB : facetWitnessCore w.1 = facetWitnessCore w'.1 := by
    have hE' : w.1.1.1 = w'.1.1.1 := hE
    calc
      facetWitnessCore w.1 = w.1.1.1 \ facetWitnessRoot w.1 :=
        facet_bad_incidence_core_eq_parent_sdiff_root K V
          facetCenter tripleLabel hBad
      _ = w'.1.1.1 \ facetWitnessRoot w'.1 := by rw [hE', hR₀]
      _ = facetWitnessCore w'.1 :=
        (facet_bad_incidence_core_eq_parent_sdiff_root K V
          facetCenter tripleLabel hBad').symm
  have hTuple : facetWitnessTuple w = facetWitnessTuple w' := by
    apply Prod.ext
    · apply Prod.ext
      · exact Prod.ext hB hR₀
      · exact Prod.ext hR₁ hT
    · exact ha
  exact facet_witness_tuple_injective I K H V tLower
    facetCenter tripleLabel hI hW hW' hTuple

/-- Fixing `(R₀,T,a,R₁)` fixes both lower and upper labels. -/
theorem facet_upper_witness_labels_eq_on_key
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    {w w' : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α)}
    (hw : w ∈ facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel)
    (hw' : w' ∈ facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel)
    (hKey : facetWitnessPinnedKey w = facetWitnessPinnedKey w') :
    tripleLabel (facetWitnessCore w.1) =
      tripleLabel (facetWitnessCore w'.1) ∧
    facetCenter w.1.1.2 = facetCenter w'.1.1.2 := by
  classical
  have hR₀ : facetWitnessRoot w.1 = facetWitnessRoot w'.1 :=
    congrArg (fun x => x.1.1.1) hKey
  have hT : w.2.2 = w'.2.2 := congrArg (fun x => x.1.1.2) hKey
  have ha : w.1.2 = w'.1.2 := congrArg (fun x => x.1.2) hKey
  have hR₁ : w.2.1 = w'.2.1 := congrArg (fun x => x.2) hKey
  have hBase := (Finset.mem_filter.mp hw).1
  have hBase' := (Finset.mem_filter.mp hw').1
  have hTmem := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).2
  have hTmem' := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase').2).2
  have hStrong := (Finset.mem_filter.mp hTmem).2.2.1
  have hStrong' := (Finset.mem_filter.mp hTmem').2.2.1
  have hUpper := (Finset.mem_filter.mp hw).2
  have hUpper' := (Finset.mem_filter.mp hw').2
  constructor
  · have hStrong'' : ActualStrongPartner H V
        (facetWitnessRoot w.1) w.2.2 2 3 tLower
        (tripleLabel (facetWitnessCore w'.1)) := by
      simpa only [hR₀, hT] using hStrong'
    exact actual_strong_partner_center_unique H V
      (facetWitnessRoot w.1) w.2.2 2 3 tLower hStrong hStrong''
  · have hUpper'' : ActualStrongPartner H V
        ((facetWitnessRoot w.1).erase w.1.2)
        (w.2.1.erase w.1.2) 1 4 tUpper
        (facetCenter w'.1.1.2) := by
      simpa only [hR₀, hR₁, ha] using hUpper'
    exact actual_strong_partner_center_unique H V
      ((facetWitnessRoot w.1).erase w.1.2)
      (w.2.1.erase w.1.2) 1 4 tUpper hUpper hUpper''

/-- Once the pinned key fixes both colors, all remaining triple cores map
    injectively into parents through one fixed four-set. -/
theorem facet_upper_witness_key_fiber_le_four_codegree
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hFacetCenter : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (key : (((Edge α × Edge α) × α) × Edge α)) :
    ((facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel).filter
        (fun w => facetWitnessPinnedKey w = key)).card ≤ D₄ := by
  classical
  let F := (facetUpperStrongWitnesses I K H V tLower tUpper
    facetCenter tripleLabel).filter
      (fun w => facetWitnessPinnedKey w = key)
  change F.card ≤ D₄
  by_cases hEmpty : F = ∅
  · simp [hEmpty]
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hUpper₀ : w₀ ∈ facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel := (Finset.mem_filter.mp hw₀).1
  have hBad₀ : w₀.1 ∈ facetBadIncidences K V facetCenter tripleLabel := by
    have hBase := (Finset.mem_filter.mp hUpper₀).1
    exact hI (Finset.mem_sigma.mp hBase).1
  let B₀ := facetWitnessCore w₀.1
  let R₀ := facetWitnessRoot w₀.1
  let zA := facetCenter w₀.1.1.2
  let zB := tripleLabel B₀
  let S : Edge α := R₀ ∪ {zA, zB}
  have hLabels₀ := facet_bad_incidence_labels_in_core K V
    facetCenter tripleLabel hFacetCenter hTripleLabels hBad₀
  have hSource₀ := (Finset.mem_filter.mp hBad₀).1
  have hE₀ : w₀.1.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource₀).1).1
  have hAcard₀ : w₀.1.1.2.card = 4 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource₀).1).2).2
  have ha₀ : w₀.1.2 ∈ w₀.1.1.2 :=
    (Finset.mem_filter.mp hBad₀).2.2.2.1
  have hBcard₀ : B₀.card = 3 := by
    have herase := Finset.card_erase_add_one ha₀
    change (w₀.1.1.2.erase w₀.1.2).card = 3
    omega
  have hBE₀ : B₀ ⊆ w₀.1.1.1 :=
    (Finset.erase_subset w₀.1.2 w₀.1.1.2).trans
      (Finset.mem_filter.mp hBad₀).2.1
  have hRcard₀ : R₀.card = 2 := by
    change (w₀.1.1.1 \ B₀).card = 2
    rw [Finset.card_sdiff_of_subset hBE₀, hUniform hE₀]
    omega
  have hRdisjB : Disjoint R₀ B₀ := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxB
    exact (Finset.mem_sdiff.mp hxR).2 hxB
  have hPairDisj : Disjoint R₀ ({zA, zB} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
    rcases hxPair with rfl | rfl
    · exact (Finset.disjoint_left.mp hRdisjB) hxR hLabels₀.1
    · exact (Finset.disjoint_left.mp hRdisjB) hxR hLabels₀.2.1
  have hScard : S.card = 4 := by
    rw [Finset.card_union_of_disjoint hPairDisj]
    rw [Finset.card_pair hLabels₀.2.2, hRcard₀]
  have hMap : ∀ w ∈ F, w.1.1.1 ∈ H.filter (fun E => S ⊆ E) := by
    intro w hw
    have hUpper : w ∈ facetUpperStrongWitnesses I K H V tLower tUpper
        facetCenter tripleLabel := (Finset.mem_filter.mp hw).1
    have hBase := (Finset.mem_filter.mp hUpper).1
    have hBad : w.1 ∈ facetBadIncidences K V facetCenter tripleLabel :=
      hI (Finset.mem_sigma.mp hBase).1
    have hKeyEq : facetWitnessPinnedKey w₀ = facetWitnessPinnedKey w :=
      (Finset.mem_filter.mp hw₀).2.trans (Finset.mem_filter.mp hw).2.symm
    have hR₀w : R₀ = facetWitnessRoot w.1 :=
      congrArg (fun x => x.1.1.1) hKeyEq
    have hColors := facet_upper_witness_labels_eq_on_key I K H V
      tLower tUpper facetCenter tripleLabel hUpper₀ hUpper hKeyEq
    have hLabels := facet_bad_incidence_labels_in_core K V
      facetCenter tripleLabel hFacetCenter hTripleLabels hBad
    have hBE : facetWitnessCore w.1 ⊆ w.1.1.1 :=
      (Finset.erase_subset w.1.2 w.1.1.2).trans
        (Finset.mem_filter.mp hBad).2.1
    have hRE : facetWitnessRoot w.1 ⊆ w.1.1.1 := Finset.sdiff_subset
    have hSource := (Finset.mem_filter.mp hBad).1
    have hE : w.1.1.1 ∈ K :=
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
    have hzAw : zA ∈ facetWitnessCore w.1 := by
      change facetCenter w₀.1.1.2 ∈ facetWitnessCore w.1
      rw [hColors.2]
      exact hLabels.1
    have hzBw : zB ∈ facetWitnessCore w.1 := by
      change tripleLabel (facetWitnessCore w₀.1) ∈ facetWitnessCore w.1
      rw [hColors.1]
      exact hLabels.2.1
    apply Finset.mem_filter.mpr
    refine ⟨hKH hE, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxR | hxPair
    · exact hRE (hR₀w ▸ hxR)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with rfl | rfl
      · exact hBE hzAw
      · exact hBE hzBw
  have hInj := facet_upper_witness_parent_injective_on_key I K H V
    tLower tUpper facetCenter tripleLabel hI key
  have hCount := Finset.card_le_card_of_injOn
    (fun w : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α) => w.1.1.1) hMap hInj
  exact hCount.trans (hD₄ S hScard)

/-- The first three coordinates used by the pinned IV.7.2 count. -/
def facetWitnessTripleKey
    (w : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) :
    (Edge α × Edge α) × α :=
  ((facetWitnessRoot w.1, w.2.2), w.1.2)

/-- For fixed `(R₀,T,a)`, the lower center is unique and the possible
    second roots obey the actual pinned repeated-center bound. -/
theorem facet_upper_witness_triple_fiber_pinned_cap
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (key : (Edge α × Edge α) × α) :
    tLower * (((facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel).filter
        (fun w => facetWitnessTripleKey w = key)).image
          (fun w => w.2.1)).card ≤ D₃ * D₄ := by
  classical
  let F := (facetUpperStrongWitnesses I K H V tLower tUpper
    facetCenter tripleLabel).filter
      (fun w => facetWitnessTripleKey w = key)
  change tLower * (F.image (fun w => w.2.1)).card ≤ D₃ * D₄
  by_cases hEmpty : F = ∅
  · simp [hEmpty]
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hBase₀ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw₀).1).1
  have hThird₀ := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase₀).2).2
  have hThirdParts₀ := Finset.mem_filter.mp hThird₀
  have hTcard : w₀.2.2.card = 2 :=
    (mem_parent_pair_link.mp hThirdParts₀.1).2.1
  let z := tripleLabel (facetWitnessCore w₀.1)
  have hStrong₀ : ActualStrongPartner H V
      (facetWitnessRoot w₀.1) w₀.2.2 2 3 tLower z :=
    hThirdParts₀.2.2.1
  have hzNotT : z ∉ w₀.2.2 := by
    have hCellPos : 0 <
        (commonPrefixTails H V (facetWitnessRoot w₀.1) w₀.2.2 3).card := by
      have hThreshold := hStrong₀.2.2.1
      omega
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hCellPos
    have hzC : z ∈ C := hStrong₀.2.2.2.1 C hC
    have hDisjCT : Disjoint C w₀.2.2 :=
      (Finset.disjoint_union_right.mp
        (mem_common_prefix_tails.mp hC).2.2.1).2
    intro hzT
    exact (Finset.disjoint_left.mp hDisjCT) hzC hzT
  have hSub : F.image (fun w => w.2.1) ⊆
      actualCenterPartners H V w₀.2.2 2 3 tLower z {w₀.1.2} := by
    intro R₁ hR₁
    obtain ⟨w, hw, hRw⟩ := Finset.mem_image.mp hR₁
    have hBase := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
    have hSecond := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).1
    have hThird := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).2
    have hKey : facetWitnessTripleKey w₀ = facetWitnessTripleKey w :=
      (Finset.mem_filter.mp hw₀).2.trans (Finset.mem_filter.mp hw).2.symm
    have hR₀ : facetWitnessRoot w₀.1 = facetWitnessRoot w.1 :=
      congrArg (fun x => x.1.1) hKey
    have hT : w₀.2.2 = w.2.2 := congrArg (fun x => x.1.2) hKey
    have ha : w₀.1.2 = w.1.2 := congrArg (fun x => x.2) hKey
    have hStrong₀w := (Finset.mem_filter.mp hThird).2.2.1
    have hStrong₀w' : ActualStrongPartner H V
        (facetWitnessRoot w₀.1) w₀.2.2 2 3 tLower
        (tripleLabel (facetWitnessCore w.1)) := by
      simpa only [hR₀, hT] using hStrong₀w
    have hzEq : z = tripleLabel (facetWitnessCore w.1) :=
      actual_strong_partner_center_unique H V
        (facetWitnessRoot w₀.1) w₀.2.2 2 3 tLower
        hStrong₀ hStrong₀w'
    have hRlink := (Finset.mem_filter.mp hSecond).1
    have hRpow : w.2.1 ∈ V.powersetCard 2 :=
      Finset.mem_powersetCard.mpr
        ⟨(mem_parent_pair_link.mp hRlink).1,
          (mem_parent_pair_link.mp hRlink).2.1⟩
    have hInter := (Finset.mem_filter.mp hSecond).2
    have haR : w.1.2 ∈ w.2.1 := by
      have haInter : w.1.2 ∈ facetWitnessRoot w.1 ∩ w.2.1 := by
        rw [hInter]
        simp
      exact (Finset.mem_inter.mp haInter).2
    have hStrong₁w := (Finset.mem_filter.mp hThird).2.2.2
    have hStrong₁w' : ActualStrongPartner H V
        w₀.2.2 w.2.1 2 3 tLower z := by
      have hSymm := actual_strong_partner_symm H V
        w.2.1 w.2.2 3 tLower
        (tripleLabel (facetWitnessCore w.1)) hRpow hStrong₁w
      simpa only [← hT, ← hzEq] using hSymm
    change R₁ ∈ (V.powersetCard 2).filter
      (fun Q => ActualStrongPartner H V w₀.2.2 Q 2 3 tLower z ∧
        {w₀.1.2} ⊆ Q)
    have hR₁Eq : w.2.1 = R₁ := hRw
    subst R₁
    exact Finset.mem_filter.mpr
      ⟨hRpow, hStrong₁w', Finset.singleton_subset_iff.mpr (ha ▸ haR)⟩
  have hPinned := repeated_center_partner_bound_from_codegrees
    H V w₀.2.2 2 3 tLower z {w₀.1.2} 1 D₃ D₄
    hTcard hzNotT (by simp) hD₃ hD₄
  exact (Nat.mul_le_mul_left tLower (Finset.card_le_card hSub)).trans hPinned

/-- The rank-five IV.9.3 bound for one fixed `(R₀,T,a)` key: the pinned
    theorem bounds its possible `R₁`, and the four-codegree bounds the
    remaining bad triple cores for each `R₁`. -/
theorem facet_upper_witness_triple_fiber_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hFacetCenter : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (key : (Edge α × Edge α) × α) :
    tLower * ((facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel).filter
        (fun w => facetWitnessTripleKey w = key)).card ≤
      D₃ * D₄ * D₄ := by
  classical
  let F := (facetUpperStrongWitnesses I K H V tLower tUpper
    facetCenter tripleLabel).filter
      (fun w => facetWitnessTripleKey w = key)
  have hOne (R₁ : Edge α) :
      (F.filter fun w => w.2.1 = R₁).card ≤ D₄ := by
    have hEq : (F.filter fun w => w.2.1 = R₁) =
        (facetUpperStrongWitnesses I K H V tLower tUpper
          facetCenter tripleLabel).filter
          (fun w => facetWitnessPinnedKey w = (key, R₁)) := by
      ext w
      simp only [F, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hw, hKey⟩, hR⟩
        exact ⟨hw, by simp [facetWitnessPinnedKey,
          facetWitnessTripleKey, ← hKey, ← hR]⟩
      · rintro ⟨hw, hKey⟩
        have hTriple : facetWitnessTripleKey w = key :=
          congrArg Prod.fst hKey
        have hR : w.2.1 = R₁ := congrArg Prod.snd hKey
        exact ⟨⟨hw, hTriple⟩, hR⟩
    rw [hEq]
    exact facet_upper_witness_key_fiber_le_four_codegree
      I K H V tLower tUpper D₄ facetCenter tripleLabel
      hI hKH hUniform hFacetCenter hTripleLabels hD₄ (key, R₁)
  have hCount := Finset.card_eq_sum_card_fiberwise
    (f := fun w : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α) => w.2.1)
    (s := F) (t := F.image (fun w => w.2.1))
    (fun w hw => Finset.mem_image_of_mem _ hw)
  have hFiber : F.card ≤ (F.image (fun w => w.2.1)).card * D₄ := by
    rw [hCount]
    calc
      (∑ R₁ ∈ F.image (fun w => w.2.1),
        (F.filter fun w => w.2.1 = R₁).card) ≤
          ∑ _R₁ ∈ F.image (fun w => w.2.1), D₄ :=
        Finset.sum_le_sum (fun R₁ hR₁ => hOne R₁)
      _ = (F.image (fun w => w.2.1)).card * D₄ := by simp
  have hPinned := facet_upper_witness_triple_fiber_pinned_cap
    I K H V tLower tUpper D₃ D₄ facetCenter tripleLabel
    ht hD₃ hD₄ key
  change tLower * F.card ≤ D₃ * D₄ * D₄
  have hScaled := Nat.mul_le_mul_left tLower hFiber
  nlinarith [Nat.mul_le_mul_right D₄ hPinned]

/-- Candidate `(R₀,T,a)` keys: both roots are pairs in the ambient set and
    the deleted vertex belongs to the first root. -/
def facetWitnessTripleKeys (V : Edge α) :
    Finset ((Edge α × Edge α) × α) :=
  ((V.powersetCard 2) ×ˢ (V.powersetCard 2)).biUnion fun p =>
    p.1.image fun a => (p, a)

theorem facet_witness_triple_keys_card_le
    (V : Edge α) :
    (facetWitnessTripleKeys V).card ≤
      2 * (V.powersetCard 2).card ^ 2 := by
  classical
  let P := V.powersetCard 2
  calc
    (facetWitnessTripleKeys V).card ≤
        ∑ p ∈ P ×ˢ P, (p.1.image fun a => (p, a)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P ×ˢ P, p.1.card := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_image_le
    _ = ∑ _p ∈ P ×ˢ P, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    _ = 2 * P.card ^ 2 := by
      simp [pow_two, mul_comm]

/-- Every actual upper-strong witness has an admissible pinned key. -/
theorem facet_upper_witness_key_mem
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    {w : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α)}
    (hw : w ∈ facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel) :
    facetWitnessTripleKey w ∈ facetWitnessTripleKeys V := by
  classical
  have hBase := (Finset.mem_filter.mp hw).1
  have hBad : w.1 ∈ facetBadIncidences K V facetCenter tripleLabel :=
    hI (Finset.mem_sigma.mp hBase).1
  have hSource := (Finset.mem_filter.mp hBad).1
  have hE : w.1.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : w.1.1.2.card = 4 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hParts := (Finset.mem_filter.mp hBad).2
  have hAE : w.1.1.2 ⊆ w.1.1.1 := hParts.1
  have ha : w.1.2 ∈ w.1.1.2 := hParts.2.2.1
  have hBcard : (facetWitnessCore w.1).card = 3 := by
    have herase := Finset.card_erase_add_one ha
    change (w.1.1.2.erase w.1.2).card = 3
    omega
  have hBE : facetWitnessCore w.1 ⊆ w.1.1.1 :=
    (Finset.erase_subset w.1.2 w.1.1.2).trans hAE
  have hRcard : (facetWitnessRoot w.1).card = 2 := by
    change (w.1.1.1 \ facetWitnessCore w.1).card = 2
    rw [Finset.card_sdiff_of_subset hBE, hUniform hE]
    omega
  have hRpow : facetWitnessRoot w.1 ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr
      ⟨Finset.sdiff_subset.trans (hAmbient w.1.1.1 hE), hRcard⟩
  have hTmem := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).2
  have hTlink := (Finset.mem_filter.mp hTmem).1
  have hTparts := mem_parent_pair_link.mp hTlink
  have hTpow : w.2.2 ∈ V.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hTparts.1, hTparts.2.1⟩
  have haNotB : w.1.2 ∉ facetWitnessCore w.1 := by
    intro haB
    exact (Finset.mem_erase.mp haB).1 rfl
  have haR : w.1.2 ∈ facetWitnessRoot w.1 :=
    Finset.mem_sdiff.mpr ⟨hAE ha, haNotB⟩
  exact Finset.mem_biUnion.mpr
    ⟨(facetWitnessRoot w.1, w.2.2),
      Finset.mem_product.mpr ⟨hRpow, hTpow⟩,
      Finset.mem_image.mpr ⟨w.1.2, haR, rfl⟩⟩

/-- The rank-five facet witness upper count in the scale of IV.9.3.  It
    has no factor involving the number of bad incidences. -/
theorem facet_upper_strong_witness_global_pinned_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hFacetCenter : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tLower * (facetUpperStrongWitnesses I K H V tLower tUpper
      facetCenter tripleLabel).card ≤
        2 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by
  classical
  let W := facetUpperStrongWitnesses I K H V tLower tUpper
    facetCenter tripleLabel
  let Keys := facetWitnessTripleKeys V
  have hMap : ∀ w ∈ W, facetWitnessTripleKey w ∈ Keys := by
    intro w hw
    exact facet_upper_witness_key_mem I K H V tLower tUpper
      facetCenter tripleLabel hI hUniform hAmbient hw
  have hCount := Finset.card_eq_sum_card_fiberwise
    (f := facetWitnessTripleKey) (s := W) (t := Keys) hMap
  have hFiber : ∀ key ∈ Keys,
      tLower * (W.filter fun w => facetWitnessTripleKey w = key).card ≤
        D₃ * D₄ * D₄ := by
    intro key hkey
    exact facet_upper_witness_triple_fiber_bound I K H V
      tLower tUpper D₃ D₄ facetCenter tripleLabel hI hKH hUniform
      hFacetCenter hTripleLabels ht hD₃ hD₄ key
  have hKeys := facet_witness_triple_keys_card_le V
  calc
    tLower * W.card =
        ∑ key ∈ Keys,
          tLower * (W.filter fun w => facetWitnessTripleKey w = key).card := by
      rw [hCount, Finset.mul_sum]
    _ ≤ ∑ _key ∈ Keys, D₃ * D₄ * D₄ :=
      Finset.sum_le_sum hFiber
    _ = Keys.card * (D₃ * D₄ * D₄) := by simp
    _ ≤ (2 * (V.powersetCard 2).card ^ 2) *
          (D₃ * D₄ * D₄) := Nat.mul_le_mul_right _ hKeys
    _ = 2 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by ring

/-- Reindex one bad incidence's witnesses by the third root. -/
theorem facet_witnesses_for_card_eq_pinned_fiber_sum
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) :
    (facetWitnessesFor K H V t tripleLabel i).card =
      ∑ T ∈ V.powersetCard 2,
        (facetPinnedSecondRoots K H V t tripleLabel i T).card := by
  classical
  let W := facetWitnessesFor K H V t tripleLabel i
  have hMap : ∀ w ∈ W, w.2 ∈ V.powersetCard 2 := by
    intro w hw
    have hThird := (Finset.mem_sigma.mp hw).2
    have hTlink := (Finset.mem_filter.mp hThird).1
    have hParts := mem_parent_pair_link.mp hTlink
    exact Finset.mem_powersetCard.mpr ⟨hParts.1, hParts.2.1⟩
  have hFiber (T : Edge α) :
      (W.filter fun w => w.2 = T).card =
        (facetPinnedSecondRoots K H V t tripleLabel i T).card := by
    have hEq : (W.filter fun w => w.2 = T) =
        (facetPinnedSecondRoots K H V t tripleLabel i T).image
          (fun R₁ => (⟨R₁, T⟩ : (_R₁ : Edge α) × Edge α)) := by
      ext ⟨R₁, U⟩
      simp only [W, facetWitnessesFor, facetPinnedSecondRoots,
        Finset.mem_filter, Finset.mem_image, Finset.mem_sigma]
      constructor
      · rintro ⟨⟨hR₁, hU⟩, hUT⟩
        refine ⟨R₁, ?_, ?_⟩
        · exact ⟨hR₁, hUT ▸ hU⟩
        · cases hUT
          rfl
      · rintro ⟨R, hR, hEq⟩
        cases hEq
        exact ⟨hR, rfl⟩
    rw [hEq, Finset.card_image_of_injective]
    intro R S hRS
    exact congrArg Sigma.fst hRS
  have hCount := Finset.card_eq_sum_card_fiberwise
    (f := fun w : (_R₁ : Edge α) × Edge α => w.2)
    (s := W) (t := V.powersetCard 2) hMap
  simpa only [hFiber] using hCount

/-- A direct pinned upper bound for the complete witness relation.  It
    counts the fixed-third-root fibers with IV.7.2, before the stronger
    reindexing by `(R₀,T,a)` used in IV.9.3. -/
theorem facet_inheritance_witnesses_pinned_upper_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t D₃ D₄ : ℕ)
    (tripleLabel : Edge α → α)
    (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    t * (facetInheritanceWitnesses I K H V t tripleLabel).card ≤
      I.card * (V.powersetCard 2).card * (D₃ * D₄) := by
  classical
  have hOne : ∀ i ∈ I,
      t * (facetWitnessesFor K H V t tripleLabel i).card ≤
        (V.powersetCard 2).card * (D₃ * D₄) := by
    intro i hi
    rw [facet_witnesses_for_card_eq_pinned_fiber_sum]
    calc
      t * (∑ T ∈ V.powersetCard 2,
          (facetPinnedSecondRoots K H V t tripleLabel i T).card) =
          ∑ T ∈ V.powersetCard 2,
            t * (facetPinnedSecondRoots K H V t tripleLabel i T).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _T ∈ V.powersetCard 2, D₃ * D₄ := by
        apply Finset.sum_le_sum
        intro T hT
        exact facet_pinned_second_roots_bound K H V t D₃ D₄
          tripleLabel ht hD₃ hD₄ i T
      _ = (V.powersetCard 2).card * (D₃ * D₄) := by simp
  simp only [facetInheritanceWitnesses, Finset.card_sigma]
  calc
    t * (∑ i ∈ I, (facetWitnessesFor K H V t tripleLabel i).card) =
        ∑ i ∈ I, t * (facetWitnessesFor K H V t tripleLabel i).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ I, (V.powersetCard 2).card * (D₃ * D₄) :=
      Finset.sum_le_sum hOne
    _ = I.card * (V.powersetCard 2).card * (D₃ * D₄) := by
      simp [mul_assoc]

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

/-- The facet witness lower count using the actual IV.7 cleanup condition:
    all first and second roots of retained bad incidences survive cleanup at
    their triple core.  The only numeric inputs are the retained degree and
    the cleanup exception threshold. -/
theorem facet_inheritance_weighted_witness_lower_bound_of_retention
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t u q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hDegree : ∀ i ∈ I,
      u ≤ (actualCoreLink H V (facetWitnessCore i) 2).card ∧
      4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hKeep : ∀ i ∈ I,
      ∀ R ∈ insert (facetWitnessRoot i) (facetWitnessSecondRoots K V i),
        R ∈ actualCoreLink H V (facetWitnessCore i) 2 ∧
        R ∉ cleanupTails H V (facetWitnessCore i) 2 u q
          (fun _ P T => ¬ ActualStrongPartner H V P T 2 3 t
            (tripleLabel (facetWitnessCore i)))) :
    (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      4 * (facetInheritanceWitnesses I K H V t tripleLabel).card := by
  apply facet_inheritance_weighted_witness_lower_bound I K H V t tripleLabel
  · intro i hi
    exact facet_bad_incidence_second_roots_half K V facetCenter tripleLabel
      hUniform hAmbient (hI hi)
  · intro i hi R₁ hR₁
    have hD := hDegree i hi
    have hKeep₀ := hKeep i hi (facetWitnessRoot i)
      (Finset.mem_insert_self ..)
    have hKeep₁ := hKeep i hi R₁
      (Finset.mem_insert_of_mem hR₁)
    have hBad₀ := retained_strong_bad_parent_partners_le
      H V (facetWitnessCore i) (facetWitnessRoot i)
      t u q (tripleLabel (facetWitnessCore i))
      hKeep₀.1 hD.1 hKeep₀.2
    have hBad₁ := retained_strong_bad_parent_partners_le
      H V (facetWitnessCore i) R₁
      t u q (tripleLabel (facetWitnessCore i))
      hKeep₁.1 hD.1 hKeep₁.2
    exact facet_third_roots_half_of_retained_partner_bounds
      K H V t q tripleLabel hKH i R₁ hD.2 hBad₀ hBad₁

/-- The complete finite rank-five facet case of IV.9.3.  IV.7 supplies the
    retained degree and good-partner bounds; IV.8 supplies the upper strong
    color on each shared facet.  The right side is the manuscript's pinned
    witness budget with `s = 2` and `k = 3`. -/
theorem facet_inheritance_weighted_incidence_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α)
    (tLower tUpper u q D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hFacetCenter : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (hFacetStrong : ∀ i ∈ I,
      ∀ R₁ ∈ facetWitnessSecondRoots K V i,
        ActualStrongPartner H V
          ((facetWitnessRoot i).erase i.2) (R₁.erase i.2)
          1 4 tUpper (facetCenter i.1.2))
    (hDegree : ∀ i ∈ I,
      u ≤ (actualCoreLink H V (facetWitnessCore i) 2).card ∧
      4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hKeep : ∀ i ∈ I,
      ∀ R ∈ insert (facetWitnessRoot i) (facetWitnessSecondRoots K V i),
        R ∈ actualCoreLink H V (facetWitnessCore i) 2 ∧
        R ∉ cleanupTails H V (facetWitnessCore i) 2 u q
          (fun _ P T => ¬ ActualStrongPartner H V P T 2 3 tLower
            (tripleLabel (facetWitnessCore i))))
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tLower * (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by
  have hLower := facet_inheritance_weighted_witness_lower_bound_of_retention
    I K H V tLower u q facetCenter tripleLabel
    hI hKH hUniform hAmbient hDegree hKeep
  have hUpper := facet_upper_strong_witness_global_pinned_bound
    I K H V tLower tUpper D₃ D₄ facetCenter tripleLabel
    hI hKH hUniform hAmbient hFacetCenter hTripleLabels
    ht hD₃ hD₄
  have hEq := facet_upper_strong_witnesses_eq I K H V
    tLower tUpper facetCenter tripleLabel hFacetStrong
  rw [hEq] at hUpper
  calc
    tLower * (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
        tLower * (4 *
          (facetInheritanceWitnesses I K H V tLower tripleLabel).card) :=
      Nat.mul_le_mul_left _ hLower
    _ = 4 * (tLower *
          (facetInheritanceWitnesses I K H V tLower tripleLabel).card) := by ring
    _ ≤ 4 * (2 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) :=
      Nat.mul_le_mul_left _ hUpper
    _ = 8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by ring

/-- Convert the weighted IV.9.3 count into the number of high-retention bad
    incidences once the two actual core degrees have uniform lower bounds. -/
theorem facet_high_retention_incidence_card_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K : Family α) (V : Edge α)
    (t L₄ L₃ D₃ D₄ : ℕ)
    (hA : ∀ i ∈ I, L₄ ≤ (facetParents K i.1.2).card)
    (hB : ∀ i ∈ I,
      L₃ ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hWeighted : t * (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) :
    t * (L₄ * L₃ * I.card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by
  have hSum : L₄ * L₃ * I.card ≤
      ∑ i ∈ I,
        (facetParents K i.1.2).card *
          (parentPairLink K V (facetWitnessCore i)).card := by
    calc
      L₄ * L₃ * I.card = ∑ _i ∈ I, L₄ * L₃ := by
        simp [mul_comm, mul_left_comm]
      _ ≤ ∑ i ∈ I,
          (facetParents K i.1.2).card *
            (parentPairLink K V (facetWitnessCore i)).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.mul_le_mul (hA i hi) (hB i hi)
  exact (Nat.mul_le_mul_left t hSum).trans hWeighted

end JSP523.Rank5
