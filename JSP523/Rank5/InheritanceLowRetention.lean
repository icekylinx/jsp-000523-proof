import JSP523.Rank5.InheritanceWitness

/-!
# Low-retention facet inheritance incidences

The finite rank-five form of IV.9.1 charges bad incidences whose four-face or
triple core has low retention to the corresponding parent-degree sums.  The
threshold is represented by a rational comparison `Q d_K < P d_H` to keep
all counting integral.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- A retained pair-link root survives the triple-core cleanup whenever the
    retained family avoids all edges removed at that core. -/
theorem retained_pair_root_survives_multilevel_cleanup
    (K H : Family α) (V : Edge α) (C : Family α)
    (u q : ℕ) (bad : Edge α → Edge α → Edge α → Prop)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (multilevelDeletedEdges H V C 2 u q bad))
    {B R : Edge α} (hBC : B ∈ C)
    (hR : R ∈ parentPairLink K V B) :
    R ∈ actualCoreLink H V B 2 ∧
      R ∉ cleanupTails H V B 2 u q bad := by
  classical
  have hParts := mem_parent_pair_link.mp hR
  have hLinkH : R ∈ actualCoreLink H V B 2 :=
    mem_actual_core_link.mpr
      ⟨hParts.1, hParts.2.1, hParts.2.2.1, hKH hParts.2.2.2⟩
  refine ⟨hLinkH, ?_⟩
  intro hTail
  have hDeleted : B ∪ R ∈ multilevelDeletedEdges H V C 2 u q bad := by
    unfold multilevelDeletedEdges
    exact Finset.mem_biUnion.mpr
      ⟨B, hBC, Finset.mem_image.mpr ⟨R, hTail, rfl⟩⟩
  exact (Finset.disjoint_left.mp hSurvive) hParts.2.2.2 hDeleted

/-- At a triple core, actual pair roots and parent edges are in bijection. -/
theorem triple_parent_pair_link_card_eq_codegree
    (K : Family α) (V B : Edge α)
    (hUniform : Uniform 5 K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hBcard : B.card = 3) :
    (parentPairLink K V B).card =
      (K.filter fun E => B ⊆ E).card := by
  classical
  let parents := K.filter fun E => B ⊆ E
  have hEq : parentPairLink K V B = parents.image (fun E => E \ B) := by
    ext R
    constructor
    · intro hR
      have hParts := mem_parent_pair_link.mp hR
      have hParent : B ∪ R ∈ parents :=
        Finset.mem_filter.mpr ⟨hParts.2.2.2, Finset.subset_union_left⟩
      apply Finset.mem_image.mpr
      refine ⟨B ∪ R, hParent, ?_⟩
      simp [Finset.union_sdiff_distrib,
        Finset.sdiff_eq_self_of_disjoint hParts.2.2.1]
    · intro hR
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hR
      have hParts := Finset.mem_filter.mp hE
      have hCard : (E \ B).card = 2 := by
        rw [Finset.card_sdiff_of_subset hParts.2, hUniform hParts.1]
        omega
      have hRecon : B ∪ (E \ B) = E := Finset.union_sdiff_of_subset hParts.2
      exact mem_parent_pair_link.mpr
        ⟨(Finset.sdiff_subset.trans (hAmbient E hParts.1)),
          hCard, Finset.sdiff_disjoint,
          hRecon.symm ▸ hParts.1⟩
  rw [hEq]
  exact Finset.card_image_iff.mpr (by
    intro E hE F hF hDiff
    have hBE : B ⊆ E := (Finset.mem_filter.mp hE).2
    have hBF : B ⊆ F := (Finset.mem_filter.mp hF).2
    calc
      E = B ∪ (E \ B) := (Finset.union_sdiff_of_subset hBE).symm
      _ = B ∪ (F \ B) := by simpa only using congrArg (fun X => B ∪ X) hDiff
      _ = F := Finset.union_sdiff_of_subset hBF)

/-- The first completion root of an actual bad facet incidence belongs to
    the retained parent pair link at its underlying triple core. -/
theorem facet_bad_incidence_first_root_mem_pair_link
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V facetCenter tripleLabel) :
    facetWitnessRoot i ∈ parentPairLink K V (facetWitnessCore i) := by
  classical
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : i.1.2.card = 4 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hi).2.1
  have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hi).2.2.2.1
  have hBE : facetWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans hAE
  have hBcard : (facetWitnessCore i).card = 3 := by
    have hErase := Finset.card_erase_add_one ha
    change (i.1.2.erase i.2).card = 3
    omega
  have hRcard : (facetWitnessRoot i).card = 2 := by
    change (i.1.1 \ facetWitnessCore i).card = 2
    rw [Finset.card_sdiff_of_subset hBE, hUniformK hE]
    omega
  have hRecon : facetWitnessCore i ∪ facetWitnessRoot i = i.1.1 :=
    Finset.union_sdiff_of_subset hBE
  exact mem_parent_pair_link.mpr
    ⟨Finset.sdiff_subset.trans (hAmbientK i.1.1 hE),
      hRcard, Finset.sdiff_disjoint, hRecon.symm ▸ hE⟩

/-- The IV.7 cleanup construction supplies the full first/second-root
    `hKeep` interface required in the facet witness lower count. -/
theorem facet_bad_incidence_roots_survive_multilevel_cleanup
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (C : Family α)
    (u q : ℕ) (bad : Edge α → Edge α → Edge α → Prop)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hC : ∀ i ∈ I, facetWitnessCore i ∈ C)
    (hSurvive : Disjoint K (multilevelDeletedEdges H V C 2 u q bad)) :
    ∀ i ∈ I,
      ∀ R ∈ insert (facetWitnessRoot i) (facetWitnessSecondRoots K V i),
        R ∈ actualCoreLink H V (facetWitnessCore i) 2 ∧
          R ∉ cleanupTails H V (facetWitnessCore i) 2 u q bad := by
  intro i hi R hR
  have hRoot : R ∈ parentPairLink K V (facetWitnessCore i) := by
    rcases Finset.mem_insert.mp hR with rfl | hSecond
    · exact facet_bad_incidence_first_root_mem_pair_link K V
        facetCenter tripleLabel hUniformK hAmbientK (hI hi)
    · exact (Finset.mem_filter.mp hSecond).1
  exact retained_pair_root_survives_multilevel_cleanup K H V C
    u q bad hKH hSurvive (hC i hi) hRoot

/-- Four-faces with retention below `P / Q`. -/
noncomputable def lowFacetCores
    (K H : Family α) (P Q : ℕ) : Family α := by
  classical
  exact (fourShadow K).filter fun A =>
    Q * (facetParents K A).card < P * (facetParents H A).card

/-- Actual bad facet incidences whose upper four-face has low retention. -/
noncomputable def lowFacetBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact (facetBadIncidences K V facetCenter tripleLabel).filter fun i =>
    Q * (facetParents K i.1.2).card <
      P * (facetParents H i.1.2).card

/-- Each fixed four-face has at most four bad deleted-vertex incidences per
    retained parent. -/
theorem low_facet_bad_incidence_card_le_parent_degree_sum
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) :
    (lowFacetBadIncidences K H V P Q facetCenter tripleLabel).card ≤
      4 * ∑ A ∈ lowFacetCores K H P Q, (facetParents K A).card := by
  classical
  let I := lowFacetBadIncidences K H V P Q facetCenter tripleLabel
  let C := lowFacetCores K H P Q
  have hMap : ∀ i ∈ I, i.1.2 ∈ C := by
    intro i hi
    have hParts := Finset.mem_filter.mp hi
    have hBad := (Finset.mem_filter.mp hParts.1).2
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hBad.2.1).1, hParts.2⟩
  have hOne : ∀ A ∈ C,
      (I.filter fun i => i.1.2 = A).card ≤
        4 * (facetParents K A).card := by
    intro A hA
    let F := I.filter fun i => i.1.2 = A
    have hAcard : A.card = 4 := by
      have hShadow : A ∈ fourShadow K := (Finset.mem_filter.mp hA).1
      obtain ⟨_, _, _, hCard⟩ := (mem_four_shadow_iff_parent K A).mp hShadow
      exact hCard
    have hCard : F.card ≤ ((facetParents K A) ×ˢ A).card := by
      apply Finset.card_le_card_of_injOn (fun i => (i.1.1, i.2))
      · intro i hi
        have hI : i ∈ I := (Finset.mem_filter.mp hi).1
        have hAeq : i.1.2 = A := (Finset.mem_filter.mp hi).2
        have hBad := (Finset.mem_filter.mp hI).1
        have hSource := (Finset.mem_filter.mp hBad).1
        have hE : i.1.1 ∈ K :=
          (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
        have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hBad).2.1
        have ha : i.2 ∈ i.1.2 :=
          (Finset.mem_filter.mp hBad).2.2.2.1
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hE, hAeq ▸ hAE⟩, hAeq ▸ ha⟩
      · intro i hi j hj hEq
        have hAeqI : i.1.2 = A := (Finset.mem_filter.mp hi).2
        have hAeqJ : j.1.2 = A := (Finset.mem_filter.mp hj).2
        have hEq' : (i.1.1, i.2) = (j.1.1, j.2) := hEq
        have hEeq : i.1.1 = j.1.1 := congrArg (fun p : Edge α × α => p.1) hEq'
        have haeq : i.2 = j.2 := congrArg (fun p : Edge α × α => p.2) hEq'
        apply Prod.ext
        · exact Prod.ext hEeq (hAeqI.trans hAeqJ.symm)
        · exact haeq
    simpa [Finset.card_product, hAcard, mul_comm] using hCard
  have hFiber := Finset.card_eq_sum_card_fiberwise
    (f := fun i : (Edge α × Edge α) × α => i.1.2)
    (s := I) (t := C) hMap
  calc
    I.card = ∑ A ∈ C, (I.filter fun i => i.1.2 = A).card := hFiber
    _ ≤ ∑ A ∈ C, 4 * (facetParents K A).card :=
      Finset.sum_le_sum hOne
    _ = 4 * ∑ A ∈ C, (facetParents K A).card := by
      rw [Finset.mul_sum]

/-- The actual upper-four-face low-retention contribution is small in the
    exact IV.9.1 scale.  No assumption on colors or bad-partner geometry is
    used beyond membership in the bad incidence set. -/
theorem low_facet_bad_incidence_budget
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformH : Uniform 5 H) :
    Q * (lowFacetBadIncidences K H V P Q
      facetCenter tripleLabel).card ≤ 20 * P * H.card := by
  classical
  let C := lowFacetCores K H P Q
  have hCsub : C ⊆ fourShadow H := by
    intro A hA
    have hShadowK : A ∈ fourShadow K := (Finset.mem_filter.mp hA).1
    obtain ⟨E, hE, hAE, hAcard⟩ :=
      (mem_four_shadow_iff_parent K A).mp hShadowK
    exact (mem_four_shadow_iff_parent H A).mpr
      ⟨E, hKH hE, hAE, hAcard⟩
  have hLowSum :
      Q * (∑ A ∈ C, (facetParents K A).card) ≤
        P * (∑ A ∈ C, (facetParents H A).card) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    exact Nat.le_of_lt (Finset.mem_filter.mp hA).2
  have hHsum : (∑ A ∈ C, (facetParents H A).card) ≤ 5 * H.card := by
    calc
      (∑ A ∈ C, (facetParents H A).card) ≤
          ∑ A ∈ fourShadow H, (facetParents H A).card :=
        Finset.sum_le_sum_of_subset_of_nonneg hCsub (by simp)
      _ = 5 * H.card := four_shadow_parent_incidence_count H hUniformH
  have hInc := low_facet_bad_incidence_card_le_parent_degree_sum
    K H V P Q facetCenter tripleLabel
  calc
    Q * (lowFacetBadIncidences K H V P Q
      facetCenter tripleLabel).card ≤
        Q * (4 * ∑ A ∈ C, (facetParents K A).card) :=
      Nat.mul_le_mul_left _ hInc
    _ = 4 * (Q * ∑ A ∈ C, (facetParents K A).card) := by ring
    _ ≤ 4 * (P * ∑ A ∈ C, (facetParents H A).card) :=
      Nat.mul_le_mul_left _ hLowSum
    _ ≤ 4 * (P * (5 * H.card)) := by
      exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left P hHsum)
    _ = 20 * P * H.card := by ring

/-- Triple cores with retention below `P / Q`. -/
noncomputable def lowTripleCores
    (K H : Family α) (V : Edge α) (P Q : ℕ) : Family α := by
  classical
  exact (V.powersetCard 3).filter fun B =>
    Q * (K.filter fun E => B ⊆ E).card <
      P * (H.filter fun E => B ⊆ E).card

/-- Actual bad facet incidences whose lower triple core has low retention. -/
noncomputable def lowTripleBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact (facetBadIncidences K V facetCenter tripleLabel).filter fun i =>
    Q * (K.filter fun E => facetWitnessCore i ⊆ E).card <
      P * (H.filter fun E => facetWitnessCore i ⊆ E).card

/-- For a fixed triple core, each retained parent has only two possible
    deleted vertices. -/
theorem low_triple_bad_incidence_card_le_parent_degree_sum
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) :
    (lowTripleBadIncidences K H V P Q facetCenter tripleLabel).card ≤
      2 * ∑ B ∈ lowTripleCores K H V P Q,
        (K.filter fun E => B ⊆ E).card := by
  classical
  let I := lowTripleBadIncidences K H V P Q facetCenter tripleLabel
  let C := lowTripleCores K H V P Q
  have hMap : ∀ i ∈ I, facetWitnessCore i ∈ C := by
    intro i hi
    have hParts := Finset.mem_filter.mp hi
    have hBad := hParts.1
    have hSource := (Finset.mem_filter.mp hBad).1
    have hE : i.1.1 ∈ K :=
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
    have hAcard : i.1.2.card = 4 :=
      (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
    have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hBad).2.1
    have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hBad).2.2.2.1
    have hBcard : (facetWitnessCore i).card = 3 := by
      have herase := Finset.card_erase_add_one ha
      change (i.1.2.erase i.2).card = 3
      omega
    have hBV : facetWitnessCore i ⊆ V :=
      (Finset.erase_subset i.2 i.1.2).trans
        (hAE.trans (hAmbientK i.1.1 hE))
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hBV, hBcard⟩, hParts.2⟩
  have hOne : ∀ B ∈ C,
      (I.filter fun i => facetWitnessCore i = B).card ≤
        2 * (K.filter fun E => B ⊆ E).card := by
    intro B hB
    let F := I.filter fun i => facetWitnessCore i = B
    have hBcard : B.card = 3 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1).2
    let parents := K.filter fun E => B ⊆ E
    have hCard : F.card ≤ (parents.sigma fun E => E \ B).card := by
      let f : ((Edge α × Edge α) × α) → ((E : Edge α) × α) :=
        fun i => ⟨i.1.1, i.2⟩
      apply Finset.card_le_card_of_injOn f
      · intro i hi
        have hI : i ∈ I := (Finset.mem_filter.mp hi).1
        have hCore : facetWitnessCore i = B := (Finset.mem_filter.mp hi).2
        have hBad := (Finset.mem_filter.mp hI).1
        have hSource := (Finset.mem_filter.mp hBad).1
        have hE : i.1.1 ∈ K :=
          (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
        have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hBad).2.1
        have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hBad).2.2.2.1
        have hBE : B ⊆ i.1.1 := by
          rw [← hCore]
          exact (Finset.erase_subset i.2 i.1.2).trans hAE
        have haNotB : i.2 ∉ B := by
          rw [← hCore]
          intro hErase
          exact (Finset.mem_erase.mp hErase).1 rfl
        exact Finset.mem_sigma.mpr
          ⟨Finset.mem_filter.mpr ⟨hE, hBE⟩,
            Finset.mem_sdiff.mpr ⟨hAE ha, haNotB⟩⟩
      · intro i hi j hj hEq
        have hCoreI : facetWitnessCore i = B := (Finset.mem_filter.mp hi).2
        have hCoreJ : facetWitnessCore j = B := (Finset.mem_filter.mp hj).2
        have hBadI := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        have hBadJ := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        have haI : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hBadI).2.2.2.1
        have haJ : j.2 ∈ j.1.2 := (Finset.mem_filter.mp hBadJ).2.2.2.1
        have hEeq : i.1.1 = j.1.1 :=
          congrArg (fun p : (E : Edge α) × α => p.1) hEq
        have haeq : i.2 = j.2 :=
          congrArg (fun p : (E : Edge α) × α => p.2) hEq
        have hAeq : i.1.2 = j.1.2 := by
          calc
            i.1.2 = B ∪ {i.2} := by
              rw [← hCoreI]
              simp [facetWitnessCore, Finset.union_singleton,
                Finset.insert_erase haI]
            _ = B ∪ {j.2} := by rw [haeq]
            _ = j.1.2 := by
              rw [← hCoreJ]
              simp [facetWitnessCore, Finset.union_singleton,
                Finset.insert_erase haJ]
        apply Prod.ext
        · exact Prod.ext hEeq hAeq
        · exact haeq
    have hSigma : (parents.sigma fun E => E \ B).card =
        2 * parents.card := by
      rw [Finset.card_sigma]
      calc
        (∑ E ∈ parents, (E \ B).card) = ∑ _E ∈ parents, 2 := by
          apply Finset.sum_congr rfl
          intro E hE
          have hParts := Finset.mem_filter.mp hE
          rw [Finset.card_sdiff_of_subset hParts.2, hUniformK hParts.1]
          omega
        _ = 2 * parents.card := by simp [mul_comm]
    exact hCard.trans_eq hSigma
  have hFiber := Finset.card_eq_sum_card_fiberwise
    (f := facetWitnessCore) (s := I) (t := C) hMap
  calc
    I.card = ∑ B ∈ C, (I.filter fun i => facetWitnessCore i = B).card := hFiber
    _ ≤ ∑ B ∈ C, 2 * (K.filter fun E => B ⊆ E).card :=
      Finset.sum_le_sum hOne
    _ = 2 * ∑ B ∈ C, (K.filter fun E => B ⊆ E).card := by
      rw [Finset.mul_sum]

/-- The low-retention triple-core contribution has the same exact budget as
    the upper-facet contribution. -/
theorem low_triple_bad_incidence_budget
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V) :
    Q * (lowTripleBadIncidences K H V P Q
      facetCenter tripleLabel).card ≤ 20 * P * H.card := by
  classical
  let C := lowTripleCores K H V P Q
  have hCsub : C ⊆ V.powersetCard 3 := Finset.filter_subset _ _
  have hLowSum :
      Q * (∑ B ∈ C, (K.filter fun E => B ⊆ E).card) ≤
        P * (∑ B ∈ C, (H.filter fun E => B ⊆ E).card) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    exact Nat.le_of_lt (Finset.mem_filter.mp hB).2
  have hHsum : (∑ B ∈ C, (H.filter fun E => B ⊆ E).card) ≤
      10 * H.card := by
    calc
      (∑ B ∈ C, (H.filter fun E => B ⊆ E).card) ≤
          ∑ B ∈ V.powersetCard 3,
            (H.filter fun E => B ⊆ E).card :=
        Finset.sum_le_sum_of_subset_of_nonneg hCsub (by simp)
      _ = 10 * H.card :=
        total_three_core_parent_degrees_eq_ten_edges H V hUniformH hAmbientH
  have hInc := low_triple_bad_incidence_card_le_parent_degree_sum
    K H V P Q facetCenter tripleLabel hUniformK
    (fun E hE => hAmbientH E (hKH hE))
  calc
    Q * (lowTripleBadIncidences K H V P Q
      facetCenter tripleLabel).card ≤
        Q * (2 * ∑ B ∈ C, (K.filter fun E => B ⊆ E).card) :=
      Nat.mul_le_mul_left _ hInc
    _ = 2 * (Q * ∑ B ∈ C, (K.filter fun E => B ⊆ E).card) := by ring
    _ ≤ 2 * (P * ∑ B ∈ C, (H.filter fun E => B ⊆ E).card) :=
      Nat.mul_le_mul_left _ hLowSum
    _ ≤ 2 * (P * (10 * H.card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hHsum)
    _ = 20 * P * H.card := by ring

/-- Bad facet incidences with low retention at either the four-face or its
    underlying triple core. -/
noncomputable def lowEitherBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact lowFacetBadIncidences K H V P Q facetCenter tripleLabel ∪
    lowTripleBadIncidences K H V P Q facetCenter tripleLabel

/-- The two low-retention contributions together cost at most forty parent
    edges at scale `P / Q`. -/
theorem low_either_bad_incidence_budget
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V) :
    Q * (lowEitherBadIncidences K H V P Q
      facetCenter tripleLabel).card ≤ 40 * P * H.card := by
  classical
  have hA := low_facet_bad_incidence_budget K H V P Q
    facetCenter tripleLabel hKH hUniformH
  have hB := low_triple_bad_incidence_budget K H V P Q
    facetCenter tripleLabel hKH hUniformK hUniformH hAmbientH
  have hUnion := Finset.card_union_le
    (lowFacetBadIncidences K H V P Q facetCenter tripleLabel)
    (lowTripleBadIncidences K H V P Q facetCenter tripleLabel)
  dsimp [lowEitherBadIncidences]
  nlinarith

/-- The incidences on which both the four-face and triple core pass the
    retention threshold. -/
noncomputable def highRetentionBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact facetBadIncidences K V facetCenter tripleLabel \
    lowEitherBadIncidences K H V P Q facetCenter tripleLabel

theorem high_retention_bad_incidence_subset
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) :
    highRetentionBadIncidences K H V P Q facetCenter tripleLabel ⊆
      facetBadIncidences K V facetCenter tripleLabel := by
  exact Finset.sdiff_subset

/-- The positive retention threshold turns lower bounds on parent degrees
    into lower bounds on the two retained degrees used by IV.9.3. -/
theorem high_retention_bad_incidence_degrees
    (K H : Family α) (V : Edge α) (P Q L₄ L₃ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hQ : 0 < Q)
    (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hMinFacet : ∀ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel,
        Q * L₄ ≤ P * (facetParents H i.1.2).card)
    (hMinTriple : ∀ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel,
        Q * L₃ ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card) :
    (∀ i ∈ highRetentionBadIncidences K H V P Q facetCenter tripleLabel,
      L₄ ≤ (facetParents K i.1.2).card) ∧
    (∀ i ∈ highRetentionBadIncidences K H V P Q facetCenter tripleLabel,
      L₃ ≤ (parentPairLink K V (facetWitnessCore i)).card) := by
  classical
  constructor
  · intro i hi
    have hBad : i ∈ facetBadIncidences K V facetCenter tripleLabel :=
      (Finset.mem_sdiff.mp hi).1
    have hNotLow := (Finset.mem_sdiff.mp hi).2
    have hRetention : P * (facetParents H i.1.2).card ≤
        Q * (facetParents K i.1.2).card := by
      by_contra hNot
      have hLt : Q * (facetParents K i.1.2).card <
          P * (facetParents H i.1.2).card := by omega
      exact hNotLow (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hBad, hLt⟩)))
    have hMin := hMinFacet i hi
    have hScaled : Q * L₄ ≤ Q * (facetParents K i.1.2).card :=
      hMin.trans hRetention
    exact (Nat.mul_le_mul_left_iff hQ).mp hScaled
  · intro i hi
    have hBad : i ∈ facetBadIncidences K V facetCenter tripleLabel :=
      (Finset.mem_sdiff.mp hi).1
    have hNotLow := (Finset.mem_sdiff.mp hi).2
    have hRetention :
        P * (H.filter fun E => facetWitnessCore i ⊆ E).card ≤
          Q * (K.filter fun E => facetWitnessCore i ⊆ E).card := by
      by_contra hNot
      have hLt : Q * (K.filter fun E => facetWitnessCore i ⊆ E).card <
          P * (H.filter fun E => facetWitnessCore i ⊆ E).card := by omega
      exact hNotLow (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hBad, hLt⟩)))
    have hSource := (Finset.mem_filter.mp hBad).1
    have hE : i.1.1 ∈ K :=
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
    have hAcard : i.1.2.card = 4 :=
      (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
    have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hBad).2.2.2.1
    have hBcard : (facetWitnessCore i).card = 3 := by
      have hErase := Finset.card_erase_add_one ha
      change (i.1.2.erase i.2).card = 3
      omega
    have hEq := triple_parent_pair_link_card_eq_codegree
      K V (facetWitnessCore i) hUniformK hAmbientK hBcard
    have hMin := hMinTriple i hi
    have hScaled : Q * L₃ ≤
        Q * (K.filter fun E => facetWitnessCore i ⊆ E).card :=
      hMin.trans hRetention
    rw [← hEq] at hScaled
    exact (Nat.mul_le_mul_left_iff hQ).mp hScaled

/-- On high-retention triple cores, a numeric lower bound `L₃` gives both
    IV.7 size conditions when `u` and `4q` lie below that bound. -/
theorem high_retention_cleanup_degree
    (K H : Family α) (V : Edge α) (P Q L₃ u q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H)
    (hQ : 0 < Q)
    (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hMinTriple : ∀ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel,
        Q * L₃ ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card)
    (hu : u ≤ L₃) (hq : 4 * q ≤ L₃) :
    ∀ i ∈ highRetentionBadIncidences K H V P Q facetCenter tripleLabel,
      u ≤ (actualCoreLink H V (facetWitnessCore i) 2).card ∧
      4 * q ≤ (parentPairLink K V (facetWitnessCore i)).card := by
  have hRetained := (high_retention_bad_incidence_degrees K H V P Q
    0 L₃ facetCenter tripleLabel hQ hUniformK hAmbientK
    (by intro i hi; simp) hMinTriple).2
  intro i hi
  have hB := hRetained i hi
  have hLinkSub : parentPairLink K V (facetWitnessCore i) ⊆
      parentPairLink H V (facetWitnessCore i) := by
    intro R hR
    have hParts := mem_parent_pair_link.mp hR
    exact mem_parent_pair_link.mpr
      ⟨hParts.1, hParts.2.1, hParts.2.2.1, hKH hParts.2.2.2⟩
  have hH : (parentPairLink K V (facetWitnessCore i)).card ≤
      (actualCoreLink H V (facetWitnessCore i) 2).card := by
    rw [actual_core_link_two_eq_parent_pair_link]
    exact Finset.card_le_card hLinkSub
  exact ⟨(hu.trans hB).trans hH, hq.trans hB⟩

/-- The actual partial color on a pair of completion vertices, formed from
    their common four-core cell in the fixed parent family. -/
noncomputable def upperSingletonPairColor
    (H : Family α) (V : Edge α) (tUpper : ℕ) (x y : α) : Option α := by
  classical
  if h : ∃ z : α,
      tUpper ≤ (commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) 4).card ∧
        UniqueCellCenter (commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) 4) z then
    exact some (Classical.choose h)
  else
    exact none

/-- For two distinct ambient vertices, the partial color is present with
    label `z` exactly when their singleton roots are actual strong partners
    with that label. -/
theorem upper_singleton_pair_color_eq_some_iff_strong
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {x y z : α} (_hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y) :
    upperSingletonPairColor H V tUpper x y = some z ↔
      ActualStrongPartner H V ({x} : Edge α) ({y} : Edge α)
        1 4 tUpper z := by
  classical
  let cell := commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) 4
  have hGeom : ({y} : Edge α) ∈ V.powersetCard 1 ∧
      Disjoint ({x} : Edge α) ({y} : Edge α) := by
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨by simpa using hy, by simp⟩
    · simpa [Finset.disjoint_singleton] using hxy
  constructor
  · intro hColor
    by_cases h : ∃ z' : α, tUpper ≤ cell.card ∧ UniqueCellCenter cell z'
    · have hColor' : some (Classical.choose h) = some z := by
        simpa [upperSingletonPairColor, h, cell] using hColor
      have hSpec := Classical.choose_spec h
      have hz : Classical.choose h = z := Option.some.inj hColor'
      exact ⟨hGeom.1, hGeom.2, hSpec.1, hz ▸ hSpec.2⟩
    · simp [upperSingletonPairColor, h, cell] at hColor
  · intro hStrong
    have h : ∃ z' : α, tUpper ≤ cell.card ∧ UniqueCellCenter cell z' :=
      ⟨z, hStrong.2.2.1, hStrong.2.2.2⟩
    have hSpec := (Classical.choose_spec h).2
    have hEq : Classical.choose h = z :=
      (hSpec.2 z hStrong.2.2.2.1).symm
    simp [upperSingletonPairColor, h, cell, hEq]

theorem upper_singleton_pair_color_symm
    (H : Family α) (V : Edge α) (tUpper : ℕ) (x y : α) :
    upperSingletonPairColor H V tUpper x y =
      upperSingletonPairColor H V tUpper y x := by
  classical
  simp only [upperSingletonPairColor]
  rw [common_prefix_tails_comm H V ({y} : Edge α) ({x} : Edge α) 4]

/-- Ordered completion pairs left uncolored by the actual parent cells. -/
noncomputable def upperUncoloredPairs
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Finset (α × α) := by
  classical
  exact (V ×ˢ V).filter fun p =>
    p.1 ≠ p.2 ∧ upperSingletonPairColor H V tUpper p.1 p.2 = none

/-- Actual parent edges involved in an uncolored upper-facet pair. -/
noncomputable def upperUncoloredFacetEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperUncoloredPairs H V tUpper).biUnion fun p =>
    (commonPrefixTails H V ({p.1} : Edge α) ({p.2} : Edge α) 4).biUnion
      fun A => ({insert p.1 A, insert p.2 A} : Family α)

/-- Each uncolored pair-facet incidence pays for at most its two parent
    edges. This is the finite deletion accounting in IV.8.1 before the
    uncolored common-cell estimate is substituted. -/
theorem upper_uncolored_facet_edges_card_le_cells
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    (upperUncoloredFacetEdges H V tUpper).card ≤
      2 * ∑ p ∈ upperUncoloredPairs H V tUpper,
        (commonPrefixTails H V ({p.1} : Edge α)
          ({p.2} : Edge α) 4).card := by
  classical
  let U := upperUncoloredPairs H V tUpper
  let cell := fun p : α × α =>
    commonPrefixTails H V ({p.1} : Edge α) ({p.2} : Edge α) 4
  have hFiber : ∀ p ∈ U,
      ((cell p).biUnion fun A => ({insert p.1 A, insert p.2 A} : Family α)).card ≤
        2 * (cell p).card := by
    intro p hp
    calc
      _ ≤ ∑ A ∈ cell p,
          ({insert p.1 A, insert p.2 A} : Family α).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ cell p, 2 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Finset.card_le_two
      _ = 2 * (cell p).card := by simp [mul_comm]
  calc
    (upperUncoloredFacetEdges H V tUpper).card ≤
        ∑ p ∈ U,
          ((cell p).biUnion fun A =>
            ({insert p.1 A, insert p.2 A} : Family α)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ U, 2 * (cell p).card := Finset.sum_le_sum hFiber
    _ = 2 * ∑ p ∈ U, (cell p).card := by rw [Finset.mul_sum]

/-- With a uniform uncolored-cell cap, IV.8.1 costs at most two edge
    deletions per ordered pair and per supporting facet. -/
theorem upper_uncolored_facet_edges_card_le_ambient_square
    (H : Family α) (V : Edge α) (tUpper C : ℕ)
    (hCell : ∀ p ∈ upperUncoloredPairs H V tUpper,
      (commonPrefixTails H V ({p.1} : Edge α)
        ({p.2} : Edge α) 4).card ≤ C) :
    (upperUncoloredFacetEdges H V tUpper).card ≤
      2 * V.card ^ 2 * C := by
  classical
  have hCells := upper_uncolored_facet_edges_card_le_cells H V tUpper
  have hSum :
      (∑ p ∈ upperUncoloredPairs H V tUpper,
        (commonPrefixTails H V ({p.1} : Edge α)
          ({p.2} : Edge α) 4).card) ≤
        (upperUncoloredPairs H V tUpper).card * C := by
    calc
      _ ≤ ∑ _p ∈ upperUncoloredPairs H V tUpper, C :=
        Finset.sum_le_sum hCell
      _ = (upperUncoloredPairs H V tUpper).card * C := by simp
  have hPair : (upperUncoloredPairs H V tUpper).card ≤ V.card ^ 2 := by
    calc
      _ ≤ (V ×ˢ V).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = V.card ^ 2 := by simp [Finset.card_product, pow_two]
  calc
    (upperUncoloredFacetEdges H V tUpper).card ≤
        2 * ∑ p ∈ upperUncoloredPairs H V tUpper,
          (commonPrefixTails H V ({p.1} : Edge α)
            ({p.2} : Edge α) 4).card := hCells
    _ ≤ 2 * ((upperUncoloredPairs H V tUpper).card * C) :=
      Nat.mul_le_mul_left 2 hSum
    _ ≤ 2 * V.card ^ 2 * C := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right C hPair) |>.trans_eq (by ring)

/-- An uncolored singleton pair has a small actual common-four-core cell
    when each two-vertex fiber through its first root has bounded parent
    degree. This is the IV.1.1 input in IV.8.1. -/
theorem upper_uncolored_pair_cell_bound
    (H : Family α) (V : Edge α) (tUpper D : ℕ)
    (hAdm : Admissible H)
    (hCap : ∀ x : α, ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => ({x} : Edge α) ∪ Q ⊆ E).card ≤ D)
    {x y : α} (_hx : x ∈ V) (_hy : y ∈ V) (hxy : x ≠ y)
    (hNone : upperSingletonPairColor H V tUpper x y = none) :
    (commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) 4).card ≤
      tUpper + 16 * D := by
  classical
  let cell := commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) 4
  change cell.card ≤ tUpper + 16 * D
  by_cases hSmall : cell.card < tUpper
  · omega
  have hLarge : tUpper ≤ cell.card := by omega
  have hNoUnique : ∀ z : α, ¬ UniqueCellCenter cell z := by
    intro z hz
    have hExists : ∃ w : α, tUpper ≤ cell.card ∧ UniqueCellCenter cell w :=
      ⟨z, hLarge, hz⟩
    have hColor : upperSingletonPairColor H V tUpper x y ≠ none := by
      simp [upperSingletonPairColor, hExists, cell]
    exact hColor hNone
  by_cases hEmpty : cell = ∅
  · simp [hEmpty]
  have hMember : ∃ A, A ∈ cell := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨A, hA⟩ := hMember
  have hY : ({x} : Edge α).Nonempty := by simp
  have hZ : ({y} : Edge α).Nonempty := by simp
  have hDisj : Disjoint ({x} : Edge α) ({y} : Edge α) := by
    simpa [Finset.disjoint_singleton] using hxy
  by_cases hNoCenter : NoGlobalCenter cell
  · have hBound := JSP523.common_prefix_tails_card_le_pair_degree_no_center
      (H := H) (W := V) (Y := ({x} : Edge α))
      (Z := ({y} : Edge α)) (A := A) (t := 4) (D := D)
      hAdm hY hZ hDisj (by omega) hA hNoCenter (hCap x)
    change cell.card ≤ 4 * 4 * D at hBound
    omega
  · have hCenter : ∃ z : α, ∀ B ∈ cell, z ∈ B := by
      by_contra h
      exact hNoCenter (by
        intro z
        by_contra hz
        exact h ⟨z, by intro B hB; by_contra hzB; exact hz ⟨B, hB, hzB⟩⟩)
    obtain ⟨z, hz⟩ := hCenter
    have hAnother : ∃ w : α, w ≠ z ∧ ∀ B ∈ cell, w ∈ B := by
      by_contra h
      apply hNoUnique z
      refine ⟨hz, ?_⟩
      intro w hw
      by_contra hwz
      exact h ⟨w, hwz, hw⟩
    obtain ⟨w, hwz, hw⟩ := hAnother
    have hBound := JSP523.common_prefix_tails_card_le_pair_degree_common_pair
      (H := H) (W := V) (Y := ({x} : Edge α))
      (Z := ({y} : Edge α)) (t := 4) (D := D)
      (x := z) (y := w) hwz.symm hz hw (hCap x)
    change cell.card ≤ D at hBound
    omega

/-- An actual IV.8.1 deletion bound from the parent common-cell geometry.
    The codegree premise is stated on the exact prefix-plus-pair fibers
    used by the finite IV.1.1 lemma. -/
theorem upper_uncolored_facet_edges_actual_budget
    (H : Family α) (V : Edge α) (tUpper D : ℕ)
    (hAdm : Admissible H)
    (hCap : ∀ x : α, ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => ({x} : Edge α) ∪ Q ⊆ E).card ≤ D) :
    (upperUncoloredFacetEdges H V tUpper).card ≤
      2 * V.card ^ 2 * (tUpper + 16 * D) := by
  apply upper_uncolored_facet_edges_card_le_ambient_square
    H V tUpper (tUpper + 16 * D)
  intro p hp
  have hParts := Finset.mem_filter.mp hp
  have hV := Finset.mem_product.mp hParts.1
  exact upper_uncolored_pair_cell_bound H V tUpper D hAdm hCap
    hV.1 hV.2 hParts.2.1 hParts.2.2

/-- Ordered completion triples carrying three actual colors that are not
    all equal. These are the union of the bicolored and rainbow cases in
    IV.8.2–IV.8.3. -/
noncomputable def upperNonmonochromaticTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact ((V ×ˢ V) ×ˢ V).filter fun p =>
    p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2 ∧
      (upperSingletonPairColor H V tUpper p.1.1 p.1.2 ≠ none) ∧
      (upperSingletonPairColor H V tUpper p.1.1 p.2 ≠ none) ∧
      (upperSingletonPairColor H V tUpper p.1.2 p.2 ≠ none) ∧
      (upperSingletonPairColor H V tUpper p.1.1 p.1.2 ≠
        upperSingletonPairColor H V tUpper p.1.1 p.2 ∨
       upperSingletonPairColor H V tUpper p.1.1 p.2 ≠
        upperSingletonPairColor H V tUpper p.1.2 p.2)

/-- Facets simultaneously completed by the vertices of one triangle. -/
noncomputable def upperTriangleFacetCell
    (H : Family α) (V : Edge α) (p : (α × α) × α) : Family α := by
  classical
  exact (V.powersetCard 4).filter fun A =>
    p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.2 ∉ A ∧
      insert p.1.1 A ∈ H ∧ insert p.1.2 A ∈ H ∧ insert p.2 A ∈ H

/-- The three actual parent edges deleted for each supported
    nonmonochromatic completion triangle. -/
noncomputable def upperNonmonochromaticTriangleEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperNonmonochromaticTriples H V tUpper).biUnion fun p =>
    (upperTriangleFacetCell H V p).biUnion fun A =>
      ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)

/-- Exact IV.8.2–IV.8.3 finite deletion accounting before the bicolored
    and rainbow supporting-facet estimates are applied. -/
theorem upper_nonmonochromatic_triangle_edges_card_le_cells
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    (upperNonmonochromaticTriangleEdges H V tUpper).card ≤
      3 * ∑ p ∈ upperNonmonochromaticTriples H V tUpper,
        (upperTriangleFacetCell H V p).card := by
  classical
  let T := upperNonmonochromaticTriples H V tUpper
  let cell := upperTriangleFacetCell H V
  have hFiber : ∀ p ∈ T,
      ((cell p).biUnion fun A =>
        ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card ≤
          3 * (cell p).card := by
    intro p hp
    calc
      _ ≤ ∑ A ∈ cell p,
          ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ cell p, 3 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Finset.card_le_three
      _ = 3 * (cell p).card := by simp [mul_comm]
  calc
    (upperNonmonochromaticTriangleEdges H V tUpper).card ≤
        ∑ p ∈ T,
          ((cell p).biUnion fun A =>
            ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ T, 3 * (cell p).card := Finset.sum_le_sum hFiber
    _ = 3 * ∑ p ∈ T, (cell p).card := by rw [Finset.mul_sum]

/-- A colored singleton pair's unique parent-cell label lies in every
    facet supported by that completion pair. -/
theorem upper_pair_color_label_mem_supporting_facet
    (H : Family α) (V A : Edge α) (tUpper : ℕ)
    {x y c : α} (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    (hAV : A ⊆ V) (hAcard : A.card = 4)
    (hxA : x ∉ A) (hyA : y ∉ A)
    (hEx : insert x A ∈ H) (hEy : insert y A ∈ H)
    (hColor : upperSingletonPairColor H V tUpper x y = some c) :
    c ∈ A := by
  have hStrong := (upper_singleton_pair_color_eq_some_iff_strong
    H V tUpper hx hy hxy).mp hColor
  have hCell : A ∈ commonPrefixTails H V
      ({x} : Edge α) ({y} : Edge α) 4 := by
    apply mem_common_prefix_tails.mpr
    refine ⟨hAV, hAcard, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hvA hv
      simp only [Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxA hvA
      · exact hyA hvA
    · simpa using hEx
    · simpa using hEy
  exact hStrong.2.2.2.1 A hCell

/-- Colored nonmonochromatic triangles with three distinct actual labels. -/
noncomputable def upperRainbowTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact (upperNonmonochromaticTriples H V tUpper).filter fun p =>
    ∃ c₁ c₂ c₃ : α,
      c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
      upperSingletonPairColor H V tUpper p.1.1 p.1.2 = some c₁ ∧
      upperSingletonPairColor H V tUpper p.1.1 p.2 = some c₂ ∧
      upperSingletonPairColor H V tUpper p.1.2 p.2 = some c₃

/-- A rainbow completion triangle has at most `D₄` supporting facets:
    every such facet contains all three different labels, and its edge at
    the first completion vertex contains the resulting fixed four-set. -/
theorem upper_rainbow_triangle_facet_cell_le_four_codegree
    (H : Family α) (V : Edge α) (tUpper D₄ : ℕ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    {p : (α × α) × α}
    (hp : p ∈ upperRainbowTriples H V tUpper) :
    (upperTriangleFacetCell H V p).card ≤ D₄ := by
  classical
  obtain ⟨hTriangle, c₁, c₂, c₃, h12, h13, h23,
    hc₁, hc₂, hc₃⟩ := Finset.mem_filter.mp hp
  have hProd := (Finset.mem_filter.mp hTriangle).1
  have hVparts := Finset.mem_product.mp hProd
  have hXY := Finset.mem_product.mp hVparts.1
  have hx : p.1.1 ∈ V := hXY.1
  have hy : p.1.2 ∈ V := hXY.2
  have hz : p.2 ∈ V := hVparts.2
  have hDistinct := (Finset.mem_filter.mp hTriangle).2
  let cell := upperTriangleFacetCell H V p
  have hLabels : ∀ A ∈ cell, c₁ ∈ A ∧ c₂ ∈ A ∧ c₃ ∈ A := by
    intro A hA
    have hAparts := Finset.mem_filter.mp hA
    have hAV := (Finset.mem_powersetCard.mp hAparts.1).1
    have hAcard := (Finset.mem_powersetCard.mp hAparts.1).2
    rcases hAparts.2 with ⟨hxA, hyA, hzA, hEx, hEy, hEz⟩
    constructor
    · exact upper_pair_color_label_mem_supporting_facet H V A tUpper
        hx hy hDistinct.1 hAV hAcard hxA hyA hEx hEy hc₁
    constructor
    · exact upper_pair_color_label_mem_supporting_facet H V A tUpper
        hx hz hDistinct.2.1 hAV hAcard hxA hzA hEx hEz hc₂
    · exact upper_pair_color_label_mem_supporting_facet H V A tUpper
        hy hz hDistinct.2.2.1 hAV hAcard hyA hzA hEy hEz hc₃
  by_cases hEmpty : cell = ∅
  · change cell.card ≤ D₄
    simp [hEmpty]
  have hCellEmpty : cell.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hEmpty
  let S : Edge α := {p.1.1, c₁, c₂, c₃}
  have hXneq : p.1.1 ≠ c₁ ∧ p.1.1 ≠ c₂ ∧ p.1.1 ≠ c₃ := by
    obtain ⟨A, hA⟩ := hCellEmpty
    have hNot : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
    have hLab := hLabels A hA
    exact ⟨fun h => hNot (h ▸ hLab.1),
      fun h => hNot (h ▸ hLab.2.1),
      fun h => hNot (h ▸ hLab.2.2)⟩
  have hScard : S.card = 4 := by
    simp [S, hXneq.1, hXneq.2.1, hXneq.2.2,
      h12, h13, h23]
  have hInject : cell.card ≤ (H.filter fun E => S ⊆ E).card := by
    apply Finset.card_le_card_of_injOn (fun A => insert p.1.1 A)
    · intro A hA
      have hParts := (Finset.mem_filter.mp hA).2
      have hLab := hLabels A hA
      refine Finset.mem_filter.mpr ⟨hParts.2.2.2.1, ?_⟩
      intro v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | hv
      · exact Finset.mem_insert_self ..
      rcases hv with rfl | hv
      · exact Finset.mem_insert_of_mem hLab.1
      rcases hv with rfl | rfl
      · exact Finset.mem_insert_of_mem hLab.2.1
      · exact Finset.mem_insert_of_mem hLab.2.2
    · intro A hA B hB hEq
      have hxA : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
      have hxB : p.1.1 ∉ B := (Finset.mem_filter.mp hB).2.1
      have hErase := congrArg (Finset.erase · p.1.1) hEq
      simpa [hxA, hxB] using hErase
  exact hInject.trans (hD₄ S hScard)

/-- Actual parent edges deleted for rainbow completion triangles. -/
noncomputable def upperRainbowTriangleEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperRainbowTriples H V tUpper).biUnion fun p =>
    (upperTriangleFacetCell H V p).biUnion fun A =>
      ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)

/-- IV.8.3 with ordered triples: a factor three for deleted edges and an
    ambient `|V|³` bound for the possible completion triples. -/
theorem upper_rainbow_triangle_edges_actual_budget
    (H : Family α) (V : Edge α) (tUpper D₄ : ℕ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (upperRainbowTriangleEdges H V tUpper).card ≤
      3 * V.card ^ 3 * D₄ := by
  classical
  let T := upperRainbowTriples H V tUpper
  let cell := upperTriangleFacetCell H V
  have hFiber : ∀ p ∈ T,
      ((cell p).biUnion fun A =>
        ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card ≤
          3 * D₄ := by
    intro p hp
    have hCap := upper_rainbow_triangle_facet_cell_le_four_codegree
      H V tUpper D₄ hD₄ hp
    calc
      _ ≤ ∑ A ∈ cell p,
          ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ cell p, 3 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Finset.card_le_three
      _ = 3 * (cell p).card := by simp [mul_comm]
      _ ≤ 3 * D₄ := Nat.mul_le_mul_left 3 hCap
  have hTriple : T.card ≤ V.card ^ 3 := by
    calc
      T.card ≤ ((V ×ˢ V) ×ˢ V).card :=
        Finset.card_le_card ((Finset.filter_subset _ _).trans
          (Finset.filter_subset _ _))
      _ = V.card ^ 3 := by simp [Finset.card_product, pow_succ]
  calc
    (upperRainbowTriangleEdges H V tUpper).card ≤
        ∑ p ∈ T,
          ((cell p).biUnion fun A =>
            ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ T, 3 * D₄ := Finset.sum_le_sum hFiber
    _ = T.card * (3 * D₄) := by simp
    _ ≤ V.card ^ 3 * (3 * D₄) := Nat.mul_le_mul_right _ hTriple
    _ = 3 * V.card ^ 3 * D₄ := by ring

/-- Colored nonmonochromatic triples with a repeated color. -/
noncomputable def upperBicoloredTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact (upperNonmonochromaticTriples H V tUpper).filter fun p =>
    ∃ c₁ c₂ c₃ : α,
      (c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃) ∧
      upperSingletonPairColor H V tUpper p.1.1 p.1.2 = some c₁ ∧
      upperSingletonPairColor H V tUpper p.1.1 p.2 = some c₂ ∧
      upperSingletonPairColor H V tUpper p.1.2 p.2 = some c₃

/-- Every fully colored nonmonochromatic completion triangle is exactly
    bicolored or rainbow. -/
theorem upper_nonmonochromatic_triples_eq_bicolored_union_rainbow
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    upperNonmonochromaticTriples H V tUpper =
      upperBicoloredTriples H V tUpper ∪
        upperRainbowTriples H V tUpper := by
  classical
  ext p
  constructor
  · intro hp
    have hParts := (Finset.mem_filter.mp hp).2
    have hNot₁ := hParts.2.2.2.1
    have hNot₂ := hParts.2.2.2.2.1
    have hNot₃ := hParts.2.2.2.2.2.1
    cases h₁ : upperSingletonPairColor H V tUpper p.1.1 p.1.2 with
    | none => exact False.elim (hNot₁ h₁)
    | some c₁ =>
      cases h₂ : upperSingletonPairColor H V tUpper p.1.1 p.2 with
      | none => exact False.elim (hNot₂ h₂)
      | some c₂ =>
        cases h₃ : upperSingletonPairColor H V tUpper p.1.2 p.2 with
        | none => exact False.elim (hNot₃ h₃)
        | some c₃ =>
          by_cases hDiff : c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
          · exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_filter.mpr
                ⟨hp, c₁, c₂, c₃, hDiff.1, hDiff.2.1, hDiff.2.2,
                  h₁, h₂, h₃⟩))
          · have hRepeat : c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃ := by
              by_cases h12 : c₁ = c₂
              · exact Or.inl h12
              by_cases h13 : c₁ = c₃
              · exact Or.inr (Or.inl h13)
              right
              right
              by_contra h23
              exact hDiff ⟨h12, h13, h23⟩
            exact Finset.mem_union.mpr (Or.inl
              (Finset.mem_filter.mpr
                ⟨hp, c₁, c₂, c₃, hRepeat, h₁, h₂, h₃⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hBi | hRainbow
    · exact (Finset.mem_filter.mp hBi).1
    · exact (Finset.mem_filter.mp hRainbow).1

/-- Each bicolored triangle has at most `D₃` supporting facets, since two
    distinct colors lie in every facet. The stronger manuscript total uses
    the pinned repeated-center count across all triangles. -/
theorem upper_bicolored_triangle_facet_cell_le_three_codegree
    (H : Family α) (V : Edge α) (tUpper D₃ : ℕ)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    {p : (α × α) × α}
    (hp : p ∈ upperBicoloredTriples H V tUpper) :
    (upperTriangleFacetCell H V p).card ≤ D₃ := by
  classical
  obtain ⟨hTriangle, c₁, c₂, c₃, hRepeat, hc₁, hc₂, hc₃⟩ :=
    Finset.mem_filter.mp hp
  have hProd := (Finset.mem_filter.mp hTriangle).1
  have hVparts := Finset.mem_product.mp hProd
  have hXY := Finset.mem_product.mp hVparts.1
  have hx : p.1.1 ∈ V := hXY.1
  have hy : p.1.2 ∈ V := hXY.2
  have hz : p.2 ∈ V := hVparts.2
  have hDistinct := (Finset.mem_filter.mp hTriangle).2
  let cell := upperTriangleFacetCell H V p
  have hLabels : ∀ A ∈ cell, c₁ ∈ A ∧ c₂ ∈ A ∧ c₃ ∈ A := by
    intro A hA
    have hAparts := Finset.mem_filter.mp hA
    have hAV := (Finset.mem_powersetCard.mp hAparts.1).1
    have hAcard := (Finset.mem_powersetCard.mp hAparts.1).2
    rcases hAparts.2 with ⟨hxA, hyA, hzA, hEx, hEy, hEz⟩
    constructor
    · exact upper_pair_color_label_mem_supporting_facet H V A tUpper
        hx hy hDistinct.1 hAV hAcard hxA hyA hEx hEy hc₁
    constructor
    · exact upper_pair_color_label_mem_supporting_facet H V A tUpper
        hx hz hDistinct.2.1 hAV hAcard hxA hzA hEx hEz hc₂
    · exact upper_pair_color_label_mem_supporting_facet H V A tUpper
        hy hz hDistinct.2.2.1 hAV hAcard hyA hzA hEy hEz hc₃
  by_cases hEmpty : cell = ∅
  · change cell.card ≤ D₃
    simp [hEmpty]
  have hCellNon : cell.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hColors : ∃ c d : α, c ≠ d ∧
      (∀ A ∈ cell, c ∈ A ∧ d ∈ A) := by
    have hNotAll : c₁ ≠ c₂ ∨ c₂ ≠ c₃ := by
      have hNot := hDistinct.2.2.2.2.2.2
      simp [hc₁, hc₂, hc₃] at hNot
      exact hNot
    rcases hNotAll with h12 | h23
    · refine ⟨c₁, c₂, h12, ?_⟩
      intro A hA
      exact ⟨(hLabels A hA).1, (hLabels A hA).2.1⟩
    · refine ⟨c₂, c₃, h23, ?_⟩
      intro A hA
      exact ⟨(hLabels A hA).2.1, (hLabels A hA).2.2⟩
  obtain ⟨c, d, hcd, hBoth⟩ := hColors
  let S : Edge α := {p.1.1, c, d}
  have hXneq : p.1.1 ≠ c ∧ p.1.1 ≠ d := by
    obtain ⟨A, hA⟩ := hCellNon
    have hxA : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
    have hBothA := hBoth A hA
    exact ⟨fun h => hxA (h ▸ hBothA.1),
      fun h => hxA (h ▸ hBothA.2)⟩
  have hScard : S.card = 3 := by simp [S, hXneq.1, hXneq.2, hcd]
  have hInject : cell.card ≤ (H.filter fun E => S ⊆ E).card := by
    apply Finset.card_le_card_of_injOn (fun A => insert p.1.1 A)
    · intro A hA
      have hParts := (Finset.mem_filter.mp hA).2
      have hLab := hBoth A hA
      refine Finset.mem_filter.mpr ⟨hParts.2.2.2.1, ?_⟩
      intro v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | hv
      · exact Finset.mem_insert_self ..
      rcases hv with rfl | rfl
      · exact Finset.mem_insert_of_mem hLab.1
      · exact Finset.mem_insert_of_mem hLab.2
    · intro A hA B hB hEq
      have hxA : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
      have hxB : p.1.1 ∉ B := (Finset.mem_filter.mp hB).2.1
      have hErase := congrArg (Finset.erase · p.1.1) hEq
      simpa [hxA, hxB] using hErase
  change cell.card ≤ D₃
  exact hInject.trans (hD₃ S hScard)

noncomputable def upperBicoloredTriangleEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperBicoloredTriples H V tUpper).biUnion fun p =>
    (upperTriangleFacetCell H V p).biUnion fun A =>
      ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)

/-- An unconditional finite bicolored-triangle deletion bound. The pinned
    repeated-center argument is needed to replace the cubic triangle count
    by the sharper IV.8.2 scale. -/
theorem upper_bicolored_triangle_edges_coarse_budget
    (H : Family α) (V : Edge α) (tUpper D₃ : ℕ)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    (upperBicoloredTriangleEdges H V tUpper).card ≤
      3 * V.card ^ 3 * D₃ := by
  classical
  let T := upperBicoloredTriples H V tUpper
  let cell := upperTriangleFacetCell H V
  have hFiber : ∀ p ∈ T,
      ((cell p).biUnion fun A =>
        ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card ≤
          3 * D₃ := by
    intro p hp
    have hCap := upper_bicolored_triangle_facet_cell_le_three_codegree
      H V tUpper D₃ hD₃ hp
    calc
      _ ≤ ∑ A ∈ cell p,
          ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ cell p, 3 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Finset.card_le_three
      _ = 3 * (cell p).card := by simp [mul_comm]
      _ ≤ 3 * D₃ := Nat.mul_le_mul_left 3 hCap
  have hTriple : T.card ≤ V.card ^ 3 := by
    calc
      T.card ≤ ((V ×ˢ V) ×ˢ V).card :=
        Finset.card_le_card ((Finset.filter_subset _ _).trans
          (Finset.filter_subset _ _))
      _ = V.card ^ 3 := by simp [Finset.card_product, pow_succ]
  calc
    (upperBicoloredTriangleEdges H V tUpper).card ≤
        ∑ p ∈ T,
          ((cell p).biUnion fun A =>
            ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ T, 3 * D₃ := Finset.sum_le_sum hFiber
    _ = T.card * (3 * D₃) := by simp
    _ ≤ V.card ^ 3 * (3 * D₃) := Nat.mul_le_mul_right _ hTriple
    _ = 3 * V.card ^ 3 * D₃ := by ring

theorem upper_nonmonochromatic_triangle_edges_eq_bicolored_union_rainbow
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    upperNonmonochromaticTriangleEdges H V tUpper =
      upperBicoloredTriangleEdges H V tUpper ∪
        upperRainbowTriangleEdges H V tUpper := by
  classical
  simp [upperNonmonochromaticTriangleEdges,
    upperBicoloredTriangleEdges, upperRainbowTriangleEdges,
    upper_nonmonochromatic_triples_eq_bicolored_union_rainbow,
    Finset.union_biUnion]

/-- The actual singleton partial coloring inherits IV.7.1's pinned bound:
    after fixing one colored pair and its label, there are few further
    completion vertices carrying that same label from the first endpoint. -/
theorem upper_singleton_color_repeated_partner_bound
    (H : Family α) (V : Edge α) (tUpper D₂ D₄ : ℕ)
    (ht : 1 ≤ tUpper)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    {x y c : α} (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    (hColor : upperSingletonPairColor H V tUpper x y = some c) :
    tUpper * ((V.filter fun z => z ≠ x ∧
      upperSingletonPairColor H V tUpper x z = some c).card) ≤
        D₂ * D₄ := by
  classical
  let Z := V.filter fun z => z ≠ x ∧
    upperSingletonPairColor H V tUpper x z = some c
  have hStrongXY := (upper_singleton_pair_color_eq_some_iff_strong
    H V tUpper hx hy hxy).mp hColor
  have hCellNon : (commonPrefixTails H V ({x} : Edge α)
      ({y} : Edge α) 4).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < tUpper)
      hStrongXY.2.2.1)
  obtain ⟨A, hA⟩ := hCellNon
  have hcA : c ∈ A := hStrongXY.2.2.2.1 A hA
  have hxA : x ∉ A := by
    have hDisj := (mem_common_prefix_tails.mp hA).2.2.1
    intro hxA
    exact (Finset.disjoint_left.mp hDisj) hxA
      (Finset.mem_union_left _ (by simp))
  have hcNotX : c ∉ ({x} : Edge α) := by
    simpa using (fun h : c = x => hxA (h ▸ hcA))
  have hMap : ∀ z ∈ Z,
      ({z} : Edge α) ∈ actualCenterPartners H V ({x} : Edge α)
        1 4 tUpper c ∅ := by
    intro z hz
    have hzParts := Finset.mem_filter.mp hz
    have hStrong := (upper_singleton_pair_color_eq_some_iff_strong
      H V tUpper hx hzParts.1 hzParts.2.1.symm).mp hzParts.2.2
    exact Finset.mem_filter.mpr
      ⟨hStrong.1, hStrong, Finset.empty_subset _⟩
  have hZ : Z.card ≤
      (actualCenterPartners H V ({x} : Edge α)
        1 4 tUpper c ∅).card := by
    apply Finset.card_le_card_of_injOn (fun z => ({z} : Edge α)) hMap
    intro z hz w hw hEq
    simpa using hEq
  have hPin := repeated_center_partner_bound_from_codegrees
    H V ({x} : Edge α) 1 4 tUpper c ∅ 0 D₂ D₄
    (by simp) hcNotX (by simp) hD₂ hD₄
  exact (Nat.mul_le_mul_left tUpper hZ).trans hPin

/-- Bicolored triangles oriented so that the two edges incident to the first
    completion vertex carry the repeated color. -/
noncomputable def upperBicoloredFirstTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact (upperBicoloredTriples H V tUpper).filter fun p =>
    upperSingletonPairColor H V tUpper p.1.1 p.1.2 =
      upperSingletonPairColor H V tUpper p.1.1 p.2

/-- The pinned IV.7.1 bound, summed over all ordered choices of the
    repeated-color vertex and one neighboring completion, pays for all
    supported bicolored triangles in this orientation. -/
theorem upper_bicolored_first_triangle_weighted_budget
    (H : Family α) (V : Edge α) (tUpper D₂ D₃ D₄ : ℕ)
    (ht : 1 ≤ tUpper)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tUpper * (∑ p ∈ upperBicoloredFirstTriples H V tUpper,
      (upperTriangleFacetCell H V p).card) ≤
      V.card ^ 2 * D₂ * D₃ * D₄ := by
  classical
  let T := upperBicoloredFirstTriples H V tUpper
  let pairs := V ×ˢ V
  let cell := upperTriangleFacetCell H V
  change tUpper * (∑ p ∈ T, (cell p).card) ≤
    V.card ^ 2 * D₂ * D₃ * D₄
  have hMap : ∀ p ∈ T, p.1 ∈ pairs := by
    intro p hp
    have hBi := (Finset.mem_filter.mp hp).1
    have hTri := (Finset.mem_filter.mp hBi).1
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hTri).1).1
  have hOne : ∀ xy ∈ pairs,
      tUpper * (∑ p ∈ T.filter fun p => p.1 = xy, (cell p).card) ≤
        D₂ * D₃ * D₄ := by
    intro xy hxy
    let F := T.filter fun p => p.1 = xy
    by_cases hEmpty : F = ∅
    · simp [F, hEmpty]
    obtain ⟨p₀, hp₀⟩ : F.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hp₀T : p₀ ∈ T := (Finset.mem_filter.mp hp₀).1
    have hp₀eq : p₀.1 = xy := (Finset.mem_filter.mp hp₀).2
    have hTri₀ := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hp₀T).1).1
    have hColorNot : upperSingletonPairColor H V tUpper
      xy.1 xy.2 ≠ none := by
      simpa [← hp₀eq] using
        (Finset.mem_filter.mp hTri₀).2.2.2.2.1
    obtain ⟨c, hc⟩ : ∃ c : α,
        upperSingletonPairColor H V tUpper xy.1 xy.2 = some c := by
      cases h : upperSingletonPairColor H V tUpper xy.1 xy.2 with
      | none => exact False.elim (hColorNot h)
      | some c => exact ⟨c, rfl⟩
    have hxyV := Finset.mem_product.mp hxy
    have hxyNe : xy.1 ≠ xy.2 := by
      simpa [← hp₀eq] using
        (Finset.mem_filter.mp hTri₀).2.1
    let Z := V.filter fun z => z ≠ xy.1 ∧
      upperSingletonPairColor H V tUpper xy.1 z = some c
    have hFsub : F.card ≤ Z.card := by
      apply Finset.card_le_card_of_injOn (fun p => p.2)
      · intro p hp
        have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hpEq : p.1 = xy := (Finset.mem_filter.mp hp).2
        have hpBi := (Finset.mem_filter.mp hpT).1
        have hpTri := (Finset.mem_filter.mp hpBi).1
        have hpV := (Finset.mem_product.mp
          (Finset.mem_filter.mp hpTri).1).2
        have hpNe := (Finset.mem_filter.mp hpTri).2.2.1
        have hpColor := (Finset.mem_filter.mp hpT).2
        apply Finset.mem_filter.mpr
        refine ⟨hpV, ?_, ?_⟩
        · simpa [← hpEq] using hpNe.symm
        · have hEqColor : upperSingletonPairColor H V tUpper
              xy.1 xy.2 = upperSingletonPairColor H V tUpper xy.1 p.2 := by
            simpa [hpEq] using hpColor
          exact hc ▸ hEqColor.symm
      · intro p hp q hq hEq
        have hpEq : p.1 = xy := (Finset.mem_filter.mp hp).2
        have hqEq : q.1 = xy := (Finset.mem_filter.mp hq).2
        exact Prod.ext (hpEq.trans hqEq.symm) hEq
    have hPinned := upper_singleton_color_repeated_partner_bound
      H V tUpper D₂ D₄ ht hD₂ hD₄
      hxyV.1 hxyV.2 hxyNe hc
    have hFweighted : tUpper * F.card ≤ D₂ * D₄ :=
      (Nat.mul_le_mul_left tUpper hFsub).trans hPinned
    have hCellSum : (∑ p ∈ F, (cell p).card) ≤ F.card * D₃ := by
      calc
        _ ≤ ∑ _p ∈ F, D₃ := by
          apply Finset.sum_le_sum
          intro p hp
          exact upper_bicolored_triangle_facet_cell_le_three_codegree
            H V tUpper D₃ hD₃ (Finset.mem_filter.mp
              (Finset.mem_filter.mp hp).1).1
        _ = F.card * D₃ := by simp
    calc
      tUpper * (∑ p ∈ F, (cell p).card) ≤
          tUpper * (F.card * D₃) := Nat.mul_le_mul_left _ hCellSum
      _ = (tUpper * F.card) * D₃ := by ring
      _ ≤ (D₂ * D₄) * D₃ := Nat.mul_le_mul_right D₃ hFweighted
      _ = D₂ * D₃ * D₄ := by ring
  have hReindex := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := pairs) hMap (fun p => (cell p).card)
  calc
    tUpper * (∑ p ∈ T, (cell p).card) =
        ∑ xy ∈ pairs,
          tUpper * (∑ p ∈ T.filter fun p => p.1 = xy, (cell p).card) := by
      rw [← hReindex, Finset.mul_sum]
    _ ≤ ∑ _xy ∈ pairs, D₂ * D₃ * D₄ := Finset.sum_le_sum hOne
    _ = pairs.card * (D₂ * D₃ * D₄) := by simp
    _ = V.card ^ 2 * D₂ * D₃ * D₄ := by
      simp [pairs, Finset.card_product, pow_two]
      ring

/-- The actual upper-facet deletion set: remove edges participating in an
    uncolored pair or a fully colored nonmonochromatic triangle. -/
noncomputable def upperFacetColorCleanupEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact upperUncoloredFacetEdges H V tUpper ∪
    upperNonmonochromaticTriangleEdges H V tUpper

/-- A finite IV.8 upper-facet deletion budget. The bicolored term uses the
    coarse per-triangle bound; the pinned first-orientation result above is
    the input for replacing that term by the manuscript's sharp scale. -/
theorem upper_facet_color_cleanup_edges_coarse_budget
    (H : Family α) (V : Edge α) (tUpper D D₃ D₄ : ℕ)
    (hAdm : Admissible H)
    (hPairCap : ∀ x : α, ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => ({x} : Edge α) ∪ Q ⊆ E).card ≤ D)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (upperFacetColorCleanupEdges H V tUpper).card ≤
      2 * V.card ^ 2 * (tUpper + 16 * D) +
        3 * V.card ^ 3 * D₃ + 3 * V.card ^ 3 * D₄ := by
  have hU := upper_uncolored_facet_edges_actual_budget
    H V tUpper D hAdm hPairCap
  have hB := upper_bicolored_triangle_edges_coarse_budget
    H V tUpper D₃ hD₃
  have hR := upper_rainbow_triangle_edges_actual_budget
    H V tUpper D₄ hD₄
  rw [upperFacetColorCleanupEdges,
    upper_nonmonochromatic_triangle_edges_eq_bicolored_union_rainbow]
  have hUnion₁ := Finset.card_union_le
    (upperUncoloredFacetEdges H V tUpper)
    (upperBicoloredTriangleEdges H V tUpper ∪
      upperRainbowTriangleEdges H V tUpper)
  have hUnion₂ := Finset.card_union_le
    (upperBicoloredTriangleEdges H V tUpper)
    (upperRainbowTriangleEdges H V tUpper)
  omega

/-- Every pair of surviving completions of an actual four-facet is colored
    after deleting the uncolored-pair edges. -/
theorem upper_facet_pair_colored_of_uncolored_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (upperUncoloredFacetEdges H V tUpper))
    (hAV : A ⊆ V) (hAcard : A.card = 4)
    {x y : α} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : x ≠ y) (hxA : x ∉ A) (hyA : y ∉ A)
    (hEx : insert x A ∈ K) (hEy : insert y A ∈ K) :
    upperSingletonPairColor H V tUpper x y ≠ none := by
  classical
  intro hNone
  have hPair : (x, y) ∈ upperUncoloredPairs H V tUpper :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy, hNone⟩
  have hCell : A ∈ commonPrefixTails H V
      ({x} : Edge α) ({y} : Edge α) 4 := by
    apply mem_common_prefix_tails.mpr
    refine ⟨hAV, hAcard, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hvA hv
      simp only [Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxA hvA
      · exact hyA hvA
    · simpa using hKH hEx
    · simpa using hKH hEy
  have hDeleted : insert x A ∈ upperUncoloredFacetEdges H V tUpper := by
    unfold upperUncoloredFacetEdges
    exact Finset.mem_biUnion.mpr
      ⟨(x, y), hPair, Finset.mem_biUnion.mpr
        ⟨A, hCell, by simp⟩⟩
  exact (Finset.disjoint_left.mp hSurvive) hEx hDeleted

/-- After deleting all colored nonmonochromatic triangles, three surviving
    completions of the same facet have one common actual pair color. -/
theorem upper_facet_triangle_monochromatic_of_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hAV : A ⊆ V) (hAcard : A.card = 4)
    {x y z : α} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxA : x ∉ A) (hyA : y ∉ A) (hzA : z ∉ A)
    (hEx : insert x A ∈ K) (hEy : insert y A ∈ K)
    (hEz : insert z A ∈ K) :
    upperSingletonPairColor H V tUpper x y =
        upperSingletonPairColor H V tUpper x z ∧
      upperSingletonPairColor H V tUpper x z =
        upperSingletonPairColor H V tUpper y z := by
  classical
  have hNoU : Disjoint K (upperUncoloredFacetEdges H V tUpper) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hSurvive
  have hCxy := upper_facet_pair_colored_of_uncolored_cleanup
    K H V A tUpper hKH hNoU hAV hAcard
    hx hy hxy hxA hyA hEx hEy
  have hCxz := upper_facet_pair_colored_of_uncolored_cleanup
    K H V A tUpper hKH hNoU hAV hAcard
    hx hz hxz hxA hzA hEx hEz
  have hCyz := upper_facet_pair_colored_of_uncolored_cleanup
    K H V A tUpper hKH hNoU hAV hAcard
    hy hz hyz hyA hzA hEy hEz
  by_contra hNonmono
  have hTriangle : ((x, y), z) ∈
      upperNonmonochromaticTriples H V tUpper := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩,
        hxy, hxz, hyz, hCxy, hCxz, hCyz, ?_⟩
    exact not_and_or.mp hNonmono
  have hCell : A ∈ upperTriangleFacetCell H V ((x, y), z) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hAV, hAcard⟩,
        hxA, hyA, hzA, hKH hEx, hKH hEy, hKH hEz⟩
  have hDeleted : insert x A ∈
      upperNonmonochromaticTriangleEdges H V tUpper := by
    unfold upperNonmonochromaticTriangleEdges
    exact Finset.mem_biUnion.mpr
      ⟨((x, y), z), hTriangle, Finset.mem_biUnion.mpr
        ⟨A, hCell, by simp⟩⟩
  exact (Finset.disjoint_left.mp hSurvive) hEx
    (Finset.mem_union_right _ hDeleted)

/-- The surviving completions of every still-shared facet have one actual
    strong-pair label, and that label lies in the facet. This constructs the
    center asserted in IV.8 from the explicit pair/triangle deletion set. -/
theorem upper_facet_color_center_exists_of_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hAV : A ⊆ V) (hAcard : A.card = 4)
    (hShared : 2 ≤ (V.filter fun x => x ∉ A ∧ insert x A ∈ K).card) :
    ∃ c ∈ A,
      ∀ x ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
        ∀ y ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
          x ≠ y → upperSingletonPairColor H V tUpper x y = some c := by
  classical
  let S := V.filter fun x => x ∉ A ∧ insert x A ∈ K
  have hS : 1 < S.card := by
    change 2 ≤ S.card at hShared
    omega
  obtain ⟨x, hx⟩ : S.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne hS x
  have hxy : x ≠ y := Ne.symm hyx
  have hParts : ∀ w ∈ S, w ∈ V ∧ w ∉ A ∧ insert w A ∈ K := by
    intro w hw
    exact Finset.mem_filter.mp hw
  have hNoU : Disjoint K (upperUncoloredFacetEdges H V tUpper) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hSurvive
  have hColorXY := upper_facet_pair_colored_of_uncolored_cleanup
    K H V A tUpper hKH hNoU hAV hAcard
    (hParts x hx).1 (hParts y hy).1 hxy
    (hParts x hx).2.1 (hParts y hy).2.1
    (hParts x hx).2.2 (hParts y hy).2.2
  obtain ⟨c, hc⟩ : ∃ c : α,
      upperSingletonPairColor H V tUpper x y = some c := by
    cases h : upperSingletonPairColor H V tUpper x y with
    | none => exact False.elim (hColorXY h)
    | some c => exact ⟨c, rfl⟩
  have hcA := upper_pair_color_label_mem_supporting_facet
    H V A tUpper (hParts x hx).1 (hParts y hy).1 hxy
    hAV hAcard (hParts x hx).2.1 (hParts y hy).2.1
    (hKH (hParts x hx).2.2) (hKH (hParts y hy).2.2) hc
  have hFromX : ∀ z ∈ S, z ≠ x →
      upperSingletonPairColor H V tUpper x z = some c := by
    intro z hz hzx
    by_cases hzy : z = y
    · simpa [hzy] using hc
    have hTri := upper_facet_triangle_monochromatic_of_cleanup
      K H V A tUpper hKH hSurvive hAV hAcard
      (hParts x hx).1 (hParts y hy).1 (hParts z hz).1
      hxy (Ne.symm hzx) (Ne.symm hzy)
      (hParts x hx).2.1 (hParts y hy).2.1 (hParts z hz).2.1
      (hParts x hx).2.2 (hParts y hy).2.2 (hParts z hz).2.2
    exact hTri.1.symm.trans hc
  refine ⟨c, hcA, ?_⟩
  intro u hu v hv huv
  by_cases hux : u = x
  · subst u
    exact hFromX v hv (Ne.symm huv)
  by_cases hvx : v = x
  · subst v
    rw [upper_singleton_pair_color_symm]
    exact hFromX u hu hux
  have hTri := upper_facet_triangle_monochromatic_of_cleanup
    K H V A tUpper hKH hSurvive hAV hAcard
    (hParts x hx).1 (hParts u hu).1 (hParts v hv).1
    (Ne.symm hux) (Ne.symm hvx) huv
    (hParts x hx).2.1 (hParts u hu).2.1 (hParts v hv).2.1
    (hParts x hx).2.2 (hParts u hu).2.2 (hParts v hv).2.2
  exact hTri.2.symm.trans (hFromX v hv hvx)

/-- For a uniform five-family, four-face parent edges and their ambient
    completion vertices are in bijection. -/
theorem facet_completion_vertices_card_eq_parent_degree
    (K : Family α) (V A : Edge α)
    (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hAcard : A.card = 4) :
    (V.filter fun x => x ∉ A ∧ insert x A ∈ K).card =
      (facetParents K A).card := by
  classical
  let S := V.filter fun x => x ∉ A ∧ insert x A ∈ K
  have hImage : S.image (fun x => insert x A) = facetParents K A := by
    ext E
    constructor
    · intro hE
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).2.2, Finset.subset_insert _ _⟩
    · intro hE
      have hParts := Finset.mem_filter.mp hE
      have hDiffCard : (E \ A).card = 1 := by
        rw [Finset.card_sdiff_of_subset hParts.2, hUniformK hParts.1]
        omega
      obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hDiffCard
      have hxDiff : x ∈ E \ A := by rw [hxEq]; simp
      have hxE : x ∈ E := (Finset.mem_sdiff.mp hxDiff).1
      have hxNotA : x ∉ A := (Finset.mem_sdiff.mp hxDiff).2
      have hRecon : insert x A = E := by
        have hUnion := Finset.union_sdiff_of_subset hParts.2
        rw [hxEq] at hUnion
        simpa [Finset.union_singleton] using hUnion
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr
          ⟨hAmbientK E hParts.1 hxE, hxNotA, hRecon ▸ hParts.1⟩,
          hRecon⟩
  rw [← hImage]
  exact (Finset.card_image_iff.mpr (by
    intro x hx y hy hEq
    have hxNotA : x ∉ A := (Finset.mem_filter.mp hx).2.1
    change insert x A = insert y A at hEq
    have hxin : x ∈ insert y A := by
      rw [← hEq]
      exact Finset.mem_insert_self ..
    rcases Finset.mem_insert.mp hxin with hxy | hxA
    · exact hxy
    · exact False.elim (hxNotA hxA))).symm

/-- The IV.8 center exists on every four-face still shared after actual
    pair and triangle cleanup. -/
theorem upper_shared_facet_color_center_exists_of_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hShared : A ∈ sharedFourShadow K) :
    ∃ c ∈ A,
      ∀ x ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
        ∀ y ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
          x ≠ y → upperSingletonPairColor H V tUpper x y = some c := by
  have hSharedParts := Finset.mem_filter.mp hShared
  obtain ⟨E, hE, hAE, hAcard⟩ :=
    (mem_four_shadow_iff_parent K A).mp hSharedParts.1
  have hAV : A ⊆ V := hAE.trans (hAmbientK E hE)
  have hS : 2 ≤ (V.filter fun x => x ∉ A ∧ insert x A ∈ K).card := by
    rw [facet_completion_vertices_card_eq_parent_degree K V A
      hUniformK hAmbientK hAcard]
    exact hSharedParts.2
  exact upper_facet_color_center_exists_of_cleanup K H V A tUpper
    hKH hSurvive hAV hAcard hS

/-- The center selected by actual IV.8 cleanup on shared facets. On other
    faces its value is immaterial. -/
noncomputable def upperFacetColorCenter
    [Nonempty α] (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (A : Edge α) : α := by
  classical
  if hA : A ∈ sharedFourShadow K then
    exact Classical.choose
      (upper_shared_facet_color_center_exists_of_cleanup
        K H V A tUpper hKH hUniformK hAmbientK hSurvive hA)
  else
    exact arbitrarySharedFacetCenter K A

theorem upper_facet_color_center_spec
    [Nonempty α] (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    {A : Edge α} (hA : A ∈ sharedFourShadow K) :
    upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK
      hSurvive A ∈ A ∧
    ∀ x ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
      ∀ y ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
        x ≠ y → upperSingletonPairColor H V tUpper x y =
          some (upperFacetColorCenter K H V tUpper
            hKH hUniformK hAmbientK hSurvive A) := by
  classical
  unfold upperFacetColorCenter
  simp only [dite_eq_left hA]
  exact Classical.choose_spec
    (upper_shared_facet_color_center_exists_of_cleanup
      K H V A tUpper hKH hUniformK hAmbientK hSurvive hA)

/-- A second root at a bad facet produces the two distinct singleton
    completion vertices of the upper four-face. -/
theorem facet_second_root_upper_completion_vertices
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ facetBadIncidences K V facetCenter tripleLabel)
    {R₁ : Edge α} (hR₁ : R₁ ∈ facetWitnessSecondRoots K V i) :
    ∃ x y : α,
      x ≠ y ∧
      (facetWitnessRoot i).erase i.2 = {x} ∧
      R₁.erase i.2 = {y} ∧
      x ∈ V.filter (fun w => w ∉ i.1.2 ∧ insert w i.1.2 ∈ K) ∧
      y ∈ V.filter (fun w => w ∉ i.1.2 ∧ insert w i.1.2 ∈ K) := by
  classical
  let A := i.1.2
  let a := i.2
  let B := facetWitnessCore i
  let R₀ := facetWitnessRoot i
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have haA : a ∈ A := (Finset.mem_filter.mp hi).2.2.2.1
  have hAeq : A = B ∪ {a} := by
    change i.1.2 = (i.1.2.erase a) ∪ {a}
    simpa [Finset.union_singleton] using (Finset.insert_erase haA).symm
  have hBE : B ⊆ i.1.1 :=
    (Finset.erase_subset a i.1.2).trans (Finset.mem_filter.mp hi).2.1
  have hEeq : i.1.1 = B ∪ R₀ :=
    (Finset.union_sdiff_of_subset hBE).symm
  have hR₀link := facet_bad_incidence_first_root_mem_pair_link K V
    facetCenter tripleLabel hUniformK hAmbientK hi
  have hR₁link : R₁ ∈ parentPairLink K V B :=
    (Finset.mem_filter.mp hR₁).1
  have hR₀parts := mem_parent_pair_link.mp hR₀link
  have hR₁parts := mem_parent_pair_link.mp hR₁link
  have hInter : R₀ ∩ R₁ = {a} := (Finset.mem_filter.mp hR₁).2
  have haR₀ : a ∈ R₀ := by
    have h : a ∈ R₀ ∩ R₁ := by rw [hInter]; simp
    exact (Finset.mem_inter.mp h).1
  have haR₁ : a ∈ R₁ := by
    have h : a ∈ R₀ ∩ R₁ := by rw [hInter]; simp
    exact (Finset.mem_inter.mp h).2
  have hR₀erase : (R₀.erase a).card = 1 := by
    have hCard := Finset.card_erase_add_one haR₀
    have hTwo : R₀.card = 2 := hR₀parts.2.1
    omega
  have hR₁erase : (R₁.erase a).card = 1 := by
    have hCard := Finset.card_erase_add_one haR₁
    have hTwo : R₁.card = 2 := hR₁parts.2.1
    omega
  obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hR₀erase
  obtain ⟨y, hyEq⟩ := Finset.card_eq_one.mp hR₁erase
  have hxR₀ : x ∈ R₀ := by
    have hx : x ∈ R₀.erase a := by rw [hxEq]; simp
    exact Finset.mem_of_mem_erase hx
  have hyR₁ : y ∈ R₁ := by
    have hy : y ∈ R₁.erase a := by rw [hyEq]; simp
    exact Finset.mem_of_mem_erase hy
  have hxa : x ≠ a := by
    have hx : x ∈ R₀.erase a := by rw [hxEq]; simp
    exact (Finset.mem_erase.mp hx).1
  have hya : y ≠ a := by
    have hy : y ∈ R₁.erase a := by rw [hyEq]; simp
    exact (Finset.mem_erase.mp hy).1
  have hxy : x ≠ y := by
    intro h
    have hxInter : x ∈ R₀ ∩ R₁ :=
      Finset.mem_inter.mpr ⟨hxR₀, h ▸ hyR₁⟩
    have hxa' : x = a := by
      rw [hInter] at hxInter
      exact Finset.mem_singleton.mp hxInter
    exact hxa hxa'
  have hxNotA : x ∉ A := by
    rw [hAeq]
    intro hx
    rcases Finset.mem_union.mp hx with hxB | hxa'
    · exact (Finset.disjoint_left.mp hR₀parts.2.2.1) hxR₀ hxB
    · exact hxa (Finset.mem_singleton.mp hxa')
  have hyNotA : y ∉ A := by
    rw [hAeq]
    intro hy
    rcases Finset.mem_union.mp hy with hyB | hya'
    · exact (Finset.disjoint_left.mp hR₁parts.2.2.1) hyR₁ hyB
    · exact hya (Finset.mem_singleton.mp hya')
  have hR₀eq : R₀ = {a, x} := by
    have hIns := Finset.insert_erase haR₀
    rw [hxEq] at hIns
    simpa [Finset.insert_comm] using hIns.symm
  have hR₁eq : R₁ = {a, y} := by
    have hIns := Finset.insert_erase haR₁
    rw [hyEq] at hIns
    simpa [Finset.insert_comm] using hIns.symm
  have hEx : insert x A ∈ K := by
    have hRecon : insert x A = i.1.1 := by
      rw [hAeq, hEeq, hR₀eq]
      ext v
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    exact hRecon.symm ▸ hE
  have hEy : insert y A ∈ K := by
    have hRecon : insert y A = B ∪ R₁ := by
      rw [hAeq, hR₁eq]
      ext v
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      tauto
    exact hRecon.symm ▸ hR₁parts.2.2.2
  refine ⟨x, y, hxy, hxEq, hyEq, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hR₀parts.1 hxR₀, hxNotA, hEx⟩
  · exact Finset.mem_filter.mpr ⟨hR₁parts.1 hyR₁, hyNotA, hEy⟩

/-- The actual IV.8 pair/triangle deletion construction supplies the
    `hFacetStrong` premise in IV.9.3 for its selected shared-facet centers. -/
theorem facet_upper_strong_of_actual_facet_color_cleanup
    [Nonempty α]
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges H V tUpper))
    (hI : I ⊆ facetBadIncidences K V
      (upperFacetColorCenter K H V tUpper hKH hUniformK hAmbientK hSurvive)
      tripleLabel) :
    ∀ i ∈ I,
      ∀ R₁ ∈ facetWitnessSecondRoots K V i,
        ActualStrongPartner H V
          ((facetWitnessRoot i).erase i.2) (R₁.erase i.2)
          1 4 tUpper
            (upperFacetColorCenter K H V tUpper
              hKH hUniformK hAmbientK hSurvive i.1.2) := by
  classical
  intro i hi R₁ hR₁
  let center := upperFacetColorCenter K H V tUpper
    hKH hUniformK hAmbientK hSurvive
  have hBad := hI hi
  have hShared : i.1.2 ∈ sharedFourShadow K :=
    (Finset.mem_filter.mp hBad).2.2.1
  obtain ⟨x, y, hxy, hxEq, hyEq, hxS, hyS⟩ :=
    facet_second_root_upper_completion_vertices K V center
      tripleLabel hUniformK hAmbientK hBad hR₁
  have hCenter := upper_facet_color_center_spec K H V tUpper
    hKH hUniformK hAmbientK hSurvive hShared
  have hColor := hCenter.2 x hxS y hyS hxy
  have hxV : x ∈ V := (Finset.mem_filter.mp hxS).1
  have hyV : y ∈ V := (Finset.mem_filter.mp hyS).1
  have hStrong := (upper_singleton_pair_color_eq_some_iff_strong
    H V tUpper hxV hyV hxy).mp hColor
  simpa [hxEq, hyEq, center] using hStrong

/-- Parent edges incident to an upper facet pair whose actual common-prefix
    cell fails to have the assigned strong color. This is the precise failure
    set removed by the upper-pair part of IV.8. -/
noncomputable def upperFacetNonStrongEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    (facetCenter : Edge α → α) : Family α := by
  classical
  exact H.filter fun E =>
    ∃ B R₀ R₁ : Edge α, ∃ a : α,
      E = B ∪ R₀ ∧
      R₀ ∈ parentPairLink H V B ∧
      R₁ ∈ parentPairLink H V B ∧
      R₀ ∩ R₁ = {a} ∧
      ¬ ActualStrongPartner H V
        (R₀.erase a) (R₁.erase a) 1 4 tUpper
          (facetCenter (B ∪ {a}))

/-- Ordered parent-edge pairs exposing the actual upper-facet strong-color
    failures. This is the incidence set whose size IV.8 must charge to
    uncolored pairs and nonmonochromatic completion triangles. -/
noncomputable def upperFacetNonStrongPairs
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    (facetCenter : Edge α → α) : Finset (Edge α × Edge α) := by
  classical
  exact (H ×ˢ H).filter fun p =>
    ∃ B R₀ R₁ : Edge α, ∃ a : α,
      p.1 = B ∪ R₀ ∧ p.2 = B ∪ R₁ ∧
      R₀ ∈ parentPairLink H V B ∧
      R₁ ∈ parentPairLink H V B ∧
      R₀ ∩ R₁ = {a} ∧
      ¬ ActualStrongPartner H V
        (R₀.erase a) (R₁.erase a) 1 4 tUpper
          (facetCenter (B ∪ {a}))

/-- The upper-facet deletion set is the first projection of its ordered
    failure incidences. Hence any IV.8 bound for the latter pays for every
    edge that the witness argument needs removed. -/
theorem upper_facet_non_strong_edges_eq_pair_projection
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    (facetCenter : Edge α → α) :
    upperFacetNonStrongEdges H V tUpper facetCenter =
      (upperFacetNonStrongPairs H V tUpper facetCenter).image Prod.fst := by
  classical
  ext E
  constructor
  · intro hE
    obtain ⟨hEH, B, R₀, R₁, a, hEq, hR₀, hR₁, hInt, hFail⟩ :=
      Finset.mem_filter.mp hE
    have hF : B ∪ R₁ ∈ H := (mem_parent_pair_link.mp hR₁).2.2.2
    exact Finset.mem_image.mpr
      ⟨(E, B ∪ R₁), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hEH, hF⟩,
          ⟨B, R₀, R₁, a, hEq, rfl, hR₀, hR₁, hInt, hFail⟩⟩, rfl⟩
  · intro hE
    obtain ⟨p, hp, hpE⟩ := Finset.mem_image.mp hE
    obtain ⟨hProd, B, R₀, R₁, a, hEq, _hF, hR₀, hR₁, hInt, hFail⟩ :=
      Finset.mem_filter.mp hp
    have hEH : E ∈ H := hpE ▸ (Finset.mem_product.mp hProd).1
    exact Finset.mem_filter.mpr
      ⟨hEH, B, R₀, R₁, a, hpE ▸ hEq, hR₀, hR₁, hInt, hFail⟩

theorem upper_facet_non_strong_edges_card_le_pair_incidences
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    (facetCenter : Edge α → α) :
    (upperFacetNonStrongEdges H V tUpper facetCenter).card ≤
      (upperFacetNonStrongPairs H V tUpper facetCenter).card := by
  rw [upper_facet_non_strong_edges_eq_pair_projection]
  exact Finset.card_image_le

/-- Avoiding the actual upper-pair failure edges gives exactly the
    `hFacetStrong` predicate consumed by the IV.9.3 witness reindexing. -/
theorem facet_upper_strong_of_non_strong_edge_cleanup
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hSurvive : Disjoint K
      (upperFacetNonStrongEdges H V tUpper facetCenter)) :
    ∀ i ∈ I, ∀ R₁ ∈ facetWitnessSecondRoots K V i,
      ActualStrongPartner H V
        ((facetWitnessRoot i).erase i.2) (R₁.erase i.2)
        1 4 tUpper (facetCenter i.1.2) := by
  classical
  intro i hi R₁ hR₁
  let B := facetWitnessCore i
  let R₀ := facetWitnessRoot i
  let a := i.2
  have hBad := hI hi
  have hSource := (Finset.mem_filter.mp hBad).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have ha : a ∈ i.1.2 := (Finset.mem_filter.mp hBad).2.2.2.1
  have hAeq : i.1.2 = B ∪ {a} := by
    change i.1.2 = (i.1.2.erase a) ∪ {a}
    simpa [Finset.union_singleton] using (Finset.insert_erase ha).symm
  have hBE : B ⊆ i.1.1 :=
    (Finset.erase_subset a i.1.2).trans
      (Finset.mem_filter.mp hBad).2.1
  have hEeq : i.1.1 = B ∪ R₀ := by
    exact (Finset.union_sdiff_of_subset hBE).symm
  have hR₀K := facet_bad_incidence_first_root_mem_pair_link K V
    facetCenter tripleLabel hUniformK hAmbientK hBad
  have hR₁K : R₁ ∈ parentPairLink K V B :=
    (Finset.mem_filter.mp hR₁).1
  have hLinkH : ∀ R ∈ parentPairLink K V B,
      R ∈ parentPairLink H V B := by
    intro R hR
    have hParts := mem_parent_pair_link.mp hR
    exact mem_parent_pair_link.mpr
      ⟨hParts.1, hParts.2.1, hParts.2.2.1, hKH hParts.2.2.2⟩
  by_contra hNotStrong
  have hFail : i.1.1 ∈ upperFacetNonStrongEdges H V tUpper facetCenter := by
    apply Finset.mem_filter.mpr
    refine ⟨hKH hE, B, R₀, R₁, a, hEeq, hLinkH R₀ hR₀K,
      hLinkH R₁ hR₁K, (Finset.mem_filter.mp hR₁).2, ?_⟩
    simpa [hAeq, B, R₀, a] using hNotStrong
  exact (Finset.disjoint_left.mp hSurvive) hE hFail

/-- IV.9.4's finite budget after dividing the bad incidences into two
    low-retention classes and the class handled by the witness count. -/
theorem facet_bad_incidence_combined_budget
    (K H : Family α) (V : Edge α) (P Q t L₄ L₃ D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hUniformH : Uniform 5 H)
    (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hA : ∀ i ∈ highRetentionBadIncidences K H V P Q facetCenter tripleLabel,
      L₄ ≤ (facetParents K i.1.2).card)
    (hB : ∀ i ∈ highRetentionBadIncidences K H V P Q facetCenter tripleLabel,
      L₃ ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hWeighted : t * (∑ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel,
        (facetParents K i.1.2).card *
          (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) :
    Q * (t * (L₄ * L₃) *
      (facetBadIncidences K V facetCenter tripleLabel).card) ≤
      t * (L₄ * L₃) * (40 * P * H.card) +
        Q * (8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) := by
  classical
  let low := lowEitherBadIncidences K H V P Q facetCenter tripleLabel
  let high := highRetentionBadIncidences K H V P Q facetCenter tripleLabel
  let badI := facetBadIncidences K V facetCenter tripleLabel
  let M := t * (L₄ * L₃)
  let W := 8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄
  have hLowSub : low ⊆ badI := by
    intro i hi
    rcases Finset.mem_union.mp hi with hFacet | hTriple
    · exact (Finset.mem_filter.mp hFacet).1
    · exact (Finset.mem_filter.mp hTriple).1
  have hPartition : high.card + low.card = badI.card := by
    simpa [high, highRetentionBadIncidences, badI] using
      Finset.card_sdiff_add_card_eq_card hLowSub
  have hLow : Q * low.card ≤ 40 * P * H.card :=
    low_either_bad_incidence_budget K H V P Q
      facetCenter tripleLabel hKH hUniformK hUniformH hAmbientH
  have hHigh : M * high.card ≤ W := by
    simpa [M, high, W, mul_assoc] using
      facet_high_retention_incidence_card_bound high K V
        t L₄ L₃ D₃ D₄ hA hB hWeighted
  calc
    Q * (M * badI.card) = M * (Q * low.card) + Q * (M * high.card) := by
      rw [← hPartition]
      ring
    _ ≤ M * (40 * P * H.card) + Q * W :=
      Nat.add_le_add (Nat.mul_le_mul_left M hLow)
        (Nat.mul_le_mul_left Q hHigh)

/-- IV.9.3 with the first/second-root cleanup premise discharged by the
    actual IV.7 edge deletion set. -/
theorem facet_inheritance_weighted_incidence_bound_of_cleanup
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (C : Family α)
    (tLower tUpper u q D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
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
    (hC : ∀ i ∈ I, facetWitnessCore i ∈ C)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V C 2 u q
        (fun B P T => ¬ ActualStrongPartner H V P T 2 3 tLower
          (tripleLabel B))))
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tLower * (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by
  apply facet_inheritance_weighted_incidence_bound I K H V
    tLower tUpper u q D₃ D₄ facetCenter tripleLabel
    hI hKH hUniformK hAmbientK hFacetCenter hTripleLabels
    hFacetStrong hDegree
  · exact facet_bad_incidence_roots_survive_multilevel_cleanup
      I K H V C u q
      (fun B P T => ¬ ActualStrongPartner H V P T 2 3 tLower
        (tripleLabel B))
      facetCenter tripleLabel hI hKH hUniformK hAmbientK hC hSurvive
  · exact ht
  · exact hD₃
  · exact hD₄

omit [DecidableEq α] in
/-- IV.9.4's natural codegree substitution in the facet case: the pinned
    witness numerator is at most `8 R³ n⁵`. -/
theorem facet_pinned_witness_natural_codegree_bound
    (V : Edge α) (n R D₃ D₄ : ℕ)
    (hV : V.card ≤ n)
    (hD₃ : D₃ ≤ R * n)
    (hD₄ : D₄ ≤ R) :
    8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ ≤
      8 * R ^ 3 * n ^ 5 := by
  have hPairs : (V.powersetCard 2).card ≤ n ^ 2 := by
    rw [Finset.card_powersetCard]
    exact (Nat.choose_le_pow V.card 2).trans
      (Nat.pow_le_pow_left hV 2)
  calc
    8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ ≤
        8 * (n ^ 2) ^ 2 * (R * n) * R * R := by gcongr
    _ = 8 * R ^ 3 * n ^ 5 := by ring

/-- The high-retention incidence count after substituting the natural
    rank-five codegree bounds. -/
theorem facet_high_retention_incidence_natural_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K : Family α) (V : Edge α)
    (n R t L₄ L₃ D₃ D₄ : ℕ)
    (hV : V.card ≤ n)
    (hD₃ : D₃ ≤ R * n) (hD₄ : D₄ ≤ R)
    (hA : ∀ i ∈ I, L₄ ≤ (facetParents K i.1.2).card)
    (hB : ∀ i ∈ I,
      L₃ ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hWeighted : t * (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄) :
    t * (L₄ * L₃ * I.card) ≤ 8 * R ^ 3 * n ^ 5 := by
  exact (facet_high_retention_incidence_card_bound I K V
    t L₄ L₃ D₃ D₄ hA hB hWeighted).trans
      (facet_pinned_witness_natural_codegree_bound V n R D₃ D₄
        hV hD₃ hD₄)

/-- IV.9.3 specialized to the high-retention class, with the IV.7 and IV.8
    partner guarantees derived from two actual edge-deletion sets. The
    remaining numeric input is the original triple-core degree threshold. -/
theorem facet_high_retention_weighted_bound_of_cleanups
    (K H : Family α) (V : Edge α) (C : Family α)
    (P Q L₃ tLower tUpper u q D₃ D₄ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform 5 K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hQ : 0 < Q)
    (hMinTriple : ∀ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel,
        Q * L₃ ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card)
    (hu : u ≤ L₃) (hq : 4 * q ≤ L₃)
    (hC : ∀ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel, facetWitnessCore i ∈ C)
    (hLowerSurvive : Disjoint K
      (multilevelDeletedEdges H V C 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 tLower
          (tripleLabel B))))
    (hUpperSurvive : Disjoint K
      (upperFacetNonStrongEdges H V tUpper facetCenter))
    (hFacetCenter : ∀ A ∈ sharedFourShadow K, facetCenter A ∈ A)
    (hTripleLabels : ActualTripleLabels K tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tLower * (∑ i ∈ highRetentionBadIncidences K H V P Q
      facetCenter tripleLabel,
        (facetParents K i.1.2).card *
          (parentPairLink K V (facetWitnessCore i)).card) ≤
      8 * (V.powersetCard 2).card ^ 2 * D₃ * D₄ * D₄ := by
  let I := highRetentionBadIncidences K H V P Q facetCenter tripleLabel
  have hI : I ⊆ facetBadIncidences K V facetCenter tripleLabel :=
    high_retention_bad_incidence_subset K H V P Q facetCenter tripleLabel
  have hDegree := high_retention_cleanup_degree K H V P Q L₃ u q
    facetCenter tripleLabel hKH hQ hUniformK hAmbientK
    hMinTriple hu hq
  have hStrong := facet_upper_strong_of_non_strong_edge_cleanup
    I K H V tUpper facetCenter tripleLabel
    hI hKH hUniformK hAmbientK hUpperSurvive
  exact facet_inheritance_weighted_incidence_bound_of_cleanup
    I K H V C tLower tUpper u q D₃ D₄ facetCenter tripleLabel
    hI hKH hUniformK hAmbientK hFacetCenter hTripleLabels
    hStrong hDegree hC hLowerSurvive ht hD₃ hD₄

end JSP523.Rank5
