import JSP523.Rank5.HigherRankFacetActual

/-! # Low-retention shared-facet incidences at arbitrary rank -/
namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α] (n : ℕ)

theorem total_core_parent_degrees
    (H : Family α) (V : Edge α) (r j : ℕ)
    (hUniform : Uniform r H)
    (hAmbient : ∀ E ∈ H, E ⊆ V) :
    (∑ B ∈ V.powersetCard j,
        (H.filter fun E => B ⊆ E).card) = r.choose j * H.card := by
  classical
  calc
    (∑ B ∈ V.powersetCard j,
        (H.filter fun E => B ⊆ E).card) =
        ∑ B ∈ V.powersetCard j,
          ∑ E ∈ H, if B ⊆ E then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro B hB
      exact Finset.card_filter (fun E : Edge α => B ⊆ E) H
    _ = ∑ E ∈ H, ∑ B ∈ V.powersetCard j,
          if B ⊆ E then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ E ∈ H, (E.powersetCard j).card := by
      apply Finset.sum_congr rfl
      intro E hE
      calc
        (∑ B ∈ V.powersetCard j,
            if B ⊆ E then (1 : ℕ) else 0) =
            ((V.powersetCard j).filter fun B => B ⊆ E).card :=
          (Finset.card_filter (fun B : Edge α => B ⊆ E) _).symm
        _ = (E.powersetCard j).card := by
          congr 1
          ext B
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          constructor
          · rintro ⟨⟨_, hCard⟩, hBE⟩
            exact ⟨hBE, hCard⟩
          · rintro ⟨hBE, hCard⟩
            exact ⟨⟨hBE.trans (hAmbient E hE), hCard⟩, hBE⟩
    _ = ∑ _E ∈ H, r.choose j := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.card_powersetCard, hUniform hE]
    _ = r.choose j * H.card := by simp [mul_comm]

theorem triple_parent_pair_link_card_eq_codegree
    (K : Family α) (V B : Edge α)
    (hUniform : Uniform (n + 2) K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hBcard : B.card = n) :
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

noncomputable def lowFacetCores
    (K H : Family α) (V : Edge α) (P Q : ℕ) : Family α := by
  classical
  exact (V.powersetCard (n + 1)).filter fun A =>
    Q * (facetParents K A).card < P * (facetParents H A).card

noncomputable def lowFacetBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact (facetBadIncidences K V (n + 1) facetCenter tripleLabel).filter fun i =>
    Q * (facetParents K i.1.2).card <
      P * (facetParents H i.1.2).card

theorem low_facet_bad_incidence_card_le_parent_degree_sum
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) :
    (lowFacetBadIncidences n K H V P Q facetCenter tripleLabel).card ≤
      (n + 1) * ∑ A ∈ lowFacetCores n K H V P Q, (facetParents K A).card := by
  classical
  let I := lowFacetBadIncidences n K H V P Q facetCenter tripleLabel
  let C := lowFacetCores n K H V P Q
  have hMap : ∀ i ∈ I, i.1.2 ∈ C := by
    intro i hi
    have hParts := Finset.mem_filter.mp hi
    have hBad := (Finset.mem_filter.mp hParts.1).2
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hBad.2.1).1, hParts.2⟩
  have hOne : ∀ A ∈ C,
      (I.filter fun i => i.1.2 = A).card ≤
        (n + 1) * (facetParents K A).card := by
    intro A hA
    let F := I.filter fun i => i.1.2 = A
    have hAcard : A.card = n + 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
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
    _ ≤ ∑ A ∈ C, (n + 1) * (facetParents K A).card :=
      Finset.sum_le_sum hOne
    _ = (n + 1) * ∑ A ∈ C, (facetParents K A).card := by
      rw [Finset.mul_sum]

noncomputable def lowTripleCores
    (K H : Family α) (V : Edge α) (P Q : ℕ) : Family α := by
  classical
  exact (V.powersetCard n).filter fun B =>
    Q * (K.filter fun E => B ⊆ E).card <
      P * (H.filter fun E => B ⊆ E).card

noncomputable def lowTripleBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact (facetBadIncidences K V (n + 1) facetCenter tripleLabel).filter fun i =>
    Q * (K.filter fun E => facetWitnessCore i ⊆ E).card <
      P * (H.filter fun E => facetWitnessCore i ⊆ E).card

theorem low_triple_bad_incidence_card_le_parent_degree_sum
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) :
    (lowTripleBadIncidences n K H V P Q facetCenter tripleLabel).card ≤
      2 * ∑ B ∈ lowTripleCores n K H V P Q,
        (K.filter fun E => B ⊆ E).card := by
  classical
  let I := lowTripleBadIncidences n K H V P Q facetCenter tripleLabel
  let C := lowTripleCores n K H V P Q
  have hMap : ∀ i ∈ I, facetWitnessCore i ∈ C := by
    intro i hi
    have hParts := Finset.mem_filter.mp hi
    have hBad := hParts.1
    have hSource := (Finset.mem_filter.mp hBad).1
    have hE : i.1.1 ∈ K :=
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
    have hAcard : i.1.2.card = n + 1 :=
      (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
    have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hBad).2.1
    have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hBad).2.2.2.1
    have hBcard : (facetWitnessCore i).card = n := by
      have herase := Finset.card_erase_add_one ha
      change (i.1.2.erase i.2).card = n
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
    have hBcard : B.card = n :=
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

noncomputable def lowEitherBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact lowFacetBadIncidences n K H V P Q facetCenter tripleLabel ∪
    lowTripleBadIncidences n K H V P Q facetCenter tripleLabel

noncomputable def highRetentionBadIncidences
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) := by
  classical
  exact facetBadIncidences K V (n + 1) facetCenter tripleLabel \
    lowEitherBadIncidences n K H V P Q facetCenter tripleLabel

theorem high_retention_bad_incidence_subset
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (facetCenter tripleLabel : Edge α → α) :
    highRetentionBadIncidences n K H V P Q facetCenter tripleLabel ⊆
      facetBadIncidences K V (n + 1) facetCenter tripleLabel := by
  exact Finset.sdiff_subset

theorem high_retention_bad_incidence_degrees
    (K H : Family α) (V : Edge α) (P Q L₄ L₃ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hQ : 0 < Q)
    (hUniformK : Uniform (n + 2) K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V)
    (hMinFacet : ∀ i ∈ highRetentionBadIncidences n K H V P Q
      facetCenter tripleLabel,
        Q * L₄ ≤ P * (facetParents H i.1.2).card)
    (hMinTriple : ∀ i ∈ highRetentionBadIncidences n K H V P Q
      facetCenter tripleLabel,
        Q * L₃ ≤ P * (H.filter fun E => facetWitnessCore i ⊆ E).card) :
    (∀ i ∈ highRetentionBadIncidences n K H V P Q facetCenter tripleLabel,
      L₄ ≤ (facetParents K i.1.2).card) ∧
    (∀ i ∈ highRetentionBadIncidences n K H V P Q facetCenter tripleLabel,
      L₃ ≤ (parentPairLink K V (facetWitnessCore i)).card) := by
  classical
  constructor
  · intro i hi
    have hBad : i ∈ facetBadIncidences K V (n + 1) facetCenter tripleLabel :=
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
    have hBad : i ∈ facetBadIncidences K V (n + 1) facetCenter tripleLabel :=
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
    have hAcard : i.1.2.card = n + 1 :=
      (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
    have ha : i.2 ∈ i.1.2 := (Finset.mem_filter.mp hBad).2.2.2.1
    have hBcard : (facetWitnessCore i).card = n := by
      have hErase := Finset.card_erase_add_one ha
      change (i.1.2.erase i.2).card = n
      omega
    have hEq := triple_parent_pair_link_card_eq_codegree n
      K V (facetWitnessCore i) hUniformK hAmbientK hBcard
    have hMin := hMinTriple i hi
    have hScaled : Q * L₃ ≤
        Q * (K.filter fun E => facetWitnessCore i ⊆ E).card :=
      hMin.trans hRetention
    rw [← hEq] at hScaled
    exact (Nat.mul_le_mul_left_iff hQ).mp hScaled

/-- IV.9.1 at any core cardinality. -/
theorem low_core_degree_sum_bound
    (K H : Family α) (V : Edge α) (r j P Q : ℕ) (C : Family α)
    (hUniform : Uniform r H) (hAmbient : ∀ E ∈ H, E ⊆ V)
    (hC : C ⊆ V.powersetCard j)
    (hLow : ∀ A ∈ C,
      Q * (K.filter fun E => A ⊆ E).card ≤
        P * (H.filter fun E => A ⊆ E).card) :
    Q * (∑ A ∈ C, (K.filter fun E => A ⊆ E).card) ≤
      P * (r.choose j * H.card) := by
  classical
  have hSum : (∑ A ∈ C, (H.filter fun E => A ⊆ E).card) ≤
      r.choose j * H.card := by
    calc
      _ ≤ ∑ A ∈ V.powersetCard j, (H.filter fun E => A ⊆ E).card :=
        Finset.sum_le_sum_of_subset_of_nonneg hC (by simp)
      _ = _ := total_core_parent_degrees H V r j hUniform hAmbient
  calc
    _ ≤ P * (∑ A ∈ C, (H.filter fun E => A ⊆ E).card) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum hLow
    _ ≤ _ := Nat.mul_le_mul_left P hSum

theorem low_facet_bad_incidence_budget
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (center lower : Edge α → α)
    (hUniformH : Uniform (n + 2) H) (hAmbientH : ∀ E ∈ H, E ⊆ V) :
    Q * (lowFacetBadIncidences n K H V P Q center lower).card ≤
      ((n + 1) * (n + 2).choose (n + 1)) * P * H.card := by
  classical
  have hSum := low_core_degree_sum_bound K H V (n + 2) (n + 1) P Q
    (lowFacetCores n K H V P Q) hUniformH hAmbientH
    (Finset.filter_subset _ _) (fun A hA => Nat.le_of_lt (Finset.mem_filter.mp hA).2)
  have hInc := low_facet_bad_incidence_card_le_parent_degree_sum n K H V P Q center lower
  have hScaled := Nat.mul_le_mul_left Q hInc
  have hSumScaled := Nat.mul_le_mul_left (n + 1) hSum
  dsimp [facetParents] at hScaled
  nlinarith

theorem low_triple_bad_incidence_budget
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (center lower : Edge α → α)
    (hUniformK : Uniform (n + 2) K) (hUniformH : Uniform (n + 2) H)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) (hAmbientH : ∀ E ∈ H, E ⊆ V) :
    Q * (lowTripleBadIncidences n K H V P Q center lower).card ≤
      (2 * (n + 2).choose n) * P * H.card := by
  classical
  have hSum := low_core_degree_sum_bound K H V (n + 2) n P Q
    (lowTripleCores n K H V P Q) hUniformH hAmbientH
    (Finset.filter_subset _ _) (fun A hA => Nat.le_of_lt (Finset.mem_filter.mp hA).2)
  have hInc := low_triple_bad_incidence_card_le_parent_degree_sum n K H V P Q
    center lower hUniformK hAmbientK
  have hScaled := Nat.mul_le_mul_left Q hInc
  have hSumScaled := Nat.mul_le_mul_left 2 hSum
  nlinarith

def lowFacetIncidenceConstant (n : ℕ) : ℕ :=
  (n + 1) * (n + 2).choose (n + 1) + 2 * (n + 2).choose n

theorem low_either_bad_incidence_budget
    (K H : Family α) (V : Edge α) (P Q : ℕ)
    (center lower : Edge α → α)
    (hUniformK : Uniform (n + 2) K) (hUniformH : Uniform (n + 2) H)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) (hAmbientH : ∀ E ∈ H, E ⊆ V) :
    Q * (lowEitherBadIncidences n K H V P Q center lower).card ≤
      lowFacetIncidenceConstant n * P * H.card := by
  have hA := low_facet_bad_incidence_budget n K H V P Q center lower hUniformH hAmbientH
  have hB := low_triple_bad_incidence_budget n K H V P Q center lower
    hUniformK hUniformH hAmbientK hAmbientH
  have hUnion := Finset.card_union_le
    (lowFacetBadIncidences n K H V P Q center lower)
    (lowTripleBadIncidences n K H V P Q center lower)
  dsimp only [lowEitherBadIncidences]
  dsimp [lowFacetIncidenceConstant]
  nlinarith

/-- Combine an actual high-retention weighted witness bound with IV.9.1. -/
theorem facet_bad_incidence_combined_budget
    (K H : Family α) (V : Edge α) (P Q t L₁ L₂ W : ℕ)
    (center lower : Edge α → α)
    (hUniformK : Uniform (n + 2) K) (hUniformH : Uniform (n + 2) H)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) (hAmbientH : ∀ E ∈ H, E ⊆ V)
    (hA : ∀ i ∈ highRetentionBadIncidences n K H V P Q center lower,
      L₁ ≤ (facetParents K i.1.2).card)
    (hB : ∀ i ∈ highRetentionBadIncidences n K H V P Q center lower,
      L₂ ≤ (parentPairLink K V (facetWitnessCore i)).card)
    (hWeighted : t * (∑ i ∈ highRetentionBadIncidences n K H V P Q center lower,
      (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card) ≤ W) :
    Q * (t * (L₁ * L₂) * (facetBadIncidences K V (n + 1) center lower).card) ≤
      t * (L₁ * L₂) * (lowFacetIncidenceConstant n * P * H.card) + Q * W := by
  classical
  let I := highRetentionBadIncidences n K H V P Q center lower
  let B := lowEitherBadIncidences n K H V P Q center lower
  let A := facetBadIncidences K V (n + 1) center lower
  have hSum : L₁ * L₂ * I.card ≤
      ∑ i ∈ I, (facetParents K i.1.2).card *
        (parentPairLink K V (facetWitnessCore i)).card := by
    calc
      _ = ∑ _i ∈ I, L₁ * L₂ := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => Nat.mul_le_mul (hA i hi) (hB i hi))
  have hHigh : t * (L₁ * L₂ * I.card) ≤ W :=
    (Nat.mul_le_mul_left t hSum).trans hWeighted
  have hLow := low_either_bad_incidence_budget n K H V P Q center lower
    hUniformK hUniformH hAmbientK hAmbientH
  have hCover : A ⊆ B ∪ I := by
    intro i hi
    by_cases hB : i ∈ B
    · exact Finset.mem_union_left _ hB
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hB⟩)
  have hTotal : A.card ≤ B.card + I.card :=
    (Finset.card_le_card hCover).trans (Finset.card_union_le ..)
  have hTotalScaled := Nat.mul_le_mul_left (Q * t * (L₁ * L₂)) hTotal
  have hLowScaled := Nat.mul_le_mul_left (t * (L₁ * L₂)) hLow
  have hHighScaled := Nat.mul_le_mul_left Q hHigh
  change Q * (t * (L₁ * L₂) * A.card) ≤ _
  nlinarith

end JSP523.Rank5.HigherRankUpper
