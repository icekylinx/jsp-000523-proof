import JSP523.Rank4.PreprocessTouchingLoss
import JSP523.Rank4.PreprocessContractionDegrees

/-! # The actual finite regularization step

All covers, owner losses, and surviving families are constructed from F.
Only scalar choices of T, S, and the integer allocation radius remain.
-/

namespace JSP523.Rank4

/-- Construct the induced remainder after covering heavy pairs, retaining
explicit numeric bounds on the actual cover and owner-cleaning loss. -/
theorem exists_actual_pair_regularized_remainder
    {n : ℕ} (F : Family (Fin n)) (R T radius : ℕ)
    (hn : 0 < n) (hR : 3 ≤ R) (hT : 0 < T) (hGap : 2 * R ≤ T ^ 2)
    (hAdm : Admissible F) (hUniform : Uniform 4 F)
    (hVertex : ∀ v, (F.filter fun E => v ∈ E).card ≤ R * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F P ≤ R * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 →
      (facetCompletions F Finset.univ Q).card ≤ R)
    (hRadius : 6 * (R * n ^ 2) ≤ radius ^ 3) :
    ∃ F₀ : Family (Fin n), ∃ x c : ℕ,
      F₀ ⊆ F ∧ x * T ≤ 8 * n ∧
      c ^ 2 ≤ n.choose 2 * (x * (x - 1) * (3 * max (R * n) (9 * R) + R * n ^ 2)) ∧
      (∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F₀ P ≤ T * n) ∧
      3 * (F \ F₀).card ≤ 3 * (x.choose 2 * (R * n)) + 3 * c + (radius + 3) * n.choose 2 := by
  classical
  let U : Edge (Fin n) := Finset.univ
  have hSupport : F ⊆ U.powersetCard 4 := by
    intro E hE
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, hUniform hE⟩
  obtain ⟨X, hXU, hXT, _, hLow⟩ := exists_quantitative_heavy_pair_cover F U T R
    hSupport hAdm (fun Q hQ => hFacet Q (Finset.mem_powersetCard.mp hQ).2)
    hR hT (by simpa [U] using hn) hGap
  let V := U \ X
  let F₀ := fixedDecompositionCore F V
  have hGround : ∀ E ∈ F, E ⊆ U := fun E _ => Finset.subset_univ E
  have hCoreEq : F₀ = F.filter fun E => Disjoint E X :=
    fixed_core_sdiff_eq_disjoint_filter F U X hGround
  have hF₀F : F₀ ⊆ F := Finset.filter_subset _ _
  have hPair₀ : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F₀ P ≤ T * n := by
    intro P hP
    rw [hCoreEq]
    simpa [U] using hLow P hP
  have hVn : V.card ≤ n := by
    have h := Finset.card_le_card (Finset.sdiff_subset : U \ X ⊆ U)
    simpa [V, U] using h
  by_cases hX : X.Nonempty
  · let : Nonempty {v // v ∈ X} := ⟨⟨hX.choose, hX.choose_spec⟩⟩
    let L := fun i : {v // v ∈ X} => rankFourStarLink F V i.val
    let owner := maximumDegreePairOwner L
    let c := ∑ i : {v // v ∈ X}, (L i \ pairOwnerCleanedLink L owner i).card
    have hOutside : ∀ i : {v // v ∈ X}, i.val ∉ V := fun i hi => (Finset.mem_sdiff.mp hi).2 i.property
    have hClean := rank_four_star_owner_cleaning_loss_sq_bound_degree_caps
      (fun i : {v // v ∈ X} => i.val) (R * n) R hAdm hUniform hGround Finset.sdiff_subset
      hPair hFacet (fun _ _ h => Subtype.ext h) hOutside
    have hClean' : c ^ 2 ≤ n.choose 2 *
        (X.card * (X.card - 1) * (3 * max (R * n) (9 * R) + R * n ^ 2)) := by
      have hQ : (V.powersetCard 2).card ≤ n.choose 2 := by
        simpa using Nat.choose_le_choose 2 hVn
      have hSq : V.card ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hVn 2
      have hMax : max R 3 = R := max_eq_left hR
      simp only [Fintype.card_coe, hMax] at hClean
      change c ^ 2 ≤ _ at hClean
      exact hClean.trans (Nat.mul_le_mul hQ
        (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left R hSq) _)))
    have hSize : ∀ v ∈ X, 6 * (F.filter fun E => v ∈ E).card ≤ radius ^ 3 := by
      intro v _
      exact (Nat.mul_le_mul_left 6 (hVertex v)).trans hRadius
    have hLoss := actual_touching_cover_loss F U X (R * n) radius hUniform hGround hPair hSize
    change 3 * (F \ F₀).card ≤ 3 * (X.card.choose 2 * (R * n)) + 3 * c +
      (radius + 3) * V.card.choose 2 at hLoss
    refine ⟨F₀, X.card, c, hF₀F, by simpa [U] using hXT, hClean', hPair₀, ?_⟩
    exact hLoss.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left (radius + 3) (Nat.choose_le_choose 2 hVn)) _)
  · have hEmpty : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    have hEq : F₀ = F := by
      rw [hCoreEq, hEmpty]
      simp
    refine ⟨F₀, 0, 0, hF₀F, by simp, by simp, hPair₀, ?_⟩
    simp [hEq]

/-- A genuine one-step contraction of all degree caps.  The polynomial
loss certificate is the finite precursor to R ↦ R^(3/4). -/
theorem exists_actual_degree_contraction_step
    {n : ℕ} (F : Family (Fin n)) (R T S radius : ℕ)
    (hn : 0 < n) (hR : 3 ≤ R) (hT : 0 < T) (hTS : T ≤ S) (hGap : 2 * R ≤ T ^ 2)
    (hAdm : Admissible F) (hUniform : Uniform 4 F)
    (hVertex : ∀ v, (F.filter fun E => v ∈ E).card ≤ R * n ^ 2)
    (hPair : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree F P ≤ R * n)
    (hFacet : ∀ Q : Edge (Fin n), Q.card = 3 →
      (facetCompletions F Finset.univ Q).card ≤ R)
    (hRadius : 6 * (R * n ^ 2) ≤ radius ^ 3) :
    ∃ K : Family (Fin n), ∃ x c : ℕ,
      K ⊆ F ∧ x * T ≤ 8 * n ∧
      c ^ 2 ≤ n.choose 2 * (x * (x - 1) * (3 * max (R * n) (9 * R) + R * n ^ 2)) ∧
      (∀ v, (K.filter fun E => v ∈ E).card ≤ S * n ^ 2) ∧
      (∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree K P ≤ S * n) ∧
      (∀ Q : Edge (Fin n), Q.card = 3 → (facetCompletions K Finset.univ Q).card ≤ S) ∧
      3 * S * (F \ K).card ≤
        S * (3 * (x.choose 2 * (R * n)) + 3 * c + (radius + 3) * n.choose 2) +
          6 * n.choose 2 * max (T * n) (9 * R) := by
  classical
  obtain ⟨F₀, x, c, hF₀F, hx, hc, hPair₀, hLoss₀⟩ :=
    exists_actual_pair_regularized_remainder F R T radius hn hR hT hGap hAdm hUniform
      hVertex hPair hFacet hRadius
  have hUniform₀ : Uniform 4 F₀ := fun _ hE => hUniform (hF₀F hE)
  have hFacet₀ : ∀ Q : Edge (Fin n), Q.card = 3 →
      (facetCompletions F₀ Finset.univ Q).card ≤ R := by
    intro Q hQ
    apply (Finset.card_le_card ?_).trans (hFacet Q hQ)
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, hF₀F (Finset.mem_filter.mp hz).2⟩
  obtain ⟨K, hKF₀, hLoss₁, hFacetK⟩ := high_codegree_deletion_regularizes_of_degree_caps
    F₀ Finset.univ S (T * n) R hUniform₀ (admissible_mono hF₀F hAdm) hPair₀ hFacet₀
  have hKF := hKF₀.trans hF₀F
  have hPairK : ∀ P : Edge (Fin n), P.card = 2 → rankFourPairDegree K P ≤ S * n := by
    intro P hP
    apply le_trans (b := rankFourPairDegree F₀ P)
    · apply Finset.card_le_card
      intro E hE
      exact Finset.mem_filter.mpr ⟨hKF₀ (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩
    · exact (hPair₀ P hP).trans (Nat.mul_le_mul_right n hTS)
  refine ⟨K, x, c, hKF, hx, hc, ?_, hPairK, ?_, ?_⟩
  · intro v
    have hv := rank_four_vertex_degree_le_ground_mul_pair_cap K Finset.univ (S * n)
      (fun _ hE => hUniform (hKF hE)) (fun E _ => Finset.subset_univ E) hPairK v
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hv
  · intro Q hQ
    exact hFacetK Q (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ Q, hQ⟩)
  · have h0 := Finset.card_sdiff_add_card_eq_card hF₀F
    have h1 := Finset.card_sdiff_add_card_eq_card hKF₀
    have h2 := Finset.card_sdiff_add_card_eq_card hKF
    have hAdd : (F \ K).card = (F \ F₀).card + (F₀ \ K).card := by omega
    have hScale₀ := Nat.mul_le_mul_left S hLoss₀
    have hScale₁ := Nat.mul_le_mul_left 3 hLoss₁
    simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hScale₁
    rw [hAdd]
    nlinarith

end JSP523.Rank4
