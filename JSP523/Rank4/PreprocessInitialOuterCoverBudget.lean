import JSP523.Rank4.PreprocessInitialOuterCoverOwner

namespace JSP523.Rank4

/-- A finite budget for deleting the actual X layer after high vertices
have been removed. Empty X is included. -/
theorem initial_outer_touching_polynomial_bound
    {n : ℕ} (H : Family (Fin n)) (W X : Edge (Fin n)) (radius : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (hGround : ∀ E ∈ H, E ⊆ W) (hU : 6 ≤ (W \ X).card)
    (hSize : ∀ c ∈ X, 6 * (H.filter fun E => c ∈ E).card ≤ radius ^ 3) :
    (H \ fixedDecompositionCore H (W \ X)).card ≤
      X.card.choose 2 * n ^ 2 + 2 * X.card * n ^ 2 * (Nat.sqrt n + 1) +
        (radius + 3) * n ^ 2 := by
  classical
  by_cases hX : X.Nonempty
  · let : Nonempty {c // c ∈ X} := ⟨⟨hX.choose, hX.choose_spec⟩⟩
    have hTouch := actual_touching_cover_loss H W X (n ^ 2) radius hUniform hGround
      (rank_four_pair_degree_le_ground_square H hUniform) hSize
    have hMoment := rank_four_star_owner_cleaning_loss_sq_bound
      (fun i : {c // c ∈ X} => i.val) hAdm Subtype.val_injective
      (fun i hi => (Finset.mem_sdiff.mp hi).2 i.property) hU
    have hUn : (W \ X).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (W \ X))
    simp only [Fintype.card_coe, Finset.card_powersetCard] at hMoment
    have hClean := initial_outer_owner_moment_linear_bound _ X.card (W \ X).card n hUn
      (by simpa only [mul_assoc] using hMoment)
    have hChoose : (W \ X).card.choose 2 ≤ n ^ 2 :=
      (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hUn 2)
    have hScale := Nat.mul_le_mul_left (radius + 3) hChoose
    dsimp only at hTouch
    omega
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hX
    subst X
    have hCore : fixedDecompositionCore H W = H := by
      ext E
      simp only [fixedDecompositionCore, Finset.mem_filter, and_iff_left_iff_imp]
      exact hGround E
    simp only [Finset.sdiff_empty, hCore, Finset.sdiff_self, Finset.card_empty]
    omega

/-- Actual original-family decomposition with a completely explicit
finite outer-loss budget. All star links and all deleted families come
from H itself. -/
theorem exists_initial_outer_original_budget
    {n : ℕ} (H : Family (Fin n)) (Z X : Edge (Fin n)) (fallback : Fin n) (radius : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform 4 H) (hX : X ⊆ Finset.univ \ Z)
    (hU : 6 ≤ (Finset.univ \ (Z ∪ X)).card)
    (hSize : ∀ c ∈ X, 6 * ((fixedDecompositionCore H (Finset.univ \ Z)).filter
      fun E => c ∈ E).card ≤ radius ^ 3) :
    let U := Finset.univ \ (Z ∪ X)
    let L := fun c => rankFourStarLink H U c
    ∃ owner : Edge (Fin n) → Fin n, ∃ outerLoss : ℕ,
      H.card ≤ (Z.biUnion (pairOwnerCleanedLink L owner)).card +
        (fixedDecompositionCore H U).card + outerLoss ∧
      outerLoss ≤ ((Z.card + X.card).choose 2 + X.card.choose 2) * n ^ 2 +
        2 * (Z.card + X.card) * n ^ 2 * (Nat.sqrt n + 1) + (radius + 3) * n ^ 2 := by
  classical
  dsimp only
  let U := Finset.univ \ (Z ∪ X)
  let W := Finset.univ \ Z
  let H₀ := fixedDecompositionCore H W
  let L := fun c => rankFourStarLink H U c
  have hOutside : ∀ c ∈ Z, c ∉ U := fun c hc h =>
    (Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ hc)
  obtain ⟨owner, hMoment⟩ := exists_initial_outer_owner H U Z fallback hAdm hOutside hU
  have hUn : U.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ U)
  have hClean := initial_outer_owner_moment_linear_bound _ Z.card U.card n hUn hMoment
  have hUeq : W \ X = U := by ext x; simp only [W, U, Finset.mem_sdiff, Finset.mem_union]; tauto
  have hSub : H₀ ⊆ H := Finset.filter_subset _ _
  have hTouch := initial_outer_touching_polynomial_bound H₀ W X radius
    (admissible_mono hSub hAdm) (fun E hE => hUniform (hSub hE))
    (fun E hE => (Finset.mem_filter.mp hE).2) (by simpa only [hUeq] using hU) hSize
  rw [hUeq] at hTouch
  let loss := (Z ∪ X).card.choose 2 * n ^ 2 +
    (H₀ \ fixedDecompositionCore H₀ U).card +
      ∑ c ∈ Z, (L c \ pairOwnerCleanedLink L owner c).card
  refine ⟨owner, loss, initial_outer_original_mass_bound H Z X owner hUniform hX, ?_⟩
  have hZX : Disjoint Z X := Finset.disjoint_left.mpr fun z hz hx =>
    (Finset.mem_sdiff.mp (hX hx)).2 hz
  dsimp only [loss, L]
  rw [Finset.card_union_of_disjoint hZX]
  nlinarith only [hClean, hTouch]

end JSP523.Rank4
