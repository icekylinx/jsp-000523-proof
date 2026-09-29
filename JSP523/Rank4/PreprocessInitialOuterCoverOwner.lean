import JSP523.Rank4.PreprocessInitialOuterCoverDecomposition

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The maximum owner on the actual center subtype extends to a vertex
owner, with the same actual cleaning loss and the finite cross-moment bound. -/
theorem exists_initial_outer_owner
    (H : Family α) (U Z : Edge α) (fallback : α)
    (hAdm : Admissible H) (hOutside : ∀ c ∈ Z, c ∉ U) (hU : 6 ≤ U.card) :
    ∃ owner : Edge α → α,
      (∑ c ∈ Z, (rankFourStarLink H U c \
        pairOwnerCleanedLink (fun d => rankFourStarLink H U d) owner c).card) ^ 2 ≤
      U.card.choose 2 * (Z.card * (Z.card - 1)) *
        (U.card ^ 3 + 3 * U.card.choose 3) := by
  classical
  by_cases hZ : Z.Nonempty
  · let : Nonempty {c // c ∈ Z} := ⟨⟨hZ.choose, hZ.choose_spec⟩⟩
    let L := fun i : {c // c ∈ Z} => rankFourStarLink H U i.val
    let owner := maximumDegreePairOwner L
    let lifted : Edge α → α := fun P => (owner P).val
    have hClean (i : {c // c ∈ Z}) :
        pairOwnerCleanedLink (fun d => rankFourStarLink H U d) lifted i.val =
          pairOwnerCleanedLink L owner i := by
      ext T
      simp only [pairOwnerCleanedLink, Finset.mem_filter]
      constructor
      · rintro ⟨hT, hOwn⟩
        exact ⟨hT, fun P hP => Subtype.ext (hOwn P hP)⟩
      · rintro ⟨hT, hOwn⟩
        exact ⟨hT, fun P hP => congrArg Subtype.val (hOwn P hP)⟩
    have hMoment := rank_four_star_owner_cleaning_loss_sq_bound
      (fun i : {c // c ∈ Z} => i.val) hAdm Subtype.val_injective
      (fun i => hOutside i.val i.property) hU
    refine ⟨lifted, ?_⟩
    rw [← Finset.sum_coe_sort Z]
    simp_rw [hClean]
    simpa only [Fintype.card_coe, Finset.card_powersetCard, mul_assoc] using hMoment
  · refine ⟨fun _ => fallback, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hZ]
    simp

/-- A convenient polynomial form of the initial owner moment. -/
theorem initial_outer_owner_moment_linear_bound
    (m z u n : ℕ) (hu : u ≤ n)
    (h : m ^ 2 ≤ u.choose 2 * (z * (z - 1)) * (u ^ 3 + 3 * u.choose 3)) :
    m ≤ 2 * z * n ^ 2 * (Nat.sqrt n + 1) := by
  have hTwo : u.choose 2 ≤ n ^ 2 :=
    (Nat.choose_le_pow u 2).trans (Nat.pow_le_pow_left hu 2)
  have hThree : u ^ 3 + 3 * u.choose 3 ≤ 4 * n ^ 3 := by
    have h1 := Nat.choose_le_pow u 3
    have h2 := Nat.pow_le_pow_left hu 3
    omega
  have hz : z * (z - 1) ≤ z ^ 2 := by nlinarith only [Nat.sub_le z 1]
  have hSq : m ^ 2 ≤ 4 * z ^ 2 * n ^ 5 := by
    calc
      _ ≤ _ := h
      _ ≤ n ^ 2 * z ^ 2 * (4 * n ^ 3) := Nat.mul_le_mul (Nat.mul_le_mul hTwo hz) hThree
      _ = _ := by ring
  have hn : n ≤ (Nat.sqrt n + 1) ^ 2 := (Nat.lt_succ_sqrt' n).le
  have hScale := Nat.mul_le_mul_left (4 * z ^ 2 * n ^ 4) hn
  have hFinal : m ^ 2 ≤ (2 * z * n ^ 2 * (Nat.sqrt n + 1)) ^ 2 := by
    nlinarith only [hSq, hScale]
  have h := hFinal
  generalize 2 * z * n ^ 2 * (Nat.sqrt n + 1) = b at h ⊢
  nlinarith only [h]

end JSP523.Rank4
