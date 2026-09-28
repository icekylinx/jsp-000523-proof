import JSP523.Rank5.StarLayerCollisionReindex
import JSP523.Rank5.ShadowAllocation
import JSP523.Rank5.ActualStarOwnership

/-!
# Global ordered-pair collision budget for actual star layers

This sums the pairwise actual collision-moment estimate over a finite set
of centers, in the form needed by the owner-degree Cauchy bound.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- Change the order of summation between shadow points and ordered
distinct center pairs. -/
theorem sum_orderedDegreePairs_eq_center_first
    {τ ι : Type*} [DecidableEq τ] [DecidableEq ι]
    (P : Finset τ) (I : Finset ι) (d : τ → ι → ℕ) :
    (∑ p ∈ P, orderedDegreePairs I (d p)) =
      ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ p ∈ P, d p i * d p j := by
  classical
  unfold orderedDegreePairs
  calc
    (∑ p ∈ P, ∑ i ∈ I, ∑ j ∈ I.erase i, d p i * d p j)
        = ∑ i ∈ I, ∑ p ∈ P, ∑ j ∈ I.erase i, d p i * d p j := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ p ∈ P, d p i * d p j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]

/-- The ordered collision budget across all distinct centers and all
codimension-two prefixes. -/
def actualStarLayerOrderedCollisionBudget
    (H : Family α) (U Centers : Edge α) (r : ℕ) : ℕ :=
  ∑ z ∈ Centers, ∑ w ∈ Centers.erase z,
    ∑ P ∈ U.powersetCard (r - 2),
      starLayerPrefixDegree (actualStarLink H U z r) P *
        starLayerPrefixDegree (actualStarLink H U w r) P

/-- Summing (IV.3.3) over every ordered pair of distinct actual star
centers gives the total collision budget with the exact center-pair factor. -/
theorem actualStarLayerOrderedCollisionBudget_le
    [Inhabited α] {H : Family α} {U Centers : Edge α} {r D₂ D₃ : ℕ}
    (hH : Admissible H)
    (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    actualStarLayerOrderedCollisionBudget H U Centers r ≤
      Centers.card * (Centers.card - 1) *
        ((r - 1) * (r - 1) * D₂ +
          U.card * (U.card - 1) * (r - 2) * D₃) := by
  classical
  unfold actualStarLayerOrderedCollisionBudget
  calc
    (∑ z ∈ Centers, ∑ w ∈ Centers.erase z,
      ∑ P ∈ U.powersetCard (r - 2),
        starLayerPrefixDegree (actualStarLink H U z r) P *
          starLayerPrefixDegree (actualStarLink H U w r) P)
      ≤ ∑ z ∈ Centers, ∑ w ∈ Centers.erase z,
          ((r - 1) * (r - 1) * D₂ +
            U.card * (U.card - 1) * (r - 2) * D₃) := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro w hw
        have hzw : z ≠ w := (Finset.mem_erase.mp hw).1.symm
        exact starLayerActualCollision_moment_le
          hH hzw (hCenters z hz) (hCenters w (Finset.mem_erase.mp hw).2)
          hr hD₂ hD₃
    _ = Centers.card * (Centers.card - 1) *
        ((r - 1) * (r - 1) * D₂ +
          U.card * (U.card - 1) * (r - 2) * D₃) := by
        calc
        (∑ z ∈ Centers, ∑ w ∈ Centers.erase z,
          ((r - 1) * (r - 1) * D₂ +
            U.card * (U.card - 1) * (r - 2) * D₃))
          = ∑ z ∈ Centers, (Centers.card - 1) *
              ((r - 1) * (r - 1) * D₂ +
                U.card * (U.card - 1) * (r - 2) * D₃) := by
              apply Finset.sum_congr rfl
              intro z hz
              simp [Finset.sum_const, Finset.card_erase_of_mem hz]
        _ = Centers.card * (Centers.card - 1) *
            ((r - 1) * (r - 1) * D₂ +
              U.card * (U.card - 1) * (r - 2) * D₃) := by
              simp [Finset.sum_const, Nat.mul_assoc]

/-- The actual star-layer non-owner degrees satisfy the same square bound
as the abstract ownership lemma, with its collision sum discharged by
(IV.3.3). -/
theorem actualStarLayerNonownerDegree_sq_le
    [Inhabited α] {H : Family α} {U Centers : Edge α} {r D₂ D₃ : ℕ}
    (hH : Admissible H)
    (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (owner : Edge α → α)
    (hOwner : ∀ P ∈ U.powersetCard (r - 2), owner P ∈ Centers)
    (hMax : ∀ P ∈ U.powersetCard (r - 2), ∀ z ∈ Centers,
      starLayerPrefixDegree (actualStarLink H U z r) P ≤
        starLayerPrefixDegree (actualStarLink H U (owner P) r) P) :
    (∑ P ∈ U.powersetCard (r - 2),
      ∑ z ∈ Centers.erase (owner P),
        starLayerPrefixDegree (actualStarLink H U z r) P) ^ 2 ≤
      (U.powersetCard (r - 2)).card *
        (Centers.card * (Centers.card - 1) *
          ((r - 1) * (r - 1) * D₂ +
            U.card * (U.card - 1) * (r - 2) * D₃)) := by
  classical
  let P := U.powersetCard (r - 2)
  let d : Edge α → α → ℕ :=
    fun Q z => starLayerPrefixDegree (actualStarLink H U z r) Q
  have hAbstract := total_nonmaximal_degree_sq_le_pair_budget
    P Centers d owner
    (by intro Q hQ; exact hOwner Q hQ)
    (by intro Q hQ z hz; exact hMax Q hQ z hz)
  have hSwap :
      (∑ Q ∈ P, orderedDegreePairs Centers (d Q)) =
        actualStarLayerOrderedCollisionBudget H U Centers r := by
    unfold actualStarLayerOrderedCollisionBudget
    rw [sum_orderedDegreePairs_eq_center_first]
  have hCollision := actualStarLayerOrderedCollisionBudget_le
    hH hCenters hr hD₂ hD₃
  calc
    (∑ Q ∈ P, ∑ z ∈ Centers.erase (owner Q), d Q z) ^ 2 ≤
        P.card * ∑ Q ∈ P, orderedDegreePairs Centers (d Q) := hAbstract
    _ = P.card * actualStarLayerOrderedCollisionBudget H U Centers r := by
        rw [hSwap]
    _ ≤ P.card * (Centers.card * (Centers.card - 1) *
          ((r - 1) * (r - 1) * D₂ +
            U.card * (U.card - 1) * (r - 2) * D₃)) :=
        Nat.mul_le_mul_left P.card hCollision

/-- The ownership module's bad-incidence count is exactly the sum of the
non-owner link degrees, after reindexing by the center. -/
theorem actualStarLayer_badShadowDegree_eq_nonowner_sum
    {H : Family α} {U Centers : Edge α} {r : ℕ}
    (owner : Edge α → α) (P : Edge α)
    (hP : P ∈ U.powersetCard (r - 2)) :
    badShadowDegree (actualStarLayerObjects H U Centers r)
        Prod.fst
        (fun zT : α × Edge α => actualStarLayerFacets U zT.2 r)
        owner P =
      ∑ z ∈ Centers.erase (owner P),
        starLayerPrefixDegree (actualStarLink H U z r) P := by
  classical
  let D := (actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
    P ∈ actualStarLayerFacets U zT.2 r ∧ owner P ≠ zT.1
  have hMaps : (D : Set (α × Edge α)).MapsTo Prod.fst
      (Centers.erase (owner P) : Finset α) := by
    intro zT hzT
    have hCenter : zT.1 ∈ Centers :=
      (Finset.mem_product.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hzT).1).1).1
    have hNe : owner P ≠ zT.1 := (Finset.mem_filter.mp hzT).2.2
    exact Finset.mem_erase.mpr ⟨hNe.symm, hCenter⟩
  rw [show badShadowDegree (actualStarLayerObjects H U Centers r)
      Prod.fst (fun zT : α × Edge α => actualStarLayerFacets U zT.2 r)
      owner P = D.card by rfl]
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  apply Finset.sum_congr rfl
  intro z hz
  let L := (actualStarLink H U z r).filter fun T => P ⊆ T
  have hzCenter : z ∈ Centers := (Finset.mem_erase.mp hz).2
  have hzNe : z ≠ owner P := (Finset.mem_erase.mp hz).1
  have hFiber : {zT ∈ D | zT.1 = z} = L.image (fun T => (z, T)) := by
    ext ⟨z', T⟩
    by_cases hzz : z = z'
    · subst z'
      simp [D, L, actualStarLayerObjects, actualStarLayerFacets,
        actualStarLink, Finset.mem_filter, Finset.mem_product,
        Finset.mem_powersetCard, hP, hzCenter, hzNe.symm,
        and_left_comm, and_comm]
    · simp [D, L, actualStarLayerObjects, actualStarLayerFacets,
        actualStarLink, Finset.mem_filter, Finset.mem_product,
        Finset.mem_powersetCard, hP, hzz, eq_comm, and_assoc, and_left_comm,
        and_comm]
  rw [hFiber, Finset.card_image_of_injective]
  · simp [L, starLayerPrefixDegree]
  · intro T₁ T₂ h
    exact congrArg Prod.snd h

/-- Finite actual deletion bound for separating all star shadows. The square
root scale follows from the true parent-family codegree caps, via the actual
collision moment and the owner-degree Cauchy inequality. -/
theorem actualStarLayerOwnershipDeletion_card_sq_le
    [Inhabited α] {H : Family α} {U Centers : Edge α} {r D₂ D₃ : ℕ}
    (hH : Admissible H)
    (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (owner : Edge α → α)
    (hOwner : ∀ P ∈ U.powersetCard (r - 2), owner P ∈ Centers)
    (hMax : ∀ P ∈ U.powersetCard (r - 2), ∀ z ∈ Centers,
      starLayerPrefixDegree (actualStarLink H U z r) P ≤
        starLayerPrefixDegree (actualStarLink H U (owner P) r) P) :
    ((actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
      ∃ P ∈ actualStarLayerFacets U zT.2 r,
        P ∈ U.powersetCard (r - 2) ∧ owner P ≠ zT.1).card ^ 2 ≤
      (U.powersetCard (r - 2)).card *
        (Centers.card * (Centers.card - 1) *
          ((r - 1) * (r - 1) * D₂ +
            U.card * (U.card - 1) * (r - 2) * D₃)) := by
  classical
  let P := U.powersetCard (r - 2)
  have hDeletion := actual_star_layer_ownership_deletion_bound
    H U Centers r owner
  have hSum :
      (∑ Q ∈ P,
        badShadowDegree (actualStarLayerObjects H U Centers r)
          Prod.fst
          (fun zT : α × Edge α => actualStarLayerFacets U zT.2 r)
          owner Q) =
        ∑ Q ∈ P, ∑ z ∈ Centers.erase (owner Q),
          starLayerPrefixDegree (actualStarLink H U z r) Q := by
    apply Finset.sum_congr rfl
    intro Q hQ
    exact actualStarLayer_badShadowDegree_eq_nonowner_sum owner Q hQ
  have hSquare := actualStarLayerNonownerDegree_sq_le
    hH hCenters hr hD₂ hD₃ owner hOwner hMax
  have hCard :
      ((actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
        ∃ Q ∈ actualStarLayerFacets U zT.2 r,
          Q ∈ U.powersetCard (r - 2) ∧ owner Q ≠ zT.1).card ≤
        ∑ Q ∈ P,
          badShadowDegree (actualStarLayerObjects H U Centers r)
            Prod.fst
            (fun zT : α × Edge α => actualStarLayerFacets U zT.2 r)
            owner Q := hDeletion
  have hCardSq := Nat.pow_le_pow_left hCard 2
  calc
    _ ≤ (∑ Q ∈ P,
        badShadowDegree (actualStarLayerObjects H U Centers r)
          Prod.fst
          (fun zT : α × Edge α => actualStarLayerFacets U zT.2 r)
          owner Q) ^ 2 := hCardSq
    _ = (∑ Q ∈ P, ∑ z ∈ Centers.erase (owner Q),
          starLayerPrefixDegree (actualStarLink H U z r) Q) ^ 2 := by
        rw [hSum]
    _ ≤ P.card * (Centers.card * (Centers.card - 1) *
          ((r - 1) * (r - 1) * D₂ +
            U.card * (U.card - 1) * (r - 2) * D₃)) := by
        simpa [P] using hSquare

/-- The finite separation bound with the maximizing owner chosen
internally. Empty center sets have no colored members to delete. -/
theorem actualStarLayerOwnershipDeletion_card_sq_le_exists_max
    [Inhabited α] {H : Family α} {U Centers : Edge α} {r D₂ D₃ : ℕ}
    (hH : Admissible H)
    (hCenters : ∀ z ∈ Centers, z ∉ U)
    (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    ∃ owner : Edge α → α,
      ((actualStarLayerObjects H U Centers r).filter fun zT : α × Edge α =>
        ∃ P ∈ actualStarLayerFacets U zT.2 r,
          P ∈ U.powersetCard (r - 2) ∧ owner P ≠ zT.1).card ^ 2 ≤
        (U.powersetCard (r - 2)).card *
          (Centers.card * (Centers.card - 1) *
            ((r - 1) * (r - 1) * D₂ +
              U.card * (U.card - 1) * (r - 2) * D₃)) := by
  classical
  by_cases hNonempty : Centers.Nonempty
  · let owner : Edge α → α := fun P =>
      Classical.choose
        (Finset.exists_max_image Centers
          (fun z => starLayerPrefixDegree (actualStarLink H U z r) P)
          hNonempty)
    have hOwner : ∀ P ∈ U.powersetCard (r - 2), owner P ∈ Centers := by
      intro P hP
      exact (Classical.choose_spec
        (Finset.exists_max_image Centers
          (fun z => starLayerPrefixDegree (actualStarLink H U z r) P)
          hNonempty)).1
    have hMax : ∀ P ∈ U.powersetCard (r - 2), ∀ z ∈ Centers,
        starLayerPrefixDegree (actualStarLink H U z r) P ≤
          starLayerPrefixDegree (actualStarLink H U (owner P) r) P := by
      intro P hP z hz
      exact (Classical.choose_spec
        (Finset.exists_max_image Centers
          (fun z => starLayerPrefixDegree (actualStarLink H U z r) P)
          hNonempty)).2 z hz
    exact ⟨owner, actualStarLayerOwnershipDeletion_card_sq_le
      hH hCenters hr hD₂ hD₃ owner hOwner hMax⟩
  · have hEmpty : Centers = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hNonempty
    refine ⟨fun _ => default, ?_⟩
    simp [actualStarLayerObjects, hEmpty]

end JSP523.Rank5
