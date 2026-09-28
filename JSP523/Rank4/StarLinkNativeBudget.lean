import JSP523.Rank4.StarLinkPairRoots
import JSP523.Rank3.RootedWeightSum

/-!
# Aggregating star-link pair payments

This file sums the fixed-size sampled link estimate across ordered
completion pairs.  A used pair gets the native-label saving; every other
pair receives the unrestricted root bound.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- The ordered presentation counts each actual used two-element pair
twice. -/
theorem ordered_used_pair_membership_count
    (U : Finset α) (C : Family α)
    (hC : C ⊆ U.powersetCard 2) :
    (∑ a ∈ U, ∑ b ∈ U.erase a,
      if ({a, b} : Edge α) ∈ C then (1 : ℚ) else 0) =
        2 * C.card := by
  classical
  have hOrdered := JSP523.Rank3.ordered_pair_sum_eq_twice_unordered
    U (fun P => if P ∈ C then (1 : ℚ) else 0)
  have hFilter : (U.powersetCard 2).filter (fun P => P ∈ C) = C := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hPC
      exact ⟨hC hPC, hPC⟩
  calc
    (∑ a ∈ U, ∑ b ∈ U.erase a,
      if ({a, b} : Edge α) ∈ C then (1 : ℚ) else 0) =
      2 * (∑ P ∈ U.powersetCard 2,
        if P ∈ C then (1 : ℚ) else 0) := hOrdered
    _ = 2 * C.card := by
      rw [← Finset.sum_filter, hFilter]
      simp

omit [Fintype α] in
/-- Count all ordered distinct pairs on the actual ground set. -/
theorem ordered_ground_pair_count
    (U : Finset α) (hU : 1 ≤ U.card) :
    (∑ a ∈ U, ∑ _b ∈ U.erase a, (1 : ℚ)) =
      (U.card : ℚ) * ((U.card : ℚ) - 1) := by
  classical
  calc
    (∑ a ∈ U, ∑ _b ∈ U.erase a, (1 : ℚ)) =
      ∑ a ∈ U, ((U.erase a).card : ℚ) := by
        apply Finset.sum_congr rfl
        intro a _
        simp
    _ = ∑ _a ∈ U, ((U.card - 1 : ℕ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.card_erase_of_mem ha]
    _ = (U.card : ℚ) * ((U.card : ℚ) - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Nat.cast_sub (by omega : 1 ≤ U.card)]
        norm_num

omit [Fintype α] in
/-- A two-valued payment summed over ordered pairs is determined by the
number of used pairs and the total number of ordered ground pairs. -/
theorem ordered_pair_two_value_sum
    (U : Finset α) (C : Family α)
    (hC : C ⊆ U.powersetCard 2)
    (hU : 1 ≤ U.card) (r s : ℚ) :
    (∑ a ∈ U, ∑ b ∈ U.erase a,
      if ({a, b} : Edge α) ∈ C then r else s) =
      2 * C.card * r +
        ((U.card : ℚ) * ((U.card : ℚ) - 1) -
          2 * C.card) * s := by
  classical
  have hPoint (a b : α) :
      (if ({a, b} : Edge α) ∈ C then r else s) =
        s + (r - s) *
          (if ({a, b} : Edge α) ∈ C then (1 : ℚ) else 0) := by
    split_ifs <;> ring
  calc
    (∑ a ∈ U, ∑ b ∈ U.erase a,
      if ({a, b} : Edge α) ∈ C then r else s) =
      ∑ a ∈ U, ∑ b ∈ U.erase a,
        (s + (r - s) *
          (if ({a, b} : Edge α) ∈ C then (1 : ℚ) else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          exact hPoint a b
    _ = (∑ a ∈ U, ∑ _b ∈ U.erase a, s) +
        (r - s) * (∑ a ∈ U, ∑ b ∈ U.erase a,
          if ({a, b} : Edge α) ∈ C then (1 : ℚ) else 0) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * C.card * r +
        ((U.card : ℚ) * ((U.card : ℚ) - 1) -
          2 * C.card) * s := by
          have hAllScaled := congrArg (fun q : ℚ => q * s)
            (ordered_ground_pair_count U hU)
          simp only [Finset.sum_mul, one_mul] at hAllScaled
          rw [hAllScaled, ordered_used_pair_membership_count U C hC]
          ring

/-- The finite star-layer pair payment after summing the sampled link
estimate.  Used pairs have a single exceptional root; unused pairs may
occur at every root other than their endpoints. -/
theorem star_link_sample_payment_aggregate
    (A : Family α) (U : Finset α) (m : ℕ)
    (C : Family α) (label : Edge α → α)
    (hC : C ⊆ U.powersetCard 2)
    (hU : 3 ≤ U.card) (hm : 3 ≤ m)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (hOff : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ C →
      ∀ x ∈ U, x ≠ label ({a, b} : Edge α) →
        graphCommonMultiplicity
          (JSP523.Coarse.tripleLinkGraph A x) a b ≤ 1) :
    ((U.card - 3).choose (m - 3) : ℚ) *
        (∑ x ∈ U,
          orderedUniquePairCount (JSP523.Coarse.tripleLinkGraph A x)) +
      ((U.card - 2).choose (m - 2) : ℚ) *
        (∑ x ∈ U,
          orderedMultiPairCount (JSP523.Coarse.tripleLinkGraph A x)) ≤
      2 * (C.card : ℚ) *
        (((U.card - 2).choose (m - 2) : ℚ) +
          (U.card - 3) *
            ((U.card - 3).choose (m - 3) : ℚ)) +
      ((U.card : ℚ) * ((U.card : ℚ) - 1) -
        2 * C.card) *
        ((U.card - 2) *
          ((U.card - 2).choose (m - 2) : ℚ)) := by
  classical
  let c₃ : ℚ := (U.card - 3).choose (m - 3)
  let c₂ : ℚ := (U.card - 2).choose (m - 2)
  let used : ℚ := c₂ + (U.card - 3) * c₃
  let unused : ℚ := (U.card - 2) * c₂
  have hPoint (a : α) (ha : a ∈ U)
      (b : α) (hb : b ∈ U.erase a) :
      c₃ * (starLinkUniqueRoots A U a b).card +
        c₂ * (starLinkMultiRoots A U a b).card ≤
          if ({a, b} : Edge α) ∈ C then used else unused := by
    have hbU : b ∈ U := (Finset.mem_erase.mp hb).2
    have hab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
    by_cases hUsed : ({a, b} : Edge α) ∈ C
    · simp only [hUsed, ↓reduceIte]
      dsimp [used, c₂, c₃]
      exact star_link_used_pair_sample_payment A U m hUniform
        ha hbU hab hU hm (label ({a, b} : Edge α))
        (hOff a ha b hb hUsed)
    · simp only [hUsed, ↓reduceIte]
      dsimp [unused, c₂, c₃]
      exact star_link_unused_pair_sample_payment A U m hUniform
        a b ha hbU hab hU hm
  have hSum :
      (∑ a ∈ U, ∑ b ∈ U.erase a,
        (c₃ * (starLinkUniqueRoots A U a b).card +
          c₂ * (starLinkMultiRoots A U a b).card)) ≤
      ∑ a ∈ U, ∑ b ∈ U.erase a,
        (if ({a, b} : Edge α) ∈ C then used else unused) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact hPoint a ha b hb
  calc
    ((U.card - 3).choose (m - 3) : ℚ) *
        (∑ x ∈ U,
          orderedUniquePairCount (JSP523.Coarse.tripleLinkGraph A x)) +
      ((U.card - 2).choose (m - 2) : ℚ) *
        (∑ x ∈ U,
          orderedMultiPairCount (JSP523.Coarse.tripleLinkGraph A x)) =
      ∑ a ∈ U, ∑ b ∈ U.erase a,
        (c₃ * (starLinkUniqueRoots A U a b).card +
          c₂ * (starLinkMultiRoots A U a b).card) := by
      rw [sum_star_link_unique_pair_count A U hGround,
        sum_star_link_multi_pair_count A U hGround]
      simp only [Finset.mul_sum, Finset.sum_add_distrib]
      rfl
    _ ≤ ∑ a ∈ U, ∑ b ∈ U.erase a,
        (if ({a, b} : Edge α) ∈ C then used else unused) := hSum
    _ = 2 * (C.card : ℚ) * used +
        ((U.card : ℚ) * ((U.card : ℚ) - 1) -
          2 * C.card) * unused :=
      ordered_pair_two_value_sum U C hC (by omega) used unused
    _ = _ := by rfl

/-- Fixed-size finite star/native inequality after the actual graph
sampling and used-pair payments are combined.  The factor multiplying
the used-pair count is the saving from the native label. -/
theorem star_link_fixed_size_native_budget
    (A : Family α) (U : Finset α) (m : ℕ)
    (C : Family α) (label : Edge α → α)
    (hC : C ⊆ U.powersetCard 2)
    (hU : 3 ≤ U.card) (hm : 3 ≤ m)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (hOff : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ C →
      ∀ x ∈ U, x ≠ label ({a, b} : Edge α) →
        graphCommonMultiplicity
          (JSP523.Coarse.tripleLinkGraph A x) a b ≤ 1) :
    2 * ((U.card - 2).choose (m - 2) : ℚ) *
        (3 * A.card : ℚ) +
      2 * (C.card : ℚ) * (U.card - 3) *
        (((U.card - 2).choose (m - 2) : ℚ) -
          ((U.card - 3).choose (m - 3) : ℚ)) ≤
      (U.card : ℚ) * ((U.card : ℚ) - 1) *
        ((U.card : ℚ) - 2) *
        ((U.card - 2).choose (m - 2) : ℚ) +
      (U.card : ℚ) * (m : ℚ) * (U.card.choose m) := by
  have hSample := sum_triple_link_sampling_inequality
    A U m hm hGround hUniform
  have hPairs := star_link_sample_payment_aggregate
    A U m C label hC hU hm hGround hUniform hOff
  nlinarith

/-- The binomial coefficient for triples in rational form. -/
private theorem six_choose_three (u : ℕ) (hu : 3 ≤ u) :
    (6 : ℚ) * (u.choose 3 : ℚ) =
      (u : ℚ) * ((u : ℚ) - 1) * ((u : ℚ) - 2) := by
  have hNat := Nat.choose_succ_right_eq u 2
  have hThree :
      (u.choose 3 : ℚ) * 3 =
        (u.choose 2 : ℚ) * ((u - 2 : ℕ) : ℚ) := by
    exact_mod_cast hNat
  rw [Nat.cast_sub (by omega : 2 ≤ u)] at hThree
  have hTwo : (u.choose 2 : ℚ) =
      (u : ℚ) * ((u : ℚ) - 1) / 2 := by
    exact Nat.cast_choose_two ℚ u
  rw [hTwo] at hThree
  nlinarith

/-- The abstract native-vertex budget can be inserted without changing
the sampled-link error.  This is the finite fixed-size analogue of the
star/native budget (III.B.14). -/
theorem star_native_fixed_size_budget
    (A : Family α) (U : Finset α) (m : ℕ)
    (C : Family α) (label : Edge α → α) (V : ℕ)
    (hC : C ⊆ U.powersetCard 2)
    (hU : 3 ≤ U.card) (hm : 3 ≤ m)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (hOff : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ C →
      ∀ x ∈ U, x ≠ label ({a, b} : Edge α) →
        graphCommonMultiplicity
          (JSP523.Coarse.tripleLinkGraph A x) a b ≤ 1)
    (hV : V ≤ (U.card - 3) * C.card) :
    2 * ((U.card - 2).choose (m - 2) : ℚ) *
        ((3 * A.card + V : ℕ) : ℚ) ≤
      6 * ((U.card - 2).choose (m - 2) : ℚ) *
        (U.card.choose 3 : ℚ) +
      2 * (C.card : ℚ) * (U.card - 3) *
        ((U.card - 3).choose (m - 3) : ℚ) +
      (U.card : ℚ) * (m : ℚ) * (U.card.choose m) := by
  have hMain := star_link_fixed_size_native_budget
    A U m C label hC hU hm hGround hUniform hOff
  have hVQ : (V : ℚ) ≤
      ((U.card - 3 : ℕ) : ℚ) * (C.card : ℚ) := by
    exact_mod_cast hV
  have hcNonneg :
      0 ≤ ((U.card - 2).choose (m - 2) : ℚ) :=
    Nat.cast_nonneg _
  have hVscaled := mul_le_mul_of_nonneg_left hVQ
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hcNonneg)
  have hUcast : ((U.card - 3 : ℕ) : ℚ) =
      (U.card : ℚ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ U.card)]
    norm_num
  rw [hUcast] at hVscaled
  have hChoose := six_choose_three U.card hU
  have hBase := congrArg
    (fun q : ℚ => q * ((U.card - 2).choose (m - 2) : ℚ))
    hChoose
  have hCast :
      (((3 * A.card + V : ℕ) : ℚ)) =
        3 * (A.card : ℚ) + (V : ℚ) := by
    push_cast
    ring
  rw [hCast]
  nlinarith [hBase]

end JSP523.Rank4
