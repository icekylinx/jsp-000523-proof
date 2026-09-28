import JSP523.Rank4.StarLinkSampling

/-!
# Root counts for a fixed pair in the star-triple links

The uniformity of the triple layer excludes the two pair endpoints as
link roots.  For a labelled used pair, multiplicity at least two can occur
only at its labelled root.  This yields the finite per-pair payment needed
after summing the sampled graph potential.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

private def linkPairMultiplicity
    (A : Family α) (x a b : α) : ℕ :=
  graphCommonMultiplicity (JSP523.Coarse.tripleLinkGraph A x) a b

/-- Roots at which a pair has exactly one common neighbor. -/
def starLinkUniqueRoots
    (A : Family α) (U : Finset α) (a b : α) : Finset α :=
  U.filter fun x => linkPairMultiplicity A x a b = 1

/-- Roots at which a pair has at least two common neighbors. -/
def starLinkMultiRoots
    (A : Family α) (U : Finset α) (a b : α) : Finset α :=
  U.filter fun x => 2 ≤ linkPairMultiplicity A x a b

/-- A positive common-neighbor multiplicity excludes both pair endpoints
as roots of a uniform triple link. -/
theorem star_link_positive_root_ne_pair
    (A : Family α) (hUniform : ∀ T ∈ A, T.card = 3)
    (x a b : α)
    (hPositive : 0 < linkPairMultiplicity A x a b) :
    x ≠ a ∧ x ≠ b := by
  classical
  unfold linkPairMultiplicity graphCommonMultiplicity at hPositive
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hPositive
  have hAy : (JSP523.Coarse.tripleLinkGraph A x).Adj a y := by
    simpa [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_filter.mp hy).1
  have hBy : (JSP523.Coarse.tripleLinkGraph A x).Adj b y :=
    (Finset.mem_filter.mp hy).2
  have hAcard : ({x, a, y} : Edge α).card = 3 :=
    hUniform _ hAy.2
  have hBcard : ({x, b, y} : Edge α).card = 3 :=
    hUniform _ hBy.2
  have hAne := (Finset.card_triple_eq_three_iff.mp hAcard).1
  have hBne := (Finset.card_triple_eq_three_iff.mp hBcard).1
  exact ⟨hAne, hBne⟩

/-- Positive common-neighbor multiplicity also confines both endpoints
to the ground set of the triple layer. -/
theorem star_link_positive_pair_supported
    (A : Family α) (U : Finset α)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (x a b : α)
    (hPositive : 0 < linkPairMultiplicity A x a b) :
    a ∈ U ∧ b ∈ U := by
  classical
  unfold linkPairMultiplicity graphCommonMultiplicity at hPositive
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hPositive
  have hAy : (JSP523.Coarse.tripleLinkGraph A x).Adj a y := by
    simpa [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_filter.mp hy).1
  have hBy : (JSP523.Coarse.tripleLinkGraph A x).Adj b y :=
    (Finset.mem_filter.mp hy).2
  exact ⟨(triple_link_adj_supported A U hGround x a y hAy).1,
    (triple_link_adj_supported A U hGround x b y hBy).1⟩

/-- A positive pair-record predicate can be summed over the actual
ground set instead of all ambient vertices. -/
private theorem link_pair_indicator_restrict
    (A : Family α) (U : Finset α)
    (hGround : ∀ T ∈ A, T ⊆ U)
    (x : α) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ k, p k → 0 < k) :
    (∑ a : α, ∑ b ∈ (Finset.univ : Finset α).erase a,
      if p (linkPairMultiplicity A x a b) then (1 : ℚ) else 0) =
    ∑ a ∈ U, ∑ b ∈ U.erase a,
      if p (linkPairMultiplicity A x a b) then (1 : ℚ) else 0 := by
  classical
  let f : α → α → ℚ := fun a b =>
    if p (linkPairMultiplicity A x a b) then 1 else 0
  have hOutside (a b : α)
      (ha : a ∉ U ∨ b ∉ U) : f a b = 0 := by
    by_cases hEvent : p (linkPairMultiplicity A x a b)
    · have hSupport := star_link_positive_pair_supported
        A U hGround x a b (hp _ hEvent)
      rcases ha with ha | hb
      · exact False.elim (ha hSupport.1)
      · exact False.elim (hb hSupport.2)
    · simp [f, hEvent]
  have hOuter :
      (∑ a : α, ∑ b ∈ (Finset.univ : Finset α).erase a, f a b) =
      ∑ a ∈ U, ∑ b ∈ (Finset.univ : Finset α).erase a, f a b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro a _ haU
    apply Finset.sum_eq_zero
    intro b _
    exact hOutside a b (Or.inl haU)
  rw [hOuter]
  apply Finset.sum_congr rfl
  intro a haU
  symm
  have hSub : U.erase a ⊆ (Finset.univ : Finset α).erase a := by
    intro b hb
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hb).1, Finset.mem_univ _⟩
  apply Finset.sum_subset hSub
  intro b hb hbU
  have hbNot : b ∉ U := by
    intro hb'
    exact hbU (Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hb).1, hb'⟩)
  exact hOutside a b (Or.inr hbNot)

/-- Actual unique-pair records in all rooted links, rewritten as the
number of roots for each ordered ground-set pair. -/
theorem sum_star_link_unique_pair_count
    (A : Family α) (U : Finset α)
    (hGround : ∀ T ∈ A, T ⊆ U) :
    (∑ x ∈ U,
      orderedUniquePairCount (JSP523.Coarse.tripleLinkGraph A x)) =
    ∑ a ∈ U, ∑ b ∈ U.erase a,
      ((starLinkUniqueRoots A U a b).card : ℚ) := by
  classical
  calc
    (∑ x ∈ U,
      orderedUniquePairCount (JSP523.Coarse.tripleLinkGraph A x)) =
      ∑ x ∈ U, ∑ a ∈ U, ∑ b ∈ U.erase a,
        if linkPairMultiplicity A x a b = 1 then (1 : ℚ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          unfold orderedUniquePairCount
          exact link_pair_indicator_restrict A U hGround x
            (fun k => k = 1) (by intro k hk; omega)
    _ = ∑ a ∈ U, ∑ b ∈ U.erase a, ∑ x ∈ U,
          if linkPairMultiplicity A x a b = 1 then (1 : ℚ) else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ a ∈ U, ∑ b ∈ U.erase a,
          ((starLinkUniqueRoots A U a b).card : ℚ) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          unfold starLinkUniqueRoots
          rw [← Finset.sum_filter]
          simp

/-- The same reindexing for pairs with at least two common neighbors. -/
theorem sum_star_link_multi_pair_count
    (A : Family α) (U : Finset α)
    (hGround : ∀ T ∈ A, T ⊆ U) :
    (∑ x ∈ U,
      orderedMultiPairCount (JSP523.Coarse.tripleLinkGraph A x)) =
    ∑ a ∈ U, ∑ b ∈ U.erase a,
      ((starLinkMultiRoots A U a b).card : ℚ) := by
  classical
  calc
    (∑ x ∈ U,
      orderedMultiPairCount (JSP523.Coarse.tripleLinkGraph A x)) =
      ∑ x ∈ U, ∑ a ∈ U, ∑ b ∈ U.erase a,
        if 2 ≤ linkPairMultiplicity A x a b then (1 : ℚ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          unfold orderedMultiPairCount
          exact link_pair_indicator_restrict A U hGround x
            (fun k => 2 ≤ k) (by intro k hk; omega)
    _ = ∑ a ∈ U, ∑ b ∈ U.erase a, ∑ x ∈ U,
          if 2 ≤ linkPairMultiplicity A x a b then (1 : ℚ) else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ a ∈ U, ∑ b ∈ U.erase a,
          ((starLinkMultiRoots A U a b).card : ℚ) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          unfold starLinkMultiRoots
          rw [← Finset.sum_filter]
          simp

/-- Unique and repeated roots occupy at most the roots other than the
pair endpoints. -/
theorem star_link_pair_root_count
    (A : Family α) (U : Finset α)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (a b : α) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) :
    (starLinkUniqueRoots A U a b).card +
      (starLinkMultiRoots A U a b).card ≤ U.card - 2 := by
  classical
  let E := (U.erase a).erase b
  have hDisj : Disjoint (starLinkUniqueRoots A U a b)
      (starLinkMultiRoots A U a b) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx1 := (Finset.mem_filter.mp hx).2
    have hx2 := (Finset.mem_filter.mp hy).2
    unfold linkPairMultiplicity at hx1 hx2
    omega
  have hSub : starLinkUniqueRoots A U a b ∪
      starLinkMultiRoots A U a b ⊆ E := by
    intro x hx
    have hPart := Finset.mem_union.mp hx
    have hxU : x ∈ U := by
      rcases hPart with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    have hPos : 0 < linkPairMultiplicity A x a b := by
      rcases hPart with h | h
      · have hOne := (Finset.mem_filter.mp h).2
        omega
      · have hMany := (Finset.mem_filter.mp h).2
        omega
    obtain ⟨hxa, hxb⟩ :=
      star_link_positive_root_ne_pair A hUniform x a b hPos
    exact Finset.mem_erase.mpr
      ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hxU⟩⟩
  have hCard := Finset.card_le_card hSub
  have hEcard : E.card = U.card - 2 := by
    have hb' : b ∈ U.erase a :=
      Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    simp [E, Finset.card_erase_of_mem hb',
      Finset.card_erase_of_mem ha]
    omega
  rw [Finset.card_union_of_disjoint hDisj, hEcard] at hCard
  exact hCard

/-- If all links outside the selected label have multiplicity at most
one, a repeated-pair root can only be that label. -/
theorem star_link_multi_roots_le_one
    (A : Family α) (U : Finset α) (a b z : α)
    (hOff : ∀ x ∈ U, x ≠ z →
      linkPairMultiplicity A x a b ≤ 1) :
    (starLinkMultiRoots A U a b).card ≤ 1 := by
  have hSub : starLinkMultiRoots A U a b ⊆ {z} := by
    intro x hx
    obtain ⟨hxU, hxMany⟩ := Finset.mem_filter.mp hx
    by_contra hxz
    have hLe := hOff x hxU (by simpa using hxz)
    omega
  exact (Finset.card_le_card hSub).trans (by simp)

/-- Fixed-size sampling payment for a used ordered pair: one exceptional
root may pay the larger pair cost, while all other possible roots pay the
unique-neighbor cost. -/
theorem star_link_used_pair_sample_payment
    (A : Family α) (U : Finset α) (m : ℕ)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (hU : 3 ≤ U.card) (hm : 3 ≤ m)
    (z : α)
    (hOff : ∀ x ∈ U, x ≠ z →
      linkPairMultiplicity A x a b ≤ 1) :
    ((U.card - 3).choose (m - 3) : ℚ) *
        (starLinkUniqueRoots A U a b).card +
      ((U.card - 2).choose (m - 2) : ℚ) *
        (starLinkMultiRoots A U a b).card ≤
      ((U.card - 2).choose (m - 2) : ℚ) +
        (U.card - 3) *
          ((U.card - 3).choose (m - 3) : ℚ) := by
  let c₃ : ℚ := (U.card - 3).choose (m - 3)
  let c₂ : ℚ := (U.card - 2).choose (m - 2)
  have hChooseNat :
      (U.card - 3).choose (m - 3) ≤
        (U.card - 2).choose (m - 2) := by
    have hUeq : U.card - 2 = (U.card - 3) + 1 := by omega
    have hMeq : m - 2 = (m - 3) + 1 := by omega
    rw [hUeq, hMeq, Nat.choose_succ_succ']
    omega
  have hc : c₃ ≤ c₂ := by
    dsimp [c₃, c₂]
    exact_mod_cast hChooseNat
  have hcNonneg : 0 ≤ c₃ := Nat.cast_nonneg _
  have hCount := star_link_pair_root_count A U hUniform a b ha hb hab
  have hCountQ :
      ((starLinkUniqueRoots A U a b).card : ℚ) +
        (starLinkMultiRoots A U a b).card ≤
          ((U.card - 2 : ℕ) : ℚ) := by
    exact_mod_cast hCount
  have hMulti := star_link_multi_roots_le_one A U a b z hOff
  have hMultiQ :
      ((starLinkMultiRoots A U a b).card : ℚ) ≤ 1 := by
    exact_mod_cast hMulti
  have hA := mul_le_mul_of_nonneg_left hCountQ hcNonneg
  have hB := mul_le_mul_of_nonneg_left hMultiQ (sub_nonneg.mpr hc)
  dsimp [c₂, c₃] at *
  have hUcast : ((U.card - 2 : ℕ) : ℚ) = (U.card : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ U.card)]
    norm_num
  rw [hUcast] at hA
  nlinarith

/-- Without a label condition, a fixed pair can contribute at most once
for each root outside its two endpoints. -/
theorem star_link_unused_pair_sample_payment
    (A : Family α) (U : Finset α) (m : ℕ)
    (hUniform : ∀ T ∈ A, T.card = 3)
    (a b : α) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (hU : 3 ≤ U.card) (hm : 3 ≤ m) :
    ((U.card - 3).choose (m - 3) : ℚ) *
        (starLinkUniqueRoots A U a b).card +
      ((U.card - 2).choose (m - 2) : ℚ) *
        (starLinkMultiRoots A U a b).card ≤
      (U.card - 2) *
        ((U.card - 2).choose (m - 2) : ℚ) := by
  let c₃ : ℚ := (U.card - 3).choose (m - 3)
  let c₂ : ℚ := (U.card - 2).choose (m - 2)
  have hChooseNat :
      (U.card - 3).choose (m - 3) ≤
        (U.card - 2).choose (m - 2) := by
    have hUeq : U.card - 2 = (U.card - 3) + 1 := by omega
    have hMeq : m - 2 = (m - 3) + 1 := by omega
    rw [hUeq, hMeq, Nat.choose_succ_succ']
    omega
  have hc : c₃ ≤ c₂ := by
    dsimp [c₃, c₂]
    exact_mod_cast hChooseNat
  have hCount := star_link_pair_root_count A U hUniform a b ha hb hab
  have hCountQ :
      ((starLinkUniqueRoots A U a b).card : ℚ) +
        (starLinkMultiRoots A U a b).card ≤
          ((U.card - 2 : ℕ) : ℚ) := by
    exact_mod_cast hCount
  have hA := mul_le_mul_of_nonneg_right hc
    (Nat.cast_nonneg (starLinkUniqueRoots A U a b).card)
  have hB := mul_le_mul_of_nonneg_left hCountQ
    (Nat.cast_nonneg ((U.card - 2).choose (m - 2)))
  dsimp [c₂, c₃] at *
  have hUcast : ((U.card - 2 : ℕ) : ℚ) = (U.card : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ U.card)]
    norm_num
  rw [hUcast] at hB
  nlinarith

end JSP523.Rank4
