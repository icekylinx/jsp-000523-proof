import JSP523.Rank3.RootCommonLinkFibers

/-!
# Actual charge sent from a rooted source edge

For a source pair with at least two completion vertices, the manuscript
distributes its positive rooted weight equally among the other completion
vertices.  The conservation identity below uses the real completion degree.
The destination restriction follows from the admissible common-link
obstruction, rather than from a free capacity assumption.
-/

namespace JSP523.Rank3

section ChargeTransfer

variable {α : Type*} [DecidableEq α]

/-- Positive part of one actual signed weight. -/
def positiveRootedWeight
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  max (rootedSignedWeight H V z x y) 0

/-- The charge sent from source `(z,{x,y})` to each other completion
    vertex.  It is used only when the source pair has degree at least two. -/
def chargePerOtherCompletion
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  positiveRootedWeight H V z x y /
    (((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1)

/-- The root of an actual link edge is a completion vertex of that edge's
    underlying pair, when the root lies in the ambient ground set. -/
theorem root_mem_source_completion
    (H : Family α) (V : Edge α) {z x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z) :
    z ∈ completionVertices H V ({x, y} : Edge α) := by
  obtain ⟨_, hzOut, hxz⟩ := Finset.mem_filter.mp hsource
  exact Finset.mem_filter.mpr ⟨hzV, hzOut, hxz⟩

/-- Every positive source with at least two completions sends exactly its
    whole positive weight across the other completion vertices. -/
theorem outgoing_charge_conservation
    (H : Family α) (V : Edge α) {z x y : α}
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hdegree : 2 ≤
      (completionVertices H V ({x, y} : Edge α)).card) :
    (∑ _v ∈ (completionVertices H V ({x, y} : Edge α)).erase z,
      chargePerOtherCompletion H V z x y) =
      positiveRootedWeight H V z x y := by
  let N := completionVertices H V ({x, y} : Edge α)
  have hzN : z ∈ N := root_mem_source_completion H V hzV hsource
  have hCardNat := Finset.card_erase_add_one hzN
  have hCardQ : ((N.erase z).card : ℚ) = (N.card : ℚ) - 1 := by
    have hCast : ((N.erase z).card : ℚ) + 1 = (N.card : ℚ) := by
      exact_mod_cast hCardNat
    linarith
  have hDen : (N.card : ℚ) - 1 ≠ 0 := by
    have hCast : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  change (∑ _v ∈ N.erase z,
    positiveRootedWeight H V z x y / ((N.card : ℚ) - 1)) = _
  rw [Finset.sum_const, nsmul_eq_mul, hCardQ]
  field_simp

/-- A positive source can only send charge toward a cell with one or two
    common-link base pairs. -/
theorem positive_charge_receiver_card_le_two
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hpositive : 0 < positiveRootedWeight H V z x y) :
    (commonLink H V ({z, v} : Edge α)).card ≤ 2 := by
  have hvComp : v ∈ completionVertices H V ({x, y} : Edge α) :=
    (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hwPos : 0 < rootedSignedWeight H V z x y := by
    simpa [positiveRootedWeight] using hpositive
  exact positive_source_receiving_link_card_le_two
    hH hzV hsource hxy hvComp hzv hwPos

/-- At a two-base-pair receiver, every individual directed charge is
    strictly less than one.  This uses the actual source degree in the
    denominator and the book-pair weak alternative in the numerator. -/
theorem charge_lt_one_of_double_receiver
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z)
    (hdouble : (commonLink H V ({z, v} : Edge α)).card = 2) :
    chargePerOtherCompletion H V z x y < 1 := by
  let N := completionVertices H V ({x, y} : Edge α)
  have hvN : v ∈ N := (Finset.mem_erase.mp hv).2
  have hzv : z ≠ v := Ne.symm (Finset.mem_erase.mp hv).1
  have hvV : v ∈ V := (Finset.mem_filter.mp hvN).1
  have hzN : z ∈ N := root_mem_source_completion H V hzV hsource
  have hpair : ({z, v} : Edge α) ⊆ N := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htz | htv
    · exact htz ▸ hzN
    · exact (Finset.mem_singleton.mp htv) ▸ hvN
  have hdegree : 2 ≤ N.card := by
    have hbound := Finset.card_le_card hpair
    rw [Finset.card_pair hzv] at hbound
    exact hbound
  have hden : (1 : ℚ) ≤ (N.card : ℚ) - 1 := by
    have hcast : (2 : ℚ) ≤ N.card := by exact_mod_cast hdegree
    linarith
  have hsourceLink := source_pair_mem_receiving_link H V hsource hvN
  have hdoubleOrient : (orientedCommonLink H V z v).card = 2 := by
    have heq : commonLink H V ({z, v} : Edge α) =
        orientedCommonLink H V z v := by
      ext p
      exact mem_common_link_pair_iff_oriented H V hzv p
    rw [← heq]
    exact hdouble
  have hweight := rooted_signed_weight_lt_one_of_double_receiving_link
    hH hzV hvV hzv hxy hsourceLink hdoubleOrient
  have hpositive : positiveRootedWeight H V z x y < 1 := by
    by_cases hw : rootedSignedWeight H V z x y ≤ 0
    · simp [positiveRootedWeight, max_eq_right hw]
    · have hwNonneg : 0 ≤ rootedSignedWeight H V z x y :=
        le_of_lt (lt_of_not_ge hw)
      simpa [positiveRootedWeight, max_eq_left hwNonneg] using hweight
  have hpNonneg : 0 ≤ positiveRootedWeight H V z x y := by
    unfold positiveRootedWeight
    exact le_max_right _ _
  have hchargeLe : chargePerOtherCompletion H V z x y ≤
      positiveRootedWeight H V z x y := by
    unfold chargePerOtherCompletion
    change positiveRootedWeight H V z x y / ((N.card : ℚ) - 1) ≤ _
    apply (div_le_iff₀ (by linarith : 0 < (N.card : ℚ) - 1)).mpr
    nlinarith [mul_nonneg hpNonneg (by linarith : 0 ≤ (N.card : ℚ) - 2)]
  exact lt_of_le_of_lt hchargeLe hpositive

end ChargeTransfer

end JSP523.Rank3
