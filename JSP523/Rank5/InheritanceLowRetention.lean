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

end JSP523.Rank5
