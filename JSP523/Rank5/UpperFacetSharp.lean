import JSP523.Rank5.InheritanceLowRetention

/-! # Sharp upper-facet bicolored-triangle accounting -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

private def upperRotate (p : (α × α) × α) : (α × α) × α :=
  ((p.1.2, p.2), p.1.1)

private def upperRotateTwice (p : (α × α) × α) : (α × α) × α :=
  ((p.2, p.1.1), p.1.2)

omit [DecidableEq α] in
private theorem upper_rotate_thrice (p : (α × α) × α) :
    upperRotate (upperRotateTwice p) = p := by
  cases p with
  | mk xy z => cases xy; rfl

omit [DecidableEq α] in
private theorem upper_rotate_twice_eq (p : (α × α) × α) :
    upperRotate (upperRotate p) = upperRotateTwice p := by
  cases p with
  | mk xy z => cases xy; rfl

private theorem upper_triangle_facet_cell_rotate
    (H : Family α) (V : Edge α) (p : (α × α) × α) :
    upperTriangleFacetCell H V (upperRotate p) =
      upperTriangleFacetCell H V p := by
  classical
  ext A
  simp [upperTriangleFacetCell, upperRotate, and_assoc, and_left_comm, and_comm]

private theorem upper_triangle_facet_cell_rotate_twice
    (H : Family α) (V : Edge α) (p : (α × α) × α) :
    upperTriangleFacetCell H V (upperRotateTwice p) =
      upperTriangleFacetCell H V p := by
  rw [← upper_rotate_twice_eq, upper_triangle_facet_cell_rotate,
    upper_triangle_facet_cell_rotate]

private theorem upper_bicolored_rotate
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {p : (α × α) × α}
    (hp : p ∈ upperBicoloredTriples H V tUpper) :
    upperRotate p ∈ upperBicoloredTriples H V tUpper := by
  classical
  have hyx := upper_singleton_pair_color_symm H V tUpper p.1.1 p.1.2
  have hzx := upper_singleton_pair_color_symm H V tUpper p.1.1 p.2
  simp only [upperBicoloredTriples, upperNonmonochromaticTriples,
    Finset.mem_filter, Finset.mem_product, upperRotate] at hp ⊢
  aesop

private theorem upper_bicolored_covered_by_first_rotations
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    upperBicoloredTriples H V tUpper ⊆
      upperBicoloredFirstTriples H V tUpper ∪
        (upperBicoloredFirstTriples H V tUpper).image upperRotate ∪
        (upperBicoloredFirstTriples H V tUpper).image upperRotateTwice := by
  classical
  intro p hp
  let F := upperBicoloredFirstTriples H V tUpper
  obtain ⟨c₁, c₂, c₃, hRepeat, h₁, h₂, h₃⟩ :=
    (Finset.mem_filter.mp hp).2
  have hxy := upper_singleton_pair_color_symm H V tUpper p.1.1 p.1.2
  have hxz := upper_singleton_pair_color_symm H V tUpper p.1.1 p.2
  have hyz := upper_singleton_pair_color_symm H V tUpper p.1.2 p.2
  rcases hRepeat with h12 | h13 | h23
  · have hpF : p ∈ F := by
      apply Finset.mem_filter.mpr
      exact ⟨hp, by rw [h₁, h₂, h12]⟩
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hpF)))
  · have hRotF : upperRotate p ∈ F := by
      apply Finset.mem_filter.mpr
      refine ⟨upper_bicolored_rotate H V tUpper hp, ?_⟩
      simp only [upperRotate]
      rw [h₃, ← hxy, h₁, h13]
    have hEq : upperRotateTwice (upperRotate p) = p := by
      cases p with
      | mk xy z => cases xy; rfl
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨upperRotate p, hRotF, hEq⟩
  · have hRotF : upperRotateTwice p ∈ F := by
      apply Finset.mem_filter.mpr
      refine ⟨upper_bicolored_rotate H V tUpper
        (upper_bicolored_rotate H V tUpper hp), ?_⟩
      simp only [upperRotateTwice]
      rw [← hxz, h₂, ← hyz, h₃, h23]
    have hEq : upperRotate (upperRotateTwice p) = p :=
      upper_rotate_thrice p
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr
      ⟨upperRotateTwice p, hRotF, hEq⟩

/-- All three placements of the repeated vertex have the pinned IV.8.2
    budget. The factor three only records the three possible placements. -/
theorem upper_bicolored_triangle_weighted_budget
    (H : Family α) (V : Edge α) (tUpper D₂ D₃ D₄ : ℕ)
    (ht : 1 ≤ tUpper)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tUpper * (∑ p ∈ upperBicoloredTriples H V tUpper,
      (upperTriangleFacetCell H V p).card) ≤
      3 * (V.card ^ 2 * D₂ * D₃ * D₄) := by
  classical
  let F := upperBicoloredFirstTriples H V tUpper
  let F₁ := F.image upperRotate
  let F₂ := F.image upperRotateTwice
  let w : ((α × α) × α) → ℕ := fun p =>
    (upperTriangleFacetCell H V p).card
  have hF₁ : (∑ p ∈ F₁, w p) = ∑ p ∈ F, w p := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [w, upper_triangle_facet_cell_rotate]
    · intro p hp q hq heq
      have := congrArg upperRotateTwice heq
      simpa [upperRotate, upperRotateTwice] using this
  have hF₂ : (∑ p ∈ F₂, w p) = ∑ p ∈ F, w p := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [w, upper_triangle_facet_cell_rotate_twice]
    · intro p hp q hq heq
      have := congrArg upperRotate heq
      simpa [upperRotate, upperRotateTwice] using this
  have hCover : upperBicoloredTriples H V tUpper ⊆
      (F ∪ F₁) ∪ F₂ :=
    upper_bicolored_covered_by_first_rotations H V tUpper
  have hSum : (∑ p ∈ upperBicoloredTriples H V tUpper, w p) ≤
      (∑ p ∈ F, w p) + (∑ p ∈ F₁, w p) +
        (∑ p ∈ F₂, w p) := by
    have hSub := Finset.sum_le_sum_of_subset (f := w) hCover
    have hU₁ := Finset.sum_union_inter (s₁ := F) (s₂ := F₁) (f := w)
    have hU₂ := Finset.sum_union_inter
      (s₁ := F ∪ F₁) (s₂ := F₂) (f := w)
    omega
  have hFirst := upper_bicolored_first_triangle_weighted_budget
    H V tUpper D₂ D₃ D₄ ht hD₂ hD₃ hD₄
  change tUpper * (∑ p ∈ upperBicoloredTriples H V tUpper, w p) ≤ _
  calc
    _ ≤ tUpper * ((∑ p ∈ F, w p) + (∑ p ∈ F₁, w p) +
        (∑ p ∈ F₂, w p)) := Nat.mul_le_mul_left _ hSum
    _ = 3 * (tUpper * ∑ p ∈ F, w p) := by rw [hF₁, hF₂]; ring
    _ ≤ 3 * (V.card ^ 2 * D₂ * D₃ * D₄) :=
      Nat.mul_le_mul_left 3 hFirst

/-- The actual parent edges removed for bicolored completion triangles
    satisfy the sharp pinned budget of IV.8.2. -/
theorem upper_bicolored_triangle_edges_sharp_budget
    (H : Family α) (V : Edge α) (tUpper D₂ D₃ D₄ : ℕ)
    (ht : 1 ≤ tUpper)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tUpper * (upperBicoloredTriangleEdges H V tUpper).card ≤
      9 * (V.card ^ 2 * D₂ * D₃ * D₄) := by
  classical
  let T := upperBicoloredTriples H V tUpper
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
  have hEdges : (upperBicoloredTriangleEdges H V tUpper).card ≤
      3 * ∑ p ∈ T, (cell p).card := by
    calc
      _ ≤ ∑ p ∈ T,
          ((cell p).biUnion fun A =>
            ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ T, 3 * (cell p).card := Finset.sum_le_sum hFiber
      _ = 3 * ∑ p ∈ T, (cell p).card := by rw [Finset.mul_sum]
  have hWeighted := upper_bicolored_triangle_weighted_budget
    H V tUpper D₂ D₃ D₄ ht hD₂ hD₃ hD₄
  calc
    tUpper * (upperBicoloredTriangleEdges H V tUpper).card ≤
        tUpper * (3 * ∑ p ∈ T, (cell p).card) :=
      Nat.mul_le_mul_left _ hEdges
    _ = 3 * (tUpper * ∑ p ∈ T, (cell p).card) := by ring
    _ ≤ 3 * (3 * (V.card ^ 2 * D₂ * D₃ * D₄)) :=
      Nat.mul_le_mul_left 3 hWeighted
    _ = 9 * (V.card ^ 2 * D₂ * D₃ * D₄) := by ring

/-- Sharp IV.8.1–IV.8.3 edge-deletion budget, multiplied by the positive
    threshold so the pinned contribution remains integral. -/
theorem upper_facet_color_cleanup_edges_sharp_budget
    (H : Family α) (V : Edge α) (tUpper D D₂ D₃ D₄ : ℕ)
    (hAdm : Admissible H)
    (ht : 1 ≤ tUpper)
    (hPairCap : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    tUpper * (upperFacetColorCleanupEdges H V tUpper).card ≤
      tUpper * (2 * V.card ^ 2 * (tUpper + 16 * D) +
        3 * V.card ^ 3 * D₄) +
      9 * (V.card ^ 2 * D₂ * D₃ * D₄) := by
  have hU := upper_uncolored_facet_edges_actual_budget
    H V tUpper D hAdm hPairCap
  have hB := upper_bicolored_triangle_edges_sharp_budget
    H V tUpper D₂ D₃ D₄ ht hD₂ hD₃ hD₄
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
  nlinarith

end JSP523.Rank5
