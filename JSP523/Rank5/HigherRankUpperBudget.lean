import JSP523.Rank5.HigherRankUpperColor

/-! # Singleton colors and actual IV.8 cell budgets at arbitrary facet rank

The repeated-color bound uses the facet-size codegree cap. Rainbow cells
use the fixed four-codegree cap, independently of the facet rank.
-/

namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α] (n : ℕ)

theorem upper_uncolored_facet_edges_card_le_ambient_square
    (H : Family α) (V : Edge α) (tUpper C : ℕ)
    (hCell : ∀ p ∈ upperUncoloredPairs n H V tUpper,
      (commonPrefixTails H V ({p.1} : Edge α)
        ({p.2} : Edge α) n).card ≤ C) :
    (upperUncoloredFacetEdges n H V tUpper).card ≤
      2 * V.card ^ 2 * C := by
  classical
  have hCells := upper_uncolored_facet_edges_card_le_cells n H V tUpper
  have hSum :
      (∑ p ∈ upperUncoloredPairs n H V tUpper,
        (commonPrefixTails H V ({p.1} : Edge α)
          ({p.2} : Edge α) n).card) ≤
        (upperUncoloredPairs n H V tUpper).card * C := by
    calc
      _ ≤ ∑ _p ∈ upperUncoloredPairs n H V tUpper, C :=
        Finset.sum_le_sum hCell
      _ = (upperUncoloredPairs n H V tUpper).card * C := by simp
  have hPair : (upperUncoloredPairs n H V tUpper).card ≤ V.card ^ 2 := by
    calc
      _ ≤ (V ×ˢ V).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = V.card ^ 2 := by simp [Finset.card_product, pow_two]
  calc
    (upperUncoloredFacetEdges n H V tUpper).card ≤
        2 * ∑ p ∈ upperUncoloredPairs n H V tUpper,
          (commonPrefixTails H V ({p.1} : Edge α)
            ({p.2} : Edge α) n).card := hCells
    _ ≤ 2 * ((upperUncoloredPairs n H V tUpper).card * C) :=
      Nat.mul_le_mul_left 2 hSum
    _ ≤ 2 * V.card ^ 2 * C := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right C hPair) |>.trans_eq (by ring)

theorem upper_uncolored_pair_cell_bound
    (H : Family α) (V : Edge α) (tUpper D : ℕ)
    (hn : 1 ≤ n) (hAdm : Admissible H)
    (hCap : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D)
    {x y : α} (_hx : x ∈ V) (_hy : y ∈ V) (hxy : x ≠ y)
    (hNone : upperSingletonPairColor n H V tUpper x y = none) :
    (commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) n).card ≤
      tUpper + (n * n) * D := by
  classical
  let cell := commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) n
  change cell.card ≤ tUpper + (n * n) * D
  by_cases hSmall : cell.card < tUpper
  · omega
  have hLarge : tUpper ≤ cell.card := by omega
  have hNoUnique : ∀ z : α, ¬ UniqueCellCenter cell z := by
    intro z hz
    have hExists : ∃ w : α, tUpper ≤ cell.card ∧ UniqueCellCenter cell w :=
      ⟨z, hLarge, hz⟩
    have hColor : upperSingletonPairColor n H V tUpper x y ≠ none := by
      simp [upperSingletonPairColor, hExists, cell]
    exact hColor hNone
  by_cases hEmpty : cell = ∅
  · simp [hEmpty]
  have hMember : ∃ A, A ∈ cell := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨A, hA⟩ := hMember
  have hY : ({x} : Edge α).Nonempty := by simp
  have hZ : ({y} : Edge α).Nonempty := by simp
  have hDisj : Disjoint ({x} : Edge α) ({y} : Edge α) := by
    simpa [Finset.disjoint_singleton] using hxy
  have hCellCap : ∀ Q : Edge α, Q.card = 2 →
      (cell.filter fun A => Q ⊆ A).card ≤ D := by
    intro Q hQ
    by_cases hxQ : x ∈ Q
    · have hEmpty : (cell.filter fun A => Q ⊆ A) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        have hd := Finset.mem_filter.mp hA
        have hc := mem_common_prefix_tails.mp hd.1
        exact (Finset.disjoint_left.mp hc.2.2.1) (hd.2 hxQ)
          (Finset.mem_union_left _ (Finset.mem_singleton_self x))
      simp [hEmpty]
    · have hCard : (({x} : Edge α) ∪ Q).card = 3 := by
        rw [Finset.singleton_union, Finset.card_insert_of_notMem hxQ, hQ]
      exact (JSP523.common_prefix_tails_fiber_le_parent_degree
        (H := H) (W := V) (Y := ({x} : Edge α))
        (Z := ({y} : Edge α)) (S := Q) (t := n)).trans
          (hCap _ hCard)
  by_cases hNoCenter : NoGlobalCenter cell
  · have hBound := JSP523.intersecting_card_le_pair_cap
      (fun P hP => (mem_common_prefix_tails.mp hP).2.1)
      (JSP523.common_prefix_tails_intersecting hAdm hY hZ hDisj (by omega : 1 ≤ n))
      hNoCenter hA (by omega) hCellCap
    change cell.card ≤ n * n * D at hBound
    omega
  · have hCenter : ∃ z : α, ∀ B ∈ cell, z ∈ B := by
      by_contra h
      exact hNoCenter (by
        intro z
        by_contra hz
        exact h ⟨z, by intro B hB; by_contra hzB; exact hz ⟨B, hB, hzB⟩⟩)
    obtain ⟨z, hz⟩ := hCenter
    have hAnother : ∃ w : α, w ≠ z ∧ ∀ B ∈ cell, w ∈ B := by
      by_contra h
      apply hNoUnique z
      refine ⟨hz, ?_⟩
      intro w hw
      by_contra hwz
      exact h ⟨w, hwz, hw⟩
    obtain ⟨w, hwz, hw⟩ := hAnother
    have hBound := JSP523.intersecting_card_le_common_pair_cap
      hwz.symm hz hw hCellCap
    change cell.card ≤ D at hBound
    have hMult : D ≤ n * n * D := by
      calc
        D = 1 * 1 * D := by ring
        _ ≤ n * n * D := by gcongr
    omega

theorem upper_uncolored_facet_edges_actual_budget
    (H : Family α) (V : Edge α) (tUpper D : ℕ)
    (hn : 1 ≤ n) (hAdm : Admissible H)
    (hCap : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D) :
    (upperUncoloredFacetEdges n H V tUpper).card ≤
      2 * V.card ^ 2 * (tUpper + (n * n) * D) := by
  apply upper_uncolored_facet_edges_card_le_ambient_square n
    H V tUpper (tUpper + (n * n) * D)
  intro p hp
  have hParts := Finset.mem_filter.mp hp
  have hV := Finset.mem_product.mp hParts.1
  exact upper_uncolored_pair_cell_bound n H V tUpper D hn hAdm hCap
    hV.1 hV.2 hParts.2.1 hParts.2.2

noncomputable def upperRainbowTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact (upperNonmonochromaticTriples n H V tUpper).filter fun p =>
    ∃ c₁ c₂ c₃ : α,
      c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
      upperSingletonPairColor n H V tUpper p.1.1 p.1.2 = some c₁ ∧
      upperSingletonPairColor n H V tUpper p.1.1 p.2 = some c₂ ∧
      upperSingletonPairColor n H V tUpper p.1.2 p.2 = some c₃

theorem upper_rainbow_triangle_facet_cell_le_four_codegree
    (H : Family α) (V : Edge α) (tUpper D₄ : ℕ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    {p : (α × α) × α}
    (hp : p ∈ upperRainbowTriples n H V tUpper) :
    (upperTriangleFacetCell n H V p).card ≤ D₄ := by
  classical
  obtain ⟨hTriangle, c₁, c₂, c₃, h12, h13, h23,
    hc₁, hc₂, hc₃⟩ := Finset.mem_filter.mp hp
  have hProd := (Finset.mem_filter.mp hTriangle).1
  have hVparts := Finset.mem_product.mp hProd
  have hXY := Finset.mem_product.mp hVparts.1
  have hx : p.1.1 ∈ V := hXY.1
  have hy : p.1.2 ∈ V := hXY.2
  have hz : p.2 ∈ V := hVparts.2
  have hDistinct := (Finset.mem_filter.mp hTriangle).2
  let cell := upperTriangleFacetCell n H V p
  have hLabels : ∀ A ∈ cell, c₁ ∈ A ∧ c₂ ∈ A ∧ c₃ ∈ A := by
    intro A hA
    have hAparts := Finset.mem_filter.mp hA
    have hAV := (Finset.mem_powersetCard.mp hAparts.1).1
    have hAcard := (Finset.mem_powersetCard.mp hAparts.1).2
    rcases hAparts.2 with ⟨hxA, hyA, hzA, hEx, hEy, hEz⟩
    constructor
    · exact upper_pair_color_label_mem_supporting_facet n H V A tUpper
        hx hy hDistinct.1 hAV hAcard hxA hyA hEx hEy hc₁
    constructor
    · exact upper_pair_color_label_mem_supporting_facet n H V A tUpper
        hx hz hDistinct.2.1 hAV hAcard hxA hzA hEx hEz hc₂
    · exact upper_pair_color_label_mem_supporting_facet n H V A tUpper
        hy hz hDistinct.2.2.1 hAV hAcard hyA hzA hEy hEz hc₃
  by_cases hEmpty : cell = ∅
  · change cell.card ≤ D₄
    simp [hEmpty]
  have hCellEmpty : cell.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hEmpty
  let S : Edge α := {p.1.1, c₁, c₂, c₃}
  have hXneq : p.1.1 ≠ c₁ ∧ p.1.1 ≠ c₂ ∧ p.1.1 ≠ c₃ := by
    obtain ⟨A, hA⟩ := hCellEmpty
    have hNot : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
    have hLab := hLabels A hA
    exact ⟨fun h => hNot (h ▸ hLab.1),
      fun h => hNot (h ▸ hLab.2.1),
      fun h => hNot (h ▸ hLab.2.2)⟩
  have hScard : S.card = 4 := by
    simp [S, hXneq.1, hXneq.2.1, hXneq.2.2,
      h12, h13, h23]
  have hInject : cell.card ≤ (H.filter fun E => S ⊆ E).card := by
    apply Finset.card_le_card_of_injOn (fun A => insert p.1.1 A)
    · intro A hA
      have hParts := (Finset.mem_filter.mp hA).2
      have hLab := hLabels A hA
      refine Finset.mem_filter.mpr ⟨hParts.2.2.2.1, ?_⟩
      intro v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | hv
      · exact Finset.mem_insert_self ..
      rcases hv with rfl | hv
      · exact Finset.mem_insert_of_mem hLab.1
      rcases hv with rfl | rfl
      · exact Finset.mem_insert_of_mem hLab.2.1
      · exact Finset.mem_insert_of_mem hLab.2.2
    · intro A hA B hB hEq
      have hxA : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
      have hxB : p.1.1 ∉ B := (Finset.mem_filter.mp hB).2.1
      have hErase := congrArg (Finset.erase · p.1.1) hEq
      simpa [hxA, hxB] using hErase
  exact hInject.trans (hD₄ S hScard)

noncomputable def upperRainbowTriangleEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperRainbowTriples n H V tUpper).biUnion fun p =>
    (upperTriangleFacetCell n H V p).biUnion fun A =>
      ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)

theorem upper_rainbow_triangle_edges_actual_budget
    (H : Family α) (V : Edge α) (tUpper D₄ : ℕ)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄) :
    (upperRainbowTriangleEdges n H V tUpper).card ≤
      3 * V.card ^ 3 * D₄ := by
  classical
  let T := upperRainbowTriples n H V tUpper
  let cell := upperTriangleFacetCell n H V
  have hFiber : ∀ p ∈ T,
      ((cell p).biUnion fun A =>
        ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card ≤
          3 * D₄ := by
    intro p hp
    have hCap := upper_rainbow_triangle_facet_cell_le_four_codegree n
      H V tUpper D₄ hD₄ hp
    calc
      _ ≤ ∑ A ∈ cell p,
          ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ cell p, 3 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Finset.card_le_three
      _ = 3 * (cell p).card := by simp [mul_comm]
      _ ≤ 3 * D₄ := Nat.mul_le_mul_left 3 hCap
  have hTriple : T.card ≤ V.card ^ 3 := by
    calc
      T.card ≤ ((V ×ˢ V) ×ˢ V).card :=
        Finset.card_le_card ((Finset.filter_subset _ _).trans
          (Finset.filter_subset _ _))
      _ = V.card ^ 3 := by simp [Finset.card_product, pow_succ]
  calc
    (upperRainbowTriangleEdges n H V tUpper).card ≤
        ∑ p ∈ T,
          ((cell p).biUnion fun A =>
            ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ T, 3 * D₄ := Finset.sum_le_sum hFiber
    _ = T.card * (3 * D₄) := by simp
    _ ≤ V.card ^ 3 * (3 * D₄) := Nat.mul_le_mul_right _ hTriple
    _ = 3 * V.card ^ 3 * D₄ := by ring

noncomputable def upperBicoloredTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact (upperNonmonochromaticTriples n H V tUpper).filter fun p =>
    ∃ c₁ c₂ c₃ : α,
      (c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃) ∧
      upperSingletonPairColor n H V tUpper p.1.1 p.1.2 = some c₁ ∧
      upperSingletonPairColor n H V tUpper p.1.1 p.2 = some c₂ ∧
      upperSingletonPairColor n H V tUpper p.1.2 p.2 = some c₃

theorem upper_nonmonochromatic_triples_eq_bicolored_union_rainbow
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    upperNonmonochromaticTriples n H V tUpper =
      upperBicoloredTriples n H V tUpper ∪
        upperRainbowTriples n H V tUpper := by
  classical
  ext p
  constructor
  · intro hp
    have hParts := (Finset.mem_filter.mp hp).2
    have hNot₁ := hParts.2.2.2.1
    have hNot₂ := hParts.2.2.2.2.1
    have hNot₃ := hParts.2.2.2.2.2.1
    cases h₁ : upperSingletonPairColor n H V tUpper p.1.1 p.1.2 with
    | none => exact False.elim (hNot₁ h₁)
    | some c₁ =>
      cases h₂ : upperSingletonPairColor n H V tUpper p.1.1 p.2 with
      | none => exact False.elim (hNot₂ h₂)
      | some c₂ =>
        cases h₃ : upperSingletonPairColor n H V tUpper p.1.2 p.2 with
        | none => exact False.elim (hNot₃ h₃)
        | some c₃ =>
          by_cases hDiff : c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃
          · exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_filter.mpr
                ⟨hp, c₁, c₂, c₃, hDiff.1, hDiff.2.1, hDiff.2.2,
                  h₁, h₂, h₃⟩))
          · have hRepeat : c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃ := by
              by_cases h12 : c₁ = c₂
              · exact Or.inl h12
              by_cases h13 : c₁ = c₃
              · exact Or.inr (Or.inl h13)
              right
              right
              by_contra h23
              exact hDiff ⟨h12, h13, h23⟩
            exact Finset.mem_union.mpr (Or.inl
              (Finset.mem_filter.mpr
                ⟨hp, c₁, c₂, c₃, hRepeat, h₁, h₂, h₃⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hBi | hRainbow
    · exact (Finset.mem_filter.mp hBi).1
    · exact (Finset.mem_filter.mp hRainbow).1

theorem upper_bicolored_triangle_facet_cell_le_three_codegree
    (H : Family α) (V : Edge α) (tUpper D₃ : ℕ)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    {p : (α × α) × α}
    (hp : p ∈ upperBicoloredTriples n H V tUpper) :
    (upperTriangleFacetCell n H V p).card ≤ D₃ := by
  classical
  obtain ⟨hTriangle, c₁, c₂, c₃, hRepeat, hc₁, hc₂, hc₃⟩ :=
    Finset.mem_filter.mp hp
  have hProd := (Finset.mem_filter.mp hTriangle).1
  have hVparts := Finset.mem_product.mp hProd
  have hXY := Finset.mem_product.mp hVparts.1
  have hx : p.1.1 ∈ V := hXY.1
  have hy : p.1.2 ∈ V := hXY.2
  have hz : p.2 ∈ V := hVparts.2
  have hDistinct := (Finset.mem_filter.mp hTriangle).2
  let cell := upperTriangleFacetCell n H V p
  have hLabels : ∀ A ∈ cell, c₁ ∈ A ∧ c₂ ∈ A ∧ c₃ ∈ A := by
    intro A hA
    have hAparts := Finset.mem_filter.mp hA
    have hAV := (Finset.mem_powersetCard.mp hAparts.1).1
    have hAcard := (Finset.mem_powersetCard.mp hAparts.1).2
    rcases hAparts.2 with ⟨hxA, hyA, hzA, hEx, hEy, hEz⟩
    constructor
    · exact upper_pair_color_label_mem_supporting_facet n H V A tUpper
        hx hy hDistinct.1 hAV hAcard hxA hyA hEx hEy hc₁
    constructor
    · exact upper_pair_color_label_mem_supporting_facet n H V A tUpper
        hx hz hDistinct.2.1 hAV hAcard hxA hzA hEx hEz hc₂
    · exact upper_pair_color_label_mem_supporting_facet n H V A tUpper
        hy hz hDistinct.2.2.1 hAV hAcard hyA hzA hEy hEz hc₃
  by_cases hEmpty : cell = ∅
  · change cell.card ≤ D₃
    simp [hEmpty]
  have hCellNon : cell.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hColors : ∃ c d : α, c ≠ d ∧
      (∀ A ∈ cell, c ∈ A ∧ d ∈ A) := by
    have hNotAll : c₁ ≠ c₂ ∨ c₂ ≠ c₃ := by
      have hNot := hDistinct.2.2.2.2.2.2
      simp [hc₁, hc₂, hc₃] at hNot
      exact hNot
    rcases hNotAll with h12 | h23
    · refine ⟨c₁, c₂, h12, ?_⟩
      intro A hA
      exact ⟨(hLabels A hA).1, (hLabels A hA).2.1⟩
    · refine ⟨c₂, c₃, h23, ?_⟩
      intro A hA
      exact ⟨(hLabels A hA).2.1, (hLabels A hA).2.2⟩
  obtain ⟨c, d, hcd, hBoth⟩ := hColors
  let S : Edge α := {p.1.1, c, d}
  have hXneq : p.1.1 ≠ c ∧ p.1.1 ≠ d := by
    obtain ⟨A, hA⟩ := hCellNon
    have hxA : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
    have hBothA := hBoth A hA
    exact ⟨fun h => hxA (h ▸ hBothA.1),
      fun h => hxA (h ▸ hBothA.2)⟩
  have hScard : S.card = 3 := by simp [S, hXneq.1, hXneq.2, hcd]
  have hInject : cell.card ≤ (H.filter fun E => S ⊆ E).card := by
    apply Finset.card_le_card_of_injOn (fun A => insert p.1.1 A)
    · intro A hA
      have hParts := (Finset.mem_filter.mp hA).2
      have hLab := hBoth A hA
      refine Finset.mem_filter.mpr ⟨hParts.2.2.2.1, ?_⟩
      intro v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | hv
      · exact Finset.mem_insert_self ..
      rcases hv with rfl | rfl
      · exact Finset.mem_insert_of_mem hLab.1
      · exact Finset.mem_insert_of_mem hLab.2
    · intro A hA B hB hEq
      have hxA : p.1.1 ∉ A := (Finset.mem_filter.mp hA).2.1
      have hxB : p.1.1 ∉ B := (Finset.mem_filter.mp hB).2.1
      have hErase := congrArg (Finset.erase · p.1.1) hEq
      simpa [hxA, hxB] using hErase
  change cell.card ≤ D₃
  exact hInject.trans (hD₃ S hScard)

noncomputable def upperBicoloredTriangleEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperBicoloredTriples n H V tUpper).biUnion fun p =>
    (upperTriangleFacetCell n H V p).biUnion fun A =>
      ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)

theorem upper_nonmonochromatic_triangle_edges_eq_bicolored_union_rainbow
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    upperNonmonochromaticTriangleEdges n H V tUpper =
      upperBicoloredTriangleEdges n H V tUpper ∪
        upperRainbowTriangleEdges n H V tUpper := by
  classical
  simp [upperNonmonochromaticTriangleEdges,
    upperBicoloredTriangleEdges, upperRainbowTriangleEdges,
    upper_nonmonochromatic_triples_eq_bicolored_union_rainbow n,
    Finset.union_biUnion]

theorem upper_singleton_color_repeated_partner_bound
    (H : Family α) (V : Edge α) (tUpper D₂ Dn : ℕ)
    (ht : 1 ≤ tUpper)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hDn : ∀ S : Edge α, S.card = n →
      (H.filter fun E => S ⊆ E).card ≤ Dn)
    {x y c : α} (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    (hColor : upperSingletonPairColor n H V tUpper x y = some c) :
    tUpper * ((V.filter fun z => z ≠ x ∧
      upperSingletonPairColor n H V tUpper x z = some c).card) ≤
        D₂ * Dn := by
  classical
  let Z := V.filter fun z => z ≠ x ∧
    upperSingletonPairColor n H V tUpper x z = some c
  have hStrongXY := (upper_singleton_pair_color_eq_some_iff_strong n
    H V tUpper hx hy hxy).mp hColor
  have hCellNon : (commonPrefixTails H V ({x} : Edge α)
      ({y} : Edge α) n).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < tUpper)
      hStrongXY.2.2.1)
  obtain ⟨A, hA⟩ := hCellNon
  have hcA : c ∈ A := hStrongXY.2.2.2.1 A hA
  have hxA : x ∉ A := by
    have hDisj := (mem_common_prefix_tails.mp hA).2.2.1
    intro hxA
    exact (Finset.disjoint_left.mp hDisj) hxA
      (Finset.mem_union_left _ (by simp))
  have hcNotX : c ∉ ({x} : Edge α) := by
    simpa using (fun h : c = x => hxA (h ▸ hcA))
  have hMap : ∀ z ∈ Z,
      ({z} : Edge α) ∈ actualCenterPartners H V ({x} : Edge α)
        1 n tUpper c ∅ := by
    intro z hz
    have hzParts := Finset.mem_filter.mp hz
    have hStrong := (upper_singleton_pair_color_eq_some_iff_strong n
      H V tUpper hx hzParts.1 hzParts.2.1.symm).mp hzParts.2.2
    exact Finset.mem_filter.mpr
      ⟨hStrong.1, hStrong, Finset.empty_subset _⟩
  have hZ : Z.card ≤
      (actualCenterPartners H V ({x} : Edge α)
        1 n tUpper c ∅).card := by
    apply Finset.card_le_card_of_injOn (fun z => ({z} : Edge α)) hMap
    intro z hz w hw hEq
    simpa using hEq
  have hPin := repeated_center_partner_bound_from_codegrees
    H V ({x} : Edge α) 1 n tUpper c ∅ 0 D₂ Dn
    (by simp) hcNotX (by simp) hD₂ hDn
  exact (Nat.mul_le_mul_left tUpper hZ).trans hPin

noncomputable def upperBicoloredFirstTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact (upperBicoloredTriples n H V tUpper).filter fun p =>
    upperSingletonPairColor n H V tUpper p.1.1 p.1.2 =
      upperSingletonPairColor n H V tUpper p.1.1 p.2

theorem upper_bicolored_first_triangle_weighted_budget
    (H : Family α) (V : Edge α) (tUpper D₂ D₃ Dn : ℕ)
    (ht : 1 ≤ tUpper)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hDn : ∀ S : Edge α, S.card = n →
      (H.filter fun E => S ⊆ E).card ≤ Dn) :
    tUpper * (∑ p ∈ upperBicoloredFirstTriples n H V tUpper,
      (upperTriangleFacetCell n H V p).card) ≤
      V.card ^ 2 * D₂ * D₃ * Dn := by
  classical
  let T := upperBicoloredFirstTriples n H V tUpper
  let pairs := V ×ˢ V
  let cell := upperTriangleFacetCell n H V
  change tUpper * (∑ p ∈ T, (cell p).card) ≤
    V.card ^ 2 * D₂ * D₃ * Dn
  have hMap : ∀ p ∈ T, p.1 ∈ pairs := by
    intro p hp
    have hBi := (Finset.mem_filter.mp hp).1
    have hTri := (Finset.mem_filter.mp hBi).1
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hTri).1).1
  have hOne : ∀ xy ∈ pairs,
      tUpper * (∑ p ∈ T.filter fun p => p.1 = xy, (cell p).card) ≤
        D₂ * D₃ * Dn := by
    intro xy hxy
    let F := T.filter fun p => p.1 = xy
    by_cases hEmpty : F = ∅
    · simp [F, hEmpty]
    obtain ⟨p₀, hp₀⟩ : F.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    have hp₀T : p₀ ∈ T := (Finset.mem_filter.mp hp₀).1
    have hp₀eq : p₀.1 = xy := (Finset.mem_filter.mp hp₀).2
    have hTri₀ := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hp₀T).1).1
    have hColorNot : upperSingletonPairColor n H V tUpper
      xy.1 xy.2 ≠ none := by
      simpa [← hp₀eq] using
        (Finset.mem_filter.mp hTri₀).2.2.2.2.1
    obtain ⟨c, hc⟩ : ∃ c : α,
        upperSingletonPairColor n H V tUpper xy.1 xy.2 = some c := by
      cases h : upperSingletonPairColor n H V tUpper xy.1 xy.2 with
      | none => exact False.elim (hColorNot h)
      | some c => exact ⟨c, rfl⟩
    have hxyV := Finset.mem_product.mp hxy
    have hxyNe : xy.1 ≠ xy.2 := by
      simpa [← hp₀eq] using
        (Finset.mem_filter.mp hTri₀).2.1
    let Z := V.filter fun z => z ≠ xy.1 ∧
      upperSingletonPairColor n H V tUpper xy.1 z = some c
    have hFsub : F.card ≤ Z.card := by
      apply Finset.card_le_card_of_injOn (fun p => p.2)
      · intro p hp
        have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hpEq : p.1 = xy := (Finset.mem_filter.mp hp).2
        have hpBi := (Finset.mem_filter.mp hpT).1
        have hpTri := (Finset.mem_filter.mp hpBi).1
        have hpV := (Finset.mem_product.mp
          (Finset.mem_filter.mp hpTri).1).2
        have hpNe := (Finset.mem_filter.mp hpTri).2.2.1
        have hpColor := (Finset.mem_filter.mp hpT).2
        apply Finset.mem_filter.mpr
        refine ⟨hpV, ?_, ?_⟩
        · simpa [← hpEq] using hpNe.symm
        · have hEqColor : upperSingletonPairColor n H V tUpper
              xy.1 xy.2 = upperSingletonPairColor n H V tUpper xy.1 p.2 := by
            simpa [hpEq] using hpColor
          exact hc ▸ hEqColor.symm
      · intro p hp q hq hEq
        have hpEq : p.1 = xy := (Finset.mem_filter.mp hp).2
        have hqEq : q.1 = xy := (Finset.mem_filter.mp hq).2
        exact Prod.ext (hpEq.trans hqEq.symm) hEq
    have hPinned := upper_singleton_color_repeated_partner_bound n
      H V tUpper D₂ Dn ht hD₂ hDn
      hxyV.1 hxyV.2 hxyNe hc
    have hFweighted : tUpper * F.card ≤ D₂ * Dn :=
      (Nat.mul_le_mul_left tUpper hFsub).trans hPinned
    have hCellSum : (∑ p ∈ F, (cell p).card) ≤ F.card * D₃ := by
      calc
        _ ≤ ∑ _p ∈ F, D₃ := by
          apply Finset.sum_le_sum
          intro p hp
          exact upper_bicolored_triangle_facet_cell_le_three_codegree n
            H V tUpper D₃ hD₃ (Finset.mem_filter.mp
              (Finset.mem_filter.mp hp).1).1
        _ = F.card * D₃ := by simp
    calc
      tUpper * (∑ p ∈ F, (cell p).card) ≤
          tUpper * (F.card * D₃) := Nat.mul_le_mul_left _ hCellSum
      _ = (tUpper * F.card) * D₃ := by ring
      _ ≤ (D₂ * Dn) * D₃ := Nat.mul_le_mul_right D₃ hFweighted
      _ = D₂ * D₃ * Dn := by ring
  have hReindex := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := pairs) hMap (fun p => (cell p).card)
  calc
    tUpper * (∑ p ∈ T, (cell p).card) =
        ∑ xy ∈ pairs,
          tUpper * (∑ p ∈ T.filter fun p => p.1 = xy, (cell p).card) := by
      rw [← hReindex, Finset.mul_sum]
    _ ≤ ∑ _xy ∈ pairs, D₂ * D₃ * Dn := Finset.sum_le_sum hOne
    _ = pairs.card * (D₂ * D₃ * Dn) := by simp
    _ = V.card ^ 2 * D₂ * D₃ * Dn := by
      simp [pairs, Finset.card_product, pow_two]
      ring

end JSP523.Rank5.HigherRankUpper
