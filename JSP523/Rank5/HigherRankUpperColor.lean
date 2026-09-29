import JSP523.Rank5.InheritanceLowRetention

/-! # Actual upper-facet colors at arbitrary facet rank

The IV.8 pair and triangle cleanup construction uses no rank-five
assumption. Here `n` is the facet size; the parent uniformity is `n+1`.
-/
namespace JSP523.Rank5.HigherRankUpper
variable {α : Type*} [DecidableEq α] (n : ℕ)

noncomputable def upperSingletonPairColor
    (H : Family α) (V : Edge α) (tUpper : ℕ) (x y : α) : Option α := by
  classical
  if h : ∃ z : α,
      tUpper ≤ (commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) n).card ∧
        UniqueCellCenter (commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) n) z then
    exact some (Classical.choose h)
  else
    exact none

theorem upper_singleton_pair_color_eq_some_iff_strong
    (H : Family α) (V : Edge α) (tUpper : ℕ)
    {x y z : α} (_hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y) :
    upperSingletonPairColor n H V tUpper x y = some z ↔
      ActualStrongPartner H V ({x} : Edge α) ({y} : Edge α)
        1 n tUpper z := by
  classical
  let cell := commonPrefixTails H V ({x} : Edge α) ({y} : Edge α) n
  have hGeom : ({y} : Edge α) ∈ V.powersetCard 1 ∧
      Disjoint ({x} : Edge α) ({y} : Edge α) := by
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨by simpa using hy, by simp⟩
    · simpa [Finset.disjoint_singleton] using hxy
  constructor
  · intro hColor
    by_cases h : ∃ z' : α, tUpper ≤ cell.card ∧ UniqueCellCenter cell z'
    · have hColor' : some (Classical.choose h) = some z := by
        simpa [upperSingletonPairColor, h, cell] using hColor
      have hSpec := Classical.choose_spec h
      have hz : Classical.choose h = z := Option.some.inj hColor'
      exact ⟨hGeom.1, hGeom.2, hSpec.1, hz ▸ hSpec.2⟩
    · simp [upperSingletonPairColor, h, cell] at hColor
  · intro hStrong
    have h : ∃ z' : α, tUpper ≤ cell.card ∧ UniqueCellCenter cell z' :=
      ⟨z, hStrong.2.2.1, hStrong.2.2.2⟩
    have hSpec := (Classical.choose_spec h).2
    have hEq : Classical.choose h = z :=
      (hSpec.2 z hStrong.2.2.2.1).symm
    simp [upperSingletonPairColor, h, cell, hEq]

theorem upper_singleton_pair_color_symm
    (H : Family α) (V : Edge α) (tUpper : ℕ) (x y : α) :
    upperSingletonPairColor n H V tUpper x y =
      upperSingletonPairColor n H V tUpper y x := by
  classical
  simp only [upperSingletonPairColor]
  rw [common_prefix_tails_comm H V ({y} : Edge α) ({x} : Edge α) n]

noncomputable def upperUncoloredPairs
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Finset (α × α) := by
  classical
  exact (V ×ˢ V).filter fun p =>
    p.1 ≠ p.2 ∧ upperSingletonPairColor n H V tUpper p.1 p.2 = none

noncomputable def upperUncoloredFacetEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperUncoloredPairs n H V tUpper).biUnion fun p =>
    (commonPrefixTails H V ({p.1} : Edge α) ({p.2} : Edge α) n).biUnion
      fun A => ({insert p.1 A, insert p.2 A} : Family α)

theorem upper_uncolored_facet_edges_card_le_cells
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    (upperUncoloredFacetEdges n H V tUpper).card ≤
      2 * ∑ p ∈ upperUncoloredPairs n H V tUpper,
        (commonPrefixTails H V ({p.1} : Edge α)
          ({p.2} : Edge α) n).card := by
  classical
  let U := upperUncoloredPairs n H V tUpper
  let cell := fun p : α × α =>
    commonPrefixTails H V ({p.1} : Edge α) ({p.2} : Edge α) n
  have hFiber : ∀ p ∈ U,
      ((cell p).biUnion fun A => ({insert p.1 A, insert p.2 A} : Family α)).card ≤
        2 * (cell p).card := by
    intro p hp
    calc
      _ ≤ ∑ A ∈ cell p,
          ({insert p.1 A, insert p.2 A} : Family α).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ cell p, 2 := by
        apply Finset.sum_le_sum
        intro A hA
        exact Finset.card_le_two
      _ = 2 * (cell p).card := by simp [mul_comm]
  calc
    (upperUncoloredFacetEdges n H V tUpper).card ≤
        ∑ p ∈ U,
          ((cell p).biUnion fun A =>
            ({insert p.1 A, insert p.2 A} : Family α)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ U, 2 * (cell p).card := Finset.sum_le_sum hFiber
    _ = 2 * ∑ p ∈ U, (cell p).card := by rw [Finset.mul_sum]

noncomputable def upperNonmonochromaticTriples
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    Finset ((α × α) × α) := by
  classical
  exact ((V ×ˢ V) ×ˢ V).filter fun p =>
    p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2 ∧
      (upperSingletonPairColor n H V tUpper p.1.1 p.1.2 ≠ none) ∧
      (upperSingletonPairColor n H V tUpper p.1.1 p.2 ≠ none) ∧
      (upperSingletonPairColor n H V tUpper p.1.2 p.2 ≠ none) ∧
      (upperSingletonPairColor n H V tUpper p.1.1 p.1.2 ≠
        upperSingletonPairColor n H V tUpper p.1.1 p.2 ∨
       upperSingletonPairColor n H V tUpper p.1.1 p.2 ≠
        upperSingletonPairColor n H V tUpper p.1.2 p.2)

noncomputable def upperTriangleFacetCell
    (H : Family α) (V : Edge α) (p : (α × α) × α) : Family α := by
  classical
  exact (V.powersetCard n).filter fun A =>
    p.1.1 ∉ A ∧ p.1.2 ∉ A ∧ p.2 ∉ A ∧
      insert p.1.1 A ∈ H ∧ insert p.1.2 A ∈ H ∧ insert p.2 A ∈ H

noncomputable def upperNonmonochromaticTriangleEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact (upperNonmonochromaticTriples n H V tUpper).biUnion fun p =>
    (upperTriangleFacetCell n H V p).biUnion fun A =>
      ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)

theorem upper_nonmonochromatic_triangle_edges_card_le_cells
    (H : Family α) (V : Edge α) (tUpper : ℕ) :
    (upperNonmonochromaticTriangleEdges n H V tUpper).card ≤
      3 * ∑ p ∈ upperNonmonochromaticTriples n H V tUpper,
        (upperTriangleFacetCell n H V p).card := by
  classical
  let T := upperNonmonochromaticTriples n H V tUpper
  let cell := upperTriangleFacetCell n H V
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
  calc
    (upperNonmonochromaticTriangleEdges n H V tUpper).card ≤
        ∑ p ∈ T,
          ((cell p).biUnion fun A =>
            ({insert p.1.1 A, insert p.1.2 A, insert p.2 A} : Family α)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p ∈ T, 3 * (cell p).card := Finset.sum_le_sum hFiber
    _ = 3 * ∑ p ∈ T, (cell p).card := by rw [Finset.mul_sum]

theorem upper_pair_color_label_mem_supporting_facet
    (H : Family α) (V A : Edge α) (tUpper : ℕ)
    {x y c : α} (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y)
    (hAV : A ⊆ V) (hAcard : A.card = n)
    (hxA : x ∉ A) (hyA : y ∉ A)
    (hEx : insert x A ∈ H) (hEy : insert y A ∈ H)
    (hColor : upperSingletonPairColor n H V tUpper x y = some c) :
    c ∈ A := by
  have hStrong := (upper_singleton_pair_color_eq_some_iff_strong n
    H V tUpper hx hy hxy).mp hColor
  have hCell : A ∈ commonPrefixTails H V
      ({x} : Edge α) ({y} : Edge α) n := by
    apply mem_common_prefix_tails.mpr
    refine ⟨hAV, hAcard, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hvA hv
      simp only [Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxA hvA
      · exact hyA hvA
    · simpa using hEx
    · simpa using hEy
  exact hStrong.2.2.2.1 A hCell

noncomputable def upperFacetColorCleanupEdges
    (H : Family α) (V : Edge α) (tUpper : ℕ) : Family α := by
  classical
  exact upperUncoloredFacetEdges n H V tUpper ∪
    upperNonmonochromaticTriangleEdges n H V tUpper

theorem upper_facet_pair_colored_of_uncolored_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K (upperUncoloredFacetEdges n H V tUpper))
    (hAV : A ⊆ V) (hAcard : A.card = n)
    {x y : α} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : x ≠ y) (hxA : x ∉ A) (hyA : y ∉ A)
    (hEx : insert x A ∈ K) (hEy : insert y A ∈ K) :
    upperSingletonPairColor n H V tUpper x y ≠ none := by
  classical
  intro hNone
  have hPair : (x, y) ∈ upperUncoloredPairs n H V tUpper :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy, hNone⟩
  have hCell : A ∈ commonPrefixTails H V
      ({x} : Edge α) ({y} : Edge α) n := by
    apply mem_common_prefix_tails.mpr
    refine ⟨hAV, hAcard, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hvA hv
      simp only [Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxA hvA
      · exact hyA hvA
    · simpa using hKH hEx
    · simpa using hKH hEy
  have hDeleted : insert x A ∈ upperUncoloredFacetEdges n H V tUpper := by
    unfold upperUncoloredFacetEdges
    exact Finset.mem_biUnion.mpr
      ⟨(x, y), hPair, Finset.mem_biUnion.mpr
        ⟨A, hCell, by simp⟩⟩
  exact (Finset.disjoint_left.mp hSurvive) hEx hDeleted

theorem upper_facet_triangle_monochromatic_of_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges n H V tUpper))
    (hAV : A ⊆ V) (hAcard : A.card = n)
    {x y z : α} (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxA : x ∉ A) (hyA : y ∉ A) (hzA : z ∉ A)
    (hEx : insert x A ∈ K) (hEy : insert y A ∈ K)
    (hEz : insert z A ∈ K) :
    upperSingletonPairColor n H V tUpper x y =
        upperSingletonPairColor n H V tUpper x z ∧
      upperSingletonPairColor n H V tUpper x z =
        upperSingletonPairColor n H V tUpper y z := by
  classical
  have hNoU : Disjoint K (upperUncoloredFacetEdges n H V tUpper) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hSurvive
  have hCxy := upper_facet_pair_colored_of_uncolored_cleanup n
    K H V A tUpper hKH hNoU hAV hAcard
    hx hy hxy hxA hyA hEx hEy
  have hCxz := upper_facet_pair_colored_of_uncolored_cleanup n
    K H V A tUpper hKH hNoU hAV hAcard
    hx hz hxz hxA hzA hEx hEz
  have hCyz := upper_facet_pair_colored_of_uncolored_cleanup n
    K H V A tUpper hKH hNoU hAV hAcard
    hy hz hyz hyA hzA hEy hEz
  by_contra hNonmono
  have hTriangle : ((x, y), z) ∈
      upperNonmonochromaticTriples n H V tUpper := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩,
        hxy, hxz, hyz, hCxy, hCxz, hCyz, ?_⟩
    exact not_and_or.mp hNonmono
  have hCell : A ∈ upperTriangleFacetCell n H V ((x, y), z) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hAV, hAcard⟩,
        hxA, hyA, hzA, hKH hEx, hKH hEy, hKH hEz⟩
  have hDeleted : insert x A ∈
      upperNonmonochromaticTriangleEdges n H V tUpper := by
    unfold upperNonmonochromaticTriangleEdges
    exact Finset.mem_biUnion.mpr
      ⟨((x, y), z), hTriangle, Finset.mem_biUnion.mpr
        ⟨A, hCell, by simp⟩⟩
  exact (Finset.disjoint_left.mp hSurvive) hEx
    (Finset.mem_union_right _ hDeleted)

theorem upper_facet_color_center_exists_of_cleanup
    (K H : Family α) (V A : Edge α) (tUpper : ℕ)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (upperFacetColorCleanupEdges n H V tUpper))
    (hAV : A ⊆ V) (hAcard : A.card = n)
    (hShared : 2 ≤ (V.filter fun x => x ∉ A ∧ insert x A ∈ K).card) :
    ∃ c ∈ A,
      ∀ x ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
        ∀ y ∈ V.filter (fun x => x ∉ A ∧ insert x A ∈ K),
          x ≠ y → upperSingletonPairColor n H V tUpper x y = some c := by
  classical
  let S := V.filter fun x => x ∉ A ∧ insert x A ∈ K
  have hS : 1 < S.card := by
    change 2 ≤ S.card at hShared
    omega
  obtain ⟨x, hx⟩ : S.Nonempty :=
    Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne hS x
  have hxy : x ≠ y := Ne.symm hyx
  have hParts : ∀ w ∈ S, w ∈ V ∧ w ∉ A ∧ insert w A ∈ K := by
    intro w hw
    exact Finset.mem_filter.mp hw
  have hNoU : Disjoint K (upperUncoloredFacetEdges n H V tUpper) :=
    Finset.disjoint_of_subset_right Finset.subset_union_left hSurvive
  have hColorXY := upper_facet_pair_colored_of_uncolored_cleanup n
    K H V A tUpper hKH hNoU hAV hAcard
    (hParts x hx).1 (hParts y hy).1 hxy
    (hParts x hx).2.1 (hParts y hy).2.1
    (hParts x hx).2.2 (hParts y hy).2.2
  obtain ⟨c, hc⟩ : ∃ c : α,
      upperSingletonPairColor n H V tUpper x y = some c := by
    cases h : upperSingletonPairColor n H V tUpper x y with
    | none => exact False.elim (hColorXY h)
    | some c => exact ⟨c, rfl⟩
  have hcA := upper_pair_color_label_mem_supporting_facet n
    H V A tUpper (hParts x hx).1 (hParts y hy).1 hxy
    hAV hAcard (hParts x hx).2.1 (hParts y hy).2.1
    (hKH (hParts x hx).2.2) (hKH (hParts y hy).2.2) hc
  have hFromX : ∀ z ∈ S, z ≠ x →
      upperSingletonPairColor n H V tUpper x z = some c := by
    intro z hz hzx
    by_cases hzy : z = y
    · simpa [hzy] using hc
    have hTri := upper_facet_triangle_monochromatic_of_cleanup n
      K H V A tUpper hKH hSurvive hAV hAcard
      (hParts x hx).1 (hParts y hy).1 (hParts z hz).1
      hxy (Ne.symm hzx) (Ne.symm hzy)
      (hParts x hx).2.1 (hParts y hy).2.1 (hParts z hz).2.1
      (hParts x hx).2.2 (hParts y hy).2.2 (hParts z hz).2.2
    exact hTri.1.symm.trans hc
  refine ⟨c, hcA, ?_⟩
  intro u hu v hv huv
  by_cases hux : u = x
  · subst u
    exact hFromX v hv (Ne.symm huv)
  by_cases hvx : v = x
  · subst v
    rw [upper_singleton_pair_color_symm n]
    exact hFromX u hu hux
  have hTri := upper_facet_triangle_monochromatic_of_cleanup n
    K H V A tUpper hKH hSurvive hAV hAcard
    (hParts x hx).1 (hParts u hu).1 (hParts v hv).1
    (Ne.symm hux) (Ne.symm hvx) huv
    (hParts x hx).2.1 (hParts u hu).2.1 (hParts v hv).2.1
    (hParts x hx).2.2 (hParts u hu).2.2 (hParts v hv).2.2
  exact hTri.2.symm.trans (hFromX v hv hvx)

end JSP523.Rank5.HigherRankUpper
