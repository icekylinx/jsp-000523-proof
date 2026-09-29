import JSP523.Rank5.ColorMajorityPairs

/-! # Monochromatic clean samples of a partial coloring

The deterministic implication in IV.6.2 is applied to the actual partial
edge coloring: a large sample containing neither an uncolored edge nor a
bicolored triangle has one color on every edge.
-/

namespace JSP523.Rank5

variable {α κ : Type*} [DecidableEq α] [DecidableEq κ]

theorem triangle_pair_supports
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x,y,z} : Finset α).powersetCard 2 = {{x,y}, {x,z}, {y,z}} := by
  rw [Finset.powersetCard_succ_insert (by simp [hxy,hxz])]
  have h2 : ({z} : Finset α).powersetCard 2 = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simp)
  simp [Finset.powersetCard_succ_insert, hyz, h2, Finset.powersetCard_one]
  ext e
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem bicolored_support_of_pair_colors
    (edgeColor : Finset α → Option κ)
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {c d : κ} (hcd : c ≠ d)
    (hxyC : edgeColor {x,y} = some c)
    (hxzC : edgeColor {x,z} = some c)
    (hyzD : edgeColor {y,z} = some d) :
    IsBicoloredTriangleSupport edgeColor {x,y,z} := by
  have hEdges : triangleEdgeSupports ({x,y,z} : Finset α) =
      {{x,y}, {x,z}, {y,z}} := triangle_pair_supports hxy hxz hyz
  refine ⟨c, d, hcd, ⟨{x,y}, ?_, hxyC⟩, ⟨{y,z}, ?_, hyzD⟩, ?_⟩
  · rw [hEdges]; simp
  · rw [hEdges]; simp
  · intro e he
    rw [hEdges] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Or.inl hxyC
    · exact Or.inl hxzC
    · exact Or.inr hyzD

/-- A large sample avoiding both sorts of obstruction has one color on
    all of its actual two-element edge supports. -/
theorem clean_partial_coloring_sample_monochromatic
    [Fintype κ] [Nonempty κ]
    (S : Finset α) (edgeColor : Finset α → Option κ)
    (hq : 2 ≤ Fintype.card κ)
    (hSize : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ S.card)
    (hTotal : ∀ e ∈ S.powersetCard 2, edgeColor e ≠ none)
    (hNoBi : ∀ T ∈ S.powersetCard 3, ¬ IsBicoloredTriangleSupport edgeColor T) :
    ∃ c : κ, ∀ e ∈ S.powersetCard 2, edgeColor e = some c := by
  classical
  let U := {x // x ∈ S}
  let defaultColor : κ := Classical.choice inferInstance
  let color : U → U → κ := fun x y => (edgeColor {x.1,y.1}).getD defaultColor
  have hSome : ∀ x y : U, x ≠ y → edgeColor {x.1,y.1} = some (color x y) := by
    intro x y hxy
    have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hEdge : ({x.1,y.1} : Finset α) ∈ S.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro x.2 y.2, Finset.card_pair hxyVal⟩
    have hNe := hTotal _ hEdge
    cases h : edgeColor {x.1,y.1} with
    | none => exact False.elim (hNe h)
    | some c => simp [color, h]
  have hRigid : NoBicoloredTriangle color := by
    constructor
    · intro x y _
      simp only [color, Finset.pair_comm]
    · intro x y z hxy hxz hyz hEq
      by_contra hDiff
      have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hxzVal : x.1 ≠ z.1 := fun h => hxz (Subtype.ext h)
      have hyzVal : y.1 ≠ z.1 := fun h => hyz (Subtype.ext h)
      have hTriple : ({x.1,y.1,z.1} : Finset α) ∈ S.powersetCard 3 := by
        apply Finset.mem_powersetCard.mpr
        exact ⟨by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro x.2 (And.intro y.2 z.2), by simp [hxyVal,hxzVal,hyzVal]⟩
      apply hNoBi _ hTriple
      exact bicolored_support_of_pair_colors edgeColor hxyVal hxzVal hyzVal
        (Ne.symm hDiff) (hSome x y hxy) (hEq.symm ▸ hSome x z hxz) (hSome y z hyz)
  have hSizeU : max 4 ((Fintype.card κ - 1) ^ 2 + 1) ≤ Fintype.card U := by
    simpa [U] using hSize
  obtain ⟨c, hMono⟩ | hSmall := color_rigidity_finite color hRigid hq
  · refine ⟨c, ?_⟩
    intro e he
    have hParts := Finset.mem_powersetCard.mp he
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hParts.2
    have hx : x ∈ S := hParts.1 (by simp)
    have hy : y ∈ S := hParts.1 (by simp)
    have hxyU : (⟨x,hx⟩ : U) ≠ ⟨y,hy⟩ := fun h => hxy (congrArg Subtype.val h)
    exact (hSome ⟨x,hx⟩ ⟨y,hy⟩ hxyU).trans (congrArg some (hMono _ _ hxyU))
  · omega

end JSP523.Rank5
