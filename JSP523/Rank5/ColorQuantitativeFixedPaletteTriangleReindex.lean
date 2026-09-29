import JSP523.Rank5.ColorQuantitativeFixedPaletteTriangles
import JSP523.Rank5.BicoloredOrientation

/-! # Actual lower bicolored supports charged to pinned orientations -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

theorem fixed_palette_core_bicolored_supports_le_orientations
    (H : Family α) (V B : Edge α) (s k t : ℕ) (hB : B ∈ V.powersetCard k) :
    (bicoloredTriangleSupports (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)).card ≤
      ((fixedPaletteBicoloredFirstTriples H V s k t).filter fun p => B ∈ fixedPaletteTriangleCoreCell H V s k p).card := by
  classical
  let O := (fixedPaletteBicoloredFirstTriples H V s k t).filter fun p => B ∈ fixedPaletteTriangleCoreCell H V s k p
  have hCover : bicoloredTriangleSupports (actualCoreLink H V B s)
      (fixedPaletteCoreSupportColor H V B s k t) ⊆
      O.image (fun p => ({p.1.1,p.1.2,p.2} : Finset (Edge α))) := by
    intro e he
    have hParts := Finset.mem_filter.mp he
    have hE := Finset.mem_powersetCard.mp hParts.1
    obtain ⟨P,Q,R,z,w,hTriple,hPQ,hPR,hQR,hzw,hPQc,hPRc,hQRc⟩ :=
      bicolored_support_has_repeated_orientation (fixedPaletteCoreSupportColor H V B s k t) hE.2 hParts.2
    have hP : P ∈ actualCoreLink H V B s := hE.1 (by rw [hTriple]; simp)
    have hQ : Q ∈ actualCoreLink H V B s := hE.1 (by rw [hTriple]; simp)
    have hR : R ∈ actualCoreLink H V B s := hE.1 (by rw [hTriple]; simp)
    have hRoot : ∀ A ∈ actualCoreLink H V B s, A ∈ V.powersetCard s := by
      intro A hA
      have h := mem_actual_core_link.mp hA
      exact Finset.mem_powersetCard.mpr ⟨h.1,h.2.1⟩
    have hStrong : ∀ A C : Edge α, ∀ z : {z // z ∈ B}, A ≠ C →
        fixedPaletteCoreSupportColor H V B s k t {A,C} = some z →
          ActualStrongPartner H V A C s k t z.1 := by
      intro A C z hAC hc
      have hLabel := (fixed_palette_core_support_color_eq_some_iff H V B s k t (Finset.card_pair hAC)).1 hc
      exact hLabel A (by simp) C (by simp) hAC
    have hzW : z.1 ≠ w.1 := fun h => hzw (Subtype.ext h)
    have hO : ((P,Q),R) ∈ O := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hRoot P hP,hRoot Q hQ⟩,hRoot R hR⟩,
          z.1,w.1,hzW,hStrong P Q z hPQ hPQc,hStrong P R z hPR hPRc,
          hStrong Q R w hQR hQRc⟩
      · exact Finset.mem_filter.mpr ⟨hB,hP,hQ,hR⟩
    exact Finset.mem_image.mpr ⟨((P,Q),R),hO,hTriple.symm⟩
  exact (Finset.card_le_card hCover).trans Finset.card_image_le

/-- Summing over actual triple cores counts each possible orientation by
    its actual common supporting cell. -/
theorem fixed_palette_bicolored_support_sum_le_cells
    (H : Family α) (V : Edge α) (s k t : ℕ) :
    (∑ B ∈ V.powersetCard k,
      (bicoloredTriangleSupports (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)).card) ≤
      ∑ p ∈ fixedPaletteBicoloredFirstTriples H V s k t, (fixedPaletteTriangleCoreCell H V s k p).card := by
  classical
  have hLocal := Finset.sum_le_sum (fun B (hB : B ∈ V.powersetCard k) =>
    fixed_palette_core_bicolored_supports_le_orientations H V B s k t hB)
  have hSwap : (∑ B ∈ V.powersetCard k,
      ((fixedPaletteBicoloredFirstTriples H V s k t).filter fun p => B ∈ fixedPaletteTriangleCoreCell H V s k p).card) =
      ∑ p ∈ fixedPaletteBicoloredFirstTriples H V s k t,
        ((V.powersetCard k).filter fun B => B ∈ fixedPaletteTriangleCoreCell H V s k p).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hSwap] at hLocal
  have hFilter : ∀ p,
      (V.powersetCard k).filter (fun B => B ∈ fixedPaletteTriangleCoreCell H V s k p) =
        fixedPaletteTriangleCoreCell H V s k p := by
    intro p
    ext B
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hB => ⟨(Finset.mem_filter.mp hB).1,hB⟩⟩
  simpa only [hFilter] using hLocal

/-- Complete actual IV.7.4 at fixed rank, with all orientations included. -/
theorem fixed_palette_bicolored_support_sum_budget
    (H : Family α) (V : Edge α) (s k t D₃ D₄ Dk : ℕ) (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = s + 1 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hDk : ∀ S : Edge α, S.card = k → (H.filter fun E => S ⊆ E).card ≤ Dk)
    (hD₄ : ∀ S : Edge α, S.card = s + 2 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    t * (∑ B ∈ V.powersetCard k,
      (bicoloredTriangleSupports (actualCoreLink H V B s) (fixedPaletteCoreSupportColor H V B s k t)).card) ≤
      (V.powersetCard s).card ^ 2 * D₃ * Dk * D₄ := by
  exact (Nat.mul_le_mul_left t (fixed_palette_bicolored_support_sum_le_cells H V s k t)).trans
    (fixed_palette_bicolored_first_triangle_weighted_budget H V s k t D₃ D₄ Dk ht hD₃ hDk hD₄)

end JSP523.Rank5
