import JSP523.Rank5.LowerBicoloredBudget
import JSP523.Rank5.BicoloredOrientation

/-! # Actual lower bicolored supports charged to pinned orientations -/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

theorem lower_core_bicolored_supports_le_orientations
    (H : Family α) (V B : Edge α) (t : ℕ) (hB : B ∈ V.powersetCard 3) :
    (bicoloredTriangleSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card ≤
      ((lowerBicoloredFirstTriples H V t).filter fun p => B ∈ lowerTriangleCoreCell H V p).card := by
  classical
  let O := (lowerBicoloredFirstTriples H V t).filter fun p => B ∈ lowerTriangleCoreCell H V p
  have hCover : bicoloredTriangleSupports (actualCoreLink H V B 2)
      (lowerCoreSupportColor H V B t) ⊆
      O.image (fun p => ({p.1.1,p.1.2,p.2} : Finset (Edge α))) := by
    intro e he
    have hParts := Finset.mem_filter.mp he
    have hE := Finset.mem_powersetCard.mp hParts.1
    obtain ⟨P,Q,R,z,w,hTriple,hPQ,hPR,hQR,hzw,hPQc,hPRc,hQRc⟩ :=
      bicolored_support_has_repeated_orientation (lowerCoreSupportColor H V B t) hE.2 hParts.2
    have hP : P ∈ actualCoreLink H V B 2 := hE.1 (by rw [hTriple]; simp)
    have hQ : Q ∈ actualCoreLink H V B 2 := hE.1 (by rw [hTriple]; simp)
    have hR : R ∈ actualCoreLink H V B 2 := hE.1 (by rw [hTriple]; simp)
    have hRoot : ∀ A ∈ actualCoreLink H V B 2, A ∈ V.powersetCard 2 := by
      intro A hA
      have h := mem_actual_core_link.mp hA
      exact Finset.mem_powersetCard.mpr ⟨h.1,h.2.1⟩
    have hStrong : ∀ A C : Edge α, ∀ z : {z // z ∈ B}, A ≠ C →
        lowerCoreSupportColor H V B t {A,C} = some z →
          ActualStrongPartner H V A C 2 3 t z.1 := by
      intro A C z hAC hc
      have hLabel := (lower_core_support_color_eq_some_iff H V B t (Finset.card_pair hAC)).1 hc
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
theorem lower_bicolored_support_sum_le_cells
    (H : Family α) (V : Edge α) (t : ℕ) :
    (∑ B ∈ V.powersetCard 3,
      (bicoloredTriangleSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card) ≤
      ∑ p ∈ lowerBicoloredFirstTriples H V t, (lowerTriangleCoreCell H V p).card := by
  classical
  have hLocal := Finset.sum_le_sum (fun B (hB : B ∈ V.powersetCard 3) =>
    lower_core_bicolored_supports_le_orientations H V B t hB)
  have hSwap : (∑ B ∈ V.powersetCard 3,
      ((lowerBicoloredFirstTriples H V t).filter fun p => B ∈ lowerTriangleCoreCell H V p).card) =
      ∑ p ∈ lowerBicoloredFirstTriples H V t,
        ((V.powersetCard 3).filter fun B => B ∈ lowerTriangleCoreCell H V p).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hSwap] at hLocal
  have hFilter : ∀ p,
      (V.powersetCard 3).filter (fun B => B ∈ lowerTriangleCoreCell H V p) =
        lowerTriangleCoreCell H V p := by
    intro p
    ext B
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hB => ⟨(Finset.mem_filter.mp hB).1,hB⟩⟩
  simpa only [hFilter] using hLocal

/-- Complete actual IV.7.4 at rank five, with all orientations included. -/
theorem lower_bicolored_support_sum_budget
    (H : Family α) (V : Edge α) (t D₃ D₄ : ℕ) (ht : 1 ≤ t)
    (hD₃ : ∀ S : Edge α, S.card = 3 → (H.filter fun E => S ⊆ E).card ≤ D₃)
    (hD₄ : ∀ S : Edge α, S.card = 4 → (H.filter fun E => S ⊆ E).card ≤ D₄) :
    t * (∑ B ∈ V.powersetCard 3,
      (bicoloredTriangleSupports (actualCoreLink H V B 2) (lowerCoreSupportColor H V B t)).card) ≤
      (V.powersetCard 2).card ^ 2 * D₃ * D₃ * D₄ := by
  exact (Nat.mul_le_mul_left t (lower_bicolored_support_sum_le_cells H V t)).trans
    (lower_bicolored_first_triangle_weighted_budget H V t D₃ D₄ ht hD₃ hD₄)

end JSP523.Rank5
