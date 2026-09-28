import JSP523.Rank5.ShadowPower

/-!
# Exact rank-two shadow-power case

Every vertex of a two-uniform edge gives a singleton in the immediate
shadow. Mapping each edge to its two singleton facets embeds the family
into the pairs of shadow members.
-/

namespace JSP523.Rank5

open scoped FinsetFamily

variable {α : Type*} [DecidableEq α]

/-- In rank two, the manuscript's shadow-power inequality holds with the
actual immediate shadow and no ambient-size or threshold assumption. -/
theorem rank_two_shadow_power_exact
    (A : Family α) (hUniform : Uniform 2 A) :
    2 * A.card ≤ (Finset.shadow A).card ^ 2 := by
  classical
  let singletonImage : Edge α → Edge (Edge α) :=
    fun E => E.image fun x => ({x} : Edge α)
  have hSingletonInjective : Function.Injective (fun x : α => ({x} : Edge α)) := by
    intro x y h
    exact Finset.singleton_injective h
  have hFacet : ∀ E ∈ A, ∀ x ∈ E, ({x} : Edge α) ∈ Finset.shadow A := by
    intro E hE x hx
    have hEraseCard : (E.erase x).card = 1 := by
      have h := Finset.card_erase_add_one hx
      rw [hUniform hE] at h
      omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hEraseCard
    have hyE : y ∈ E := by
      rw [← Finset.insert_erase hx, hy]
      simp
    have hyNe : y ≠ x := by
      intro hEq
      subst y
      have hxNot : x ∉ E.erase x := by simp
      rw [hy] at hxNot
      simp at hxNot
    have hRep : E = insert x {y} := by
      rw [← Finset.insert_erase hx, hy]
    have hEdgeEq : insert y ({x} : Edge α) = E := by
      rw [hRep]
      ext z
      simp [or_comm]
    have hEdge : insert y ({x} : Edge α) ∈ A := hEdgeEq ▸ hE
    exact Finset.mem_shadow_iff_insert_mem.mpr
      ⟨y, by simp [hyNe], hEdge⟩
  have hImageSub : ∀ E ∈ A, singletonImage E ∈
      (Finset.shadow A).powersetCard 2 := by
    intro E hE
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro S hS
      obtain ⟨x, hxE, rfl⟩ := Finset.mem_image.mp hS
      exact hFacet E hE x hxE
    · rw [Finset.card_image_of_injective E hSingletonInjective, hUniform hE]
  have hImageInj : Set.InjOn singletonImage (↑A : Set (Edge α)) := by
    intro E hE F hF hEq
    ext x
    have hxE : x ∈ E ↔ ({x} : Edge α) ∈ singletonImage E := by
      simp [singletonImage]
    have hxF : x ∈ F ↔ ({x} : Edge α) ∈ singletonImage F := by
      simp [singletonImage]
    rw [hxE, hxF, hEq]
  have hCard : A.card ≤ ((Finset.shadow A).powersetCard 2).card :=
    Finset.card_le_card_of_injOn singletonImage hImageSub hImageInj
  rw [Finset.card_powersetCard] at hCard
  have hChoose : 2 * (Finset.shadow A).card.choose 2 ≤
      (Finset.shadow A).card ^ 2 := by
    rw [Nat.choose_two_right]
    calc
      2 * ((Finset.shadow A).card * ((Finset.shadow A).card - 1) / 2) ≤
          (Finset.shadow A).card * ((Finset.shadow A).card - 1) :=
        Nat.mul_div_le _ _
      _ ≤ (Finset.shadow A).card * (Finset.shadow A).card :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (Finset.shadow A).card ^ 2 := by simp [pow_two]
  calc
    2 * A.card ≤ 2 * (Finset.shadow A).card.choose 2 :=
      Nat.mul_le_mul_left 2 hCard
    _ ≤ (Finset.shadow A).card ^ 2 := hChoose

end JSP523.Rank5
