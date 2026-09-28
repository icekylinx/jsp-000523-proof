import JSP523.Counting.LinearTriple

/-!
# Linear uniform families are admissible above rank two

The cardinal obstruction and the centered-star criterion supply the
admissibility proofs for the equality constructions in Parts III and IV.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

theorem linear_uniform_admissible
    {H : Family α} {r : ℕ}
    (hr : 3 ≤ r) (hU : Uniform r H) (hL : LinearFamily H) :
    Admissible H := by
  intro A B C D hA hB hC hD hq
  have hAC : (A ∩ C).card ≤ 1 :=
    hL hA hC hq.distinct.ac
  have hAD : (A ∩ D).card ≤ 1 :=
    hL hA hD hq.distinct.ad
  have hAsub : A ⊆ C ∪ D := by
    intro x hxA
    have hxAB : x ∈ A ∪ B := Finset.mem_union_left B hxA
    rw [hq.sameUnion] at hxAB
    exact hxAB
  have hAeq : A = (A ∩ C) ∪ (A ∩ D) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hxA
      rcases Finset.mem_union.mp (hAsub hxA) with hxC | hxD
      · exact Or.inl ⟨hxA, hxC⟩
      · exact Or.inr ⟨hxA, hxD⟩
    · rintro (⟨hxA, _⟩ | ⟨hxA, _⟩) <;> exact hxA
  have hCard := Finset.card_union_le (A ∩ C) (A ∩ D)
  rw [← hAeq] at hCard
  have hAcard := hU hA
  omega


/-! The common admissibility criterion for the equality constructions in
§III.C.5 and §IV.2.3 of `paper/proof.pdf`. -/

omit [DecidableEq α] in
private theorem star_pair_not_disjoint
    {S : Family α} {v : α} {E F : Edge α}
    (hCenter : ∀ T ∈ S, v ∈ T) (hE : E ∈ S) (hF : F ∈ S) :
    ¬ Disjoint E F := by
  intro hEF
  exact (Finset.disjoint_left.mp hEF) (hCenter E hE) (hCenter F hF)

private theorem mixed_star_outside_impossible
    {S B : Family α} {v : α} {r : ℕ} {S₁ S₂ E F : Edge α}
    (hSUniform : Uniform r S) (hBUniform : Uniform r B)
    (hr : 3 ≤ r)
    (hLinear : LinearFamily B)
    (hCenter : ∀ T ∈ S, v ∈ T) (hAvoid : ∀ T ∈ B, v ∉ T)
    (hMissing : ∀ X ∈ B, ∀ Y ∈ B, X ≠ Y →
      ¬ Disjoint X Y →
        insert v (X \ Y) ∉ S ∨ insert v (Y \ X) ∉ S)
    (hS₁ : S₁ ∈ S) (hS₂ : S₂ ∈ S)
    (hE : E ∈ B) (hF : F ∈ B) (hEF : E ≠ F)
    (hUnion : S₁ ∪ E = S₂ ∪ F) : False := by
  have hEcard : E.card = r := hBUniform hE
  have hS₂card : S₂.card = r := hSUniform hS₂
  have hvS₂ : v ∈ S₂ := hCenter S₂ hS₂
  have hvE : v ∉ E := hAvoid E hE
  by_cases hDisj : Disjoint E F
  · have hEsub : E ⊆ S₂ := by
      intro x hxE
      have hxUnion : x ∈ S₁ ∪ E := Finset.mem_union_right S₁ hxE
      rw [hUnion] at hxUnion
      rcases Finset.mem_union.mp hxUnion with hxS₂ | hxF
      · exact hxS₂
      · exact False.elim ((Finset.disjoint_left.mp hDisj) hxE hxF)
    have hEq : E = S₂ := Finset.eq_of_subset_of_card_le hEsub (by omega)
    exact hvE (hEq ▸ hvS₂)
  · have hIntersectionPos : 0 < (E ∩ F).card := by
      have hNonempty : (E ∩ F).Nonempty := by
        by_contra hNone
        exact hDisj (Finset.disjoint_iff_inter_eq_empty.mpr
          (Finset.not_nonempty_iff_eq_empty.mp hNone))
      exact Finset.card_pos.mpr hNonempty
    have hIntersectionOne : (E ∩ F).card = 1 := by
      have hBound := hLinear hE hF hEF
      omega
    have hDiffCard : (E \ F).card = r - 1 := by
      have hCount := Finset.card_sdiff_add_card_inter E F
      omega
    have hDiffSub : E \ F ⊆ S₂ := by
      intro x hxDiff
      have hxE : x ∈ E := (Finset.mem_sdiff.mp hxDiff).1
      have hxF : x ∉ F := (Finset.mem_sdiff.mp hxDiff).2
      have hxUnion : x ∈ S₁ ∪ E := Finset.mem_union_right S₁ hxE
      rw [hUnion] at hxUnion
      rcases Finset.mem_union.mp hxUnion with hxS₂ | hxF'
      · exact hxS₂
      · exact False.elim (hxF hxF')
    have hvDiff : v ∉ E \ F := fun hv => hvE (Finset.mem_sdiff.mp hv).1
    have hInsertSub : insert v (E \ F) ⊆ S₂ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxDiff
      · exact hvS₂
      · exact hDiffSub hxDiff
    have hInsertCard : (insert v (E \ F)).card = r := by
      rw [Finset.card_insert_of_notMem hvDiff, hDiffCard]
      omega
    have hEq : insert v (E \ F) = S₂ :=
      Finset.eq_of_subset_of_card_le hInsertSub (by omega)
    rcases hMissing E hE F hF hEF hDisj with hMissE | hMissF
    · exact hMissE (hEq ▸ hS₂)
    · have hFcard : F.card = r := hBUniform hF
      have hS₁card : S₁.card = r := hSUniform hS₁
      have hvS₁ : v ∈ S₁ := hCenter S₁ hS₁
      have hvF : v ∉ F := hAvoid F hF
      have hInterSym : (F ∩ E).card = 1 := by
        simpa only [Finset.inter_comm] using hIntersectionOne
      have hDiffFCard : (F \ E).card = r - 1 := by
        have hCount := Finset.card_sdiff_add_card_inter F E
        omega
      have hDiffFSub : F \ E ⊆ S₁ := by
        intro x hxDiff
        have hxF : x ∈ F := (Finset.mem_sdiff.mp hxDiff).1
        have hxE : x ∉ E := (Finset.mem_sdiff.mp hxDiff).2
        have hxUnion : x ∈ S₂ ∪ F := Finset.mem_union_right S₂ hxF
        rw [← hUnion] at hxUnion
        rcases Finset.mem_union.mp hxUnion with hxS₁ | hxE'
        · exact hxS₁
        · exact False.elim (hxE hxE')
      have hvDiffF : v ∉ F \ E := fun hv => hvF (Finset.mem_sdiff.mp hv).1
      have hInsertFSub : insert v (F \ E) ⊆ S₁ := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxDiff
        · exact hvS₁
        · exact hDiffFSub hxDiff
      have hInsertFCard : (insert v (F \ E)).card = r := by
        rw [Finset.card_insert_of_notMem hvDiffF, hDiffFCard]
        omega
      have hEqF : insert v (F \ E) = S₁ :=
        Finset.eq_of_subset_of_card_le hInsertFSub (by omega)
      exact hMissF (hEqF ▸ hS₁)

/-- A centered rank-r star and a linear outside layer are admissible when
all intersecting outside pairs have at least one opposite star facet absent. -/
theorem star_plus_linear_outside_admissible
    {S B : Family α} {v : α} {r : ℕ}
    (hr : 3 ≤ r)
    (hSUniform : Uniform r S) (hBUniform : Uniform r B)
    (hLinear : LinearFamily B) (hCenter : ∀ T ∈ S, v ∈ T)
    (hAvoid : ∀ T ∈ B, v ∉ T)
    (hMissing : ∀ E ∈ B, ∀ F ∈ B, E ≠ F →
      ¬ Disjoint E F →
        insert v (E \ F) ∉ S ∨ insert v (F \ E) ∉ S) :
    Admissible (S ∪ B) := by
  intro A B₁ C D hA hB₁ hC hD hq
  simp only [Finset.mem_union] at hA hB₁ hC hD
  rcases hA with hAs | hAb <;>
  rcases hB₁ with hB₁s | hB₁b <;>
  rcases hC with hCs | hCb <;>
  rcases hD with hDs | hDb
  · exact star_pair_not_disjoint hCenter hAs hB₁s hq.disjAB
  · exact star_pair_not_disjoint hCenter hAs hB₁s hq.disjAB
  · exact star_pair_not_disjoint hCenter hAs hB₁s hq.disjAB
  · exact star_pair_not_disjoint hCenter hAs hB₁s hq.disjAB
  · exact star_pair_not_disjoint hCenter hCs hDs hq.disjCD
  · exact mixed_star_outside_impossible hSUniform hBUniform hr hLinear
      hCenter hAvoid hMissing hAs hCs hB₁b hDb hq.distinct.bd hq.sameUnion
  · exact mixed_star_outside_impossible hSUniform hBUniform hr hLinear
      hCenter hAvoid hMissing hAs hDs hB₁b hCb hq.distinct.bc
      (hq.sameUnion.trans (Finset.union_comm C D))
  · have hvLeft : v ∈ A ∪ B₁ := Finset.mem_union_left B₁ (hCenter A hAs)
    have hvRight : v ∉ C ∪ D := by
      intro hv
      rcases Finset.mem_union.mp hv with hvC | hvD
      · exact hAvoid C hCb hvC
      · exact hAvoid D hDb hvD
    exact hvRight (hq.sameUnion ▸ hvLeft)
  · exact star_pair_not_disjoint hCenter hCs hDs hq.disjCD
  · exact mixed_star_outside_impossible hSUniform hBUniform hr hLinear
      hCenter hAvoid hMissing hB₁s hCs hAb hDb hq.distinct.ad
      ((Finset.union_comm B₁ A).trans hq.sameUnion)
  · exact mixed_star_outside_impossible hSUniform hBUniform hr hLinear
      hCenter hAvoid hMissing hB₁s hDs hAb hCb hq.distinct.ac
      ((Finset.union_comm B₁ A).trans
        (hq.sameUnion.trans (Finset.union_comm C D)))
  · have hvLeft : v ∈ A ∪ B₁ := Finset.mem_union_right A (hCenter B₁ hB₁s)
    have hvRight : v ∉ C ∪ D := by
      intro hv
      rcases Finset.mem_union.mp hv with hvC | hvD
      · exact hAvoid C hCb hvC
      · exact hAvoid D hDb hvD
    exact hvRight (hq.sameUnion ▸ hvLeft)
  · exact star_pair_not_disjoint hCenter hCs hDs hq.disjCD
  · have hvLeft : v ∉ A ∪ B₁ := by
      intro hv
      rcases Finset.mem_union.mp hv with hvA | hvB₁
      · exact hAvoid A hAb hvA
      · exact hAvoid B₁ hB₁b hvB₁
    have hvRight : v ∈ C ∪ D := Finset.mem_union_left D (hCenter C hCs)
    exact hvLeft (hq.sameUnion.symm ▸ hvRight)
  · have hvLeft : v ∉ A ∪ B₁ := by
      intro hv
      rcases Finset.mem_union.mp hv with hvA | hvB₁
      · exact hAvoid A hAb hvA
      · exact hAvoid B₁ hB₁b hvB₁
    have hvRight : v ∈ C ∪ D := Finset.mem_union_right C (hCenter D hDs)
    exact hvLeft (hq.sameUnion.symm ▸ hvRight)
  · exact linear_uniform_admissible hr
      hBUniform hLinear hAb hB₁b hCb hDb hq

end JSP523
