import JSP523.Counting.LinearAdmissible
import JSP523.LowerConstruction
import JSP523.Counting.LinearNearStar

/-!
# Rank-r admissibility of the local equality constructions

This is the converse construction from §IV.2.3: a complete star plus a
matching, or with one star facet removed and two exceptional outside edges
meeting in one vertex.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

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

/-- The second §IV.2.3 construction is admissible at every rank `r ≥ 5`.
The assumptions encode disjoint `(r-1)`-blocks P,Q, their common external
vertex x, and a matching disjoint from their union. -/
theorem one_missing_star_exceptional_pair_admissible
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 5 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform r M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    Admissible (((starFamily v r).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M) ) := by
  let S : Family α := (starFamily v r).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  have hPcard' : (insert x P).card = r := by
    rw [Finset.card_insert_of_notMem hxP, hPcard]
    omega
  have hQcard' : (insert x Q).card = r := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
    omega
  have hSU : Uniform r S := by
    intro E hE
    exact (mem_starFamily.mp (Finset.mem_erase.mp hE).2).1
  have hBU : Uniform r B := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · exact hPcard'
    · exact hQcard'
    · exact hMU hEM
  have hCenter : ∀ E ∈ S, v ∈ E := by
    intro E hE
    exact (mem_starFamily.mp (Finset.mem_erase.mp hE).2).2
  have hAvoid : ∀ E ∈ B, v ∉ E := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · simp [hvx, hvP]
    · simp [hvx, hvQ]
    · exact hMAvoid E hEM
  have hSpecPDisj : ∀ E ∈ M, Disjoint (insert x P) E := by
    intro E hEM
    apply Finset.disjoint_left.mpr
    intro y hySpec hyE
    have hyBig : y ∈ insert x (P ∪ Q) := by
      rcases Finset.mem_insert.mp hySpec with rfl | hyP
      · simp
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left Q hyP)
    exact (Finset.disjoint_left.mp (hMDisj E hEM)) hyE hyBig
  have hSpecQDisj : ∀ E ∈ M, Disjoint (insert x Q) E := by
    intro E hEM
    apply Finset.disjoint_left.mpr
    intro y hySpec hyE
    have hyBig : y ∈ insert x (P ∪ Q) := by
      rcases Finset.mem_insert.mp hySpec with rfl | hyQ
      · simp
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right P hyQ)
    exact (Finset.disjoint_left.mp (hMDisj E hEM)) hyE hyBig
  have hSpecialOne : (insert x P ∩ insert x Q).card ≤ 1 := by
    have hInter : insert x P ∩ insert x Q = {x} := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyP, hyQ⟩ := Finset.mem_inter.mp hy
        rcases Finset.mem_insert.mp hyP with rfl | hyP'
        · simp
        rcases Finset.mem_insert.mp hyQ with rfl | hyQ'
        · simp
        exact False.elim ((Finset.disjoint_left.mp hPQ) hyP' hyQ')
      · intro hy
        have : y = x := Finset.mem_singleton.mp hy
        subst y
        simp
    rw [hInter]
    simp
  have hSpecialOneSym : (insert x Q ∩ insert x P).card ≤ 1 := by
    simpa only [Finset.inter_comm] using hSpecialOne
  have hBLin : LinearFamily B := by
    intro E F hE hF hne
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    change F ∈ insert (insert x P) (insert (insert x Q) M) at hF
    simp only [Finset.mem_insert] at hE hF
    rcases hE with rfl | rfl | hEM <;>
      rcases hF with rfl | rfl | hFM
    · exact False.elim (hne rfl)
    · exact hSpecialOne
    · have hD := hSpecPDisj F hFM
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · exact hSpecialOneSym
    · exact False.elim (hne rfl)
    · have hD := hSpecQDisj F hFM
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · have hD := (hSpecPDisj E hEM).symm
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · have hD := (hSpecQDisj E hEM).symm
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · have hD := hMatch hEM hFM hne
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
  have hMissingStar : insert v P ∉ S := Finset.notMem_erase _ _
  have hMissing : ∀ E ∈ B, ∀ F ∈ B, E ≠ F →
      ¬ Disjoint E F →
        insert v (E \ F) ∉ S ∨ insert v (F \ E) ∉ S := by
    intro E hE F hF hne hNonDisj
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    change F ∈ insert (insert x P) (insert (insert x Q) M) at hF
    simp only [Finset.mem_insert] at hE hF
    rcases hE with rfl | rfl | hEM <;>
      rcases hF with rfl | rfl | hFM
    · exact False.elim (hne rfl)
    · left
      have hDiff : insert x P \ insert x Q = P := by
        ext y
        constructor
        · intro hy
          have hh := Finset.mem_sdiff.mp hy
          rcases Finset.mem_insert.mp hh.1 with hyx | hyP
          · exact False.elim (hh.2 (hyx ▸ Finset.mem_insert_self x Q))
          · exact hyP
        · intro hyP
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_insert_of_mem hyP, ?_⟩
          intro hyQ
          rcases Finset.mem_insert.mp hyQ with hyx | hyQ'
          · exact hxP (hyx ▸ hyP)
          · exact (Finset.disjoint_left.mp hPQ) hyP hyQ'
      rw [hDiff]
      exact hMissingStar
    · exact False.elim (hNonDisj (hSpecPDisj F hFM))
    · right
      have hDiff : insert x P \ insert x Q = P := by
        ext y
        constructor
        · intro hy
          have hh := Finset.mem_sdiff.mp hy
          rcases Finset.mem_insert.mp hh.1 with hyx | hyP
          · exact False.elim (hh.2 (hyx ▸ Finset.mem_insert_self x Q))
          · exact hyP
        · intro hyP
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_insert_of_mem hyP, ?_⟩
          intro hyQ
          rcases Finset.mem_insert.mp hyQ with hyx | hyQ'
          · exact hxP (hyx ▸ hyP)
          · exact (Finset.disjoint_left.mp hPQ) hyP hyQ'
      rw [hDiff]
      exact hMissingStar
    · exact False.elim (hne rfl)
    · exact False.elim (hNonDisj (hSpecQDisj F hFM))
    · exact False.elim (hNonDisj (hSpecPDisj E hEM).symm)
    · exact False.elim (hNonDisj (hSpecQDisj E hEM).symm)
    · exact False.elim (hNonDisj (hMatch hEM hFM hne))
  change Admissible (S ∪ B)
  exact star_plus_linear_outside_admissible (by omega : 3 ≤ r)
    hSU hBU hBLin hCenter hAvoid hMissing

/-- Complete star plus a maximum matching is admissible for every positive
rank (the Rank 5 instance of the first §IV.2.3 equality construction). -/
theorem complete_star_plus_matching_admissible
    [Fintype α] {r : ℕ} {v : α} {M : Family α}
    (hr : 0 < r) (hMU : Uniform r M) (hMatch : IsMatching M)
    (hAvoid : ∀ E ∈ M, v ∉ E) :
    Admissible (starFamily v r ∪ M) := by
  simpa only [starPlusMatching] using
    starPlusMatching_admissible hr hMU hMatch hAvoid


/-- The complete rank-r star is parametrized without repetition by its
`(r-1)`-subsets of the vertices away from the center. -/
theorem rank_r_star_card [Fintype α] (v : α) (r : ℕ) (hr : 0 < r) :
    (starFamily v r).card =
      ((Finset.univ.erase v : Edge α).card).choose (r - 1) := by
  classical
  let W : Edge α := Finset.univ.erase v
  have hvW : v ∉ W := Finset.notMem_erase v Finset.univ
  have hEq : starFamily v r = (W.powersetCard (r - 1)).image (insert v) := by
    ext E
    constructor
    · intro hE
      obtain ⟨hEcard, hvE⟩ := mem_starFamily.mp hE
      have hTsub : E.erase v ⊆ W := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
      have hTcard : (E.erase v).card = r - 1 := by
        have hCount := Finset.card_erase_add_one hvE
        omega
      apply Finset.mem_image.mpr
      exact ⟨E.erase v,
        Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩,
        Finset.insert_erase hvE⟩
    · intro hE
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hE
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
      have hvT : v ∉ T := fun hv => hvW (hTsub hv)
      apply mem_starFamily.mpr
      constructor
      · rw [Finset.card_insert_of_notMem hvT, hTcard]
        omega
      · exact Finset.mem_insert_self v T
  have hInj : Set.InjOn (insert v)
      (↑(W.powersetCard (r - 1)) : Set (Edge α)) := by
    intro T hT S hS hES
    have hvT : v ∉ T := fun hv => hvW ((Finset.mem_powersetCard.mp hT).1 hv)
    have hvS : v ∉ S := fun hv => hvW ((Finset.mem_powersetCard.mp hS).1 hv)
    have hErase := congrArg (fun E : Edge α => E.erase v) hES
    simpa [Finset.erase_insert hvT, Finset.erase_insert hvS] using hErase
  rw [hEq, Finset.card_image_of_injOn hInj, Finset.card_powersetCard]

/-- First equality construction: the complete star plus an outside maximum
matching has its exact binomial-plus-matching size, is uniform/admissible,
and has no missing star facets. -/
theorem complete_star_plus_matching_extremal
    [Fintype α] {r : ℕ} {v : α} {M : Family α}
    (hr : 0 < r) (hMU : Uniform r M) (hMatch : IsMatching M)
    (hAvoid : ∀ E ∈ M, v ∉ E)
    (hMsize : M.card =
      (Finset.univ.erase v : Edge α).card / r) :
    let W : Edge α := Finset.univ.erase v
    let H : Family α := starFamily v r ∪ M
    Admissible H ∧ Uniform r H ∧
      (∀ E ∈ H, E ⊆ insert v W) ∧
      missingStarFacets H W v r = ∅ ∧
      H.card = W.card.choose (r - 1) + W.card / r := by
  classical
  let W : Edge α := Finset.univ.erase v
  let H : Family α := starFamily v r ∪ M
  have hvW : v ∉ W := Finset.notMem_erase v Finset.univ
  have hUniform : Uniform r H := by
    intro E hE
    simp only [H, Finset.mem_union] at hE
    rcases hE with hE | hE
    · exact (mem_starFamily.mp hE).1
    · exact hMU hE
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E hE
    simp only [H, Finset.mem_union] at hE
    rcases hE with hStar | hM
    · intro x hx
      by_cases hxv : x = v
      · subst x
        exact Finset.mem_insert_self v W
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩)
    · intro x hx
      by_cases hxv : x = v
      · subst x
        exact False.elim (hAvoid E hM hx)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩)
  have hMissing : missingStarFacets H W v r = ∅ := by
    ext T
    constructor
    · intro hT
      simp only [missingStarFacets, Finset.mem_filter] at hT
      obtain ⟨hT, hMiss⟩ := hT
      have hTp := Finset.mem_powersetCard.mp hT
      have hvT : v ∉ T := fun hv => hvW (hTp.1 hv)
      have hStar : insert v T ∈ starFamily v r := by
        apply mem_starFamily.mpr
        constructor
        · rw [Finset.card_insert_of_notMem hvT, hTp.2]
          omega
        · exact Finset.mem_insert_self v T
      exact False.elim (hMiss (Finset.mem_union_left M hStar))
    · simp
  have hAdmissible : Admissible H := by
    change Admissible (starFamily v r ∪ M)
    exact starPlusMatching_admissible hr hMU hMatch hAvoid
  have hDisj : Disjoint (starFamily v r) M := by
    apply Finset.disjoint_left.mpr
    intro E hStar hM
    exact hAvoid E hM (mem_starFamily.mp hStar).2
  have hCard : H.card = W.card.choose (r - 1) + W.card / r := by
    change (starFamily v r ∪ M).card = W.card.choose (r - 1) + W.card / r
    rw [Finset.card_union_of_disjoint hDisj,
      rank_r_star_card v r hr, hMsize]
  exact ⟨hAdmissible, hUniform, hSupport, hMissing, hCard⟩

/-- Exceptional construction data, including the unique missing facet P. -/
theorem one_missing_star_exceptional_pair_equality_data
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 5 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform r M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q)))
    (hMsize : M.card + 1 =
      (Finset.univ.erase v : Edge α).card / r) :
    let W : Edge α := Finset.univ.erase v
    let S : Family α := (starFamily v r).erase (insert v P)
    let B : Family α := insert (insert x P) (insert (insert x Q) M)
    let H : Family α := S ∪ B
    Admissible H ∧ Uniform r H ∧
      (∀ E ∈ H, E ⊆ insert v W) ∧
      missingStarFacets H W v r = {P} ∧
      Uniform (r - 1) (missingStarFacets H W v r) ∧
      (missingStarFacets H W v r).card = 1 ∧
      H.card = W.card.choose (r - 1) + W.card / r := by
  classical
  let W : Edge α := Finset.univ.erase v
  let S : Family α := (starFamily v r).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  let H : Family α := S ∪ B
  have hvW : v ∉ W := Finset.notMem_erase v Finset.univ
  have hPsub : P ⊆ W := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨by
      intro h
      exact hvP (h ▸ hy), Finset.mem_univ _⟩
  have hPfacet : P ∈ W.powersetCard (r - 1) :=
    Finset.mem_powersetCard.mpr ⟨hPsub, hPcard⟩
  have hPstar : insert v P ∈ starFamily v r := by
    apply mem_starFamily.mpr
    constructor
    · rw [Finset.card_insert_of_notMem hvP, hPcard]
      omega
    · exact Finset.mem_insert_self v P
  have hSpecialAvoid : ∀ E ∈ B, v ∉ E := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · simp [hvx, hvP]
    · simp [hvx, hvQ]
    · exact hMAvoid E hEM
  have hUniform : Uniform r H := by
    intro E hE
    simp only [H, Finset.mem_union] at hE
    rcases hE with hE | hE
    · exact (mem_starFamily.mp (Finset.mem_erase.mp hE).2).1
    · change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
      simp only [Finset.mem_insert] at hE
      rcases hE with rfl | rfl | hEM
      · rw [Finset.card_insert_of_notMem hxP, hPcard]
        omega
      · rw [Finset.card_insert_of_notMem hxQ, hQcard]
        omega
      · exact hMU hEM
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E hE y hy
    simp only [H, Finset.mem_union] at hE
    rcases hE with hES | hEB
    · have hStar := (Finset.mem_erase.mp hES).2
      by_cases hyv : y = v
      · subst y
        exact Finset.mem_insert_self v W
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ _⟩)
    · by_cases hyv : y = v
      · subst y
        exact False.elim (hSpecialAvoid E hEB hy)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ _⟩)
  have hNotP : insert v P ∉ B := by
    intro h
    exact (hSpecialAvoid (insert v P) h) (Finset.mem_insert_self v P)
  have hMissing : missingStarFacets H W v r = {P} := by
    ext T
    simp only [missingStarFacets, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hT, hMiss⟩
      by_cases hTP : T = P
      · exact hTP
      · have hTsub := (Finset.mem_powersetCard.mp hT).1
        have hvT : v ∉ T := fun hv => hvW (hTsub hv)
        have hStar : insert v T ∈ starFamily v r := by
          apply mem_starFamily.mpr
          constructor
          · rw [Finset.card_insert_of_notMem hvT, (Finset.mem_powersetCard.mp hT).2]
            omega
          · exact Finset.mem_insert_self v T
        have hNotErase : insert v T ≠ insert v P := by
          intro hEq
          have hErase := congrArg (fun E : Edge α => E.erase v) hEq
          have hEraseTP : T = P := by
            simpa [Finset.erase_insert hvT, Finset.erase_insert hvP] using hErase
          exact hTP hEraseTP
        have hInS : insert v T ∈ S := Finset.mem_erase.mpr ⟨hNotErase, hStar⟩
        exact False.elim (hMiss (Finset.mem_union_left B hInS))
    · intro hTP
      have hT : T = P := hTP
      subst T
      refine ⟨hPfacet, ?_⟩
      intro hH
      simp only [H, Finset.mem_union] at hH
      rcases hH with hS | hB
      · exact (Finset.mem_erase.mp hS).1 rfl
      · exact hNotP hB
  have hMissingUniform : Uniform (r - 1) (missingStarFacets H W v r) := by
    intro T hT
    rw [hMissing] at hT
    have : T = P := Finset.mem_singleton.mp hT
    subst T
    exact hPcard
  have hMissingCard : (missingStarFacets H W v r).card = 1 := by
    rw [hMissing]
    simp
  have hAdmissible : Admissible H :=
    one_missing_star_exceptional_pair_admissible hr hPcard hQcard hPQ
      hxP hxQ hvx hvP hvQ hMU hMatch hMAvoid hMDisj
  have hStarMem : insert v P ∈ starFamily v r := hPstar
  have hSCard : S.card + 1 = W.card.choose (r - 1) := by
    have hErase := Finset.card_erase_add_one hStarMem
    rw [rank_r_star_card v r (by omega)] at hErase
    exact hErase
  have hQnotM : insert x Q ∉ M := by
    intro hQM
    exact (Finset.disjoint_left.mp (hMDisj (insert x Q) hQM))
      (Finset.mem_insert_self x Q) (Finset.mem_insert_self x (P ∪ Q))
  have hPnotM : insert x P ∉ M := by
    intro hPM
    exact (Finset.disjoint_left.mp (hMDisj (insert x P) hPM))
      (Finset.mem_insert_self x P) (Finset.mem_insert_self x (P ∪ Q))
  have hSpecNe : insert x P ≠ insert x Q := by
    intro hEq
    have hEqPQ : P = Q := by
      have hErase := congrArg (fun E : Edge α => E.erase x) hEq
      simpa [Finset.erase_insert hxP, Finset.erase_insert hxQ] using hErase
    subst Q
    obtain ⟨y, hyP⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
    exact (Finset.disjoint_left.mp hPQ) hyP hyP
  have hPnotTail : insert x P ∉ insert (insert x Q) M := by
    simp only [Finset.mem_insert]
    exact not_or.mpr ⟨hSpecNe, hPnotM⟩
  have hBcard : B.card = M.card + 2 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hPnotTail,
      Finset.card_insert_of_notMem hQnotM]
  have hSBDisj : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro E hES hEB
    have hvE := (mem_starFamily.mp (Finset.mem_erase.mp hES).2).2
    exact hSpecialAvoid E hEB hvE
  have hCard : H.card = W.card.choose (r - 1) + W.card / r := by
    have hUnionCard := Finset.card_union_of_disjoint hSBDisj
    have hMsize' : M.card + 1 = W.card / r := by
      simpa [W] using hMsize
    change (S ∪ B).card = W.card.choose (r - 1) + W.card / r
    rw [hUnionCard, hBcard]
    omega
  exact ⟨hAdmissible, hUniform, hSupport, hMissing, hMissingUniform,
    hMissingCard, hCard⟩

end JSP523.Rank5
