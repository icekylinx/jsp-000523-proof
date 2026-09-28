import JSP523.Counting.LinearAdmissible
import JSP523.LowerConstruction

/-!
# Admissibility of the rank-four equality constructions

The converse direction of §III.C.5 needs a slightly more general fact than
the complete-star plus matching construction.  A linear outside family may
have intersecting pairs if the star edge opposite every such pair is
missing.  The following finite theorem states this exact condition.
-/

namespace JSP523.Rank4

variable {α : Type*}

private theorem star_pair_not_disjoint
    {S : Family α} {v : α} {E F : Edge α}
    (hCenter : ∀ T ∈ S, v ∈ T)
    (hE : E ∈ S) (hF : F ∈ S) : ¬ Disjoint E F := by
  intro hEF
  exact (Finset.disjoint_left.mp hEF) (hCenter E hE) (hCenter F hF)

variable [DecidableEq α]

/-- In a mixed repeated-union partition, a linear outside pair forces the
star edge opposite its difference set.  If that star edge is absent, the
partition is impossible. -/
private theorem mixed_star_outside_impossible
    {S B : Family α} {v : α} {S₁ S₂ E F : Edge α}
    (hSUniform : Uniform 4 S) (hBUniform : Uniform 4 B)
    (hLinear : LinearFamily B)
    (hCenter : ∀ T ∈ S, v ∈ T)
    (hAvoid : ∀ T ∈ B, v ∉ T)
    (hMissing : ∀ X ∈ B, ∀ Y ∈ B, X ≠ Y →
      ¬ Disjoint X Y →
        insert v (X \ Y) ∉ S ∨ insert v (Y \ X) ∉ S)
    (hS₁ : S₁ ∈ S) (hS₂ : S₂ ∈ S)
    (hE : E ∈ B) (hF : F ∈ B)
    (hEF : E ≠ F) (hUnion : S₁ ∪ E = S₂ ∪ F) : False := by
  have hEcard : E.card = 4 := hBUniform hE
  have hS₂card : S₂.card = 4 := hSUniform hS₂
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
    have hEq : E = S₂ :=
      Finset.eq_of_subset_of_card_le hEsub (by omega)
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
    have hDiffCard : (E \ F).card = 3 := by
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
    have hvDiff : v ∉ E \ F := by
      intro hv
      exact hvE (Finset.mem_sdiff.mp hv).1
    have hInsertSub : insert v (E \ F) ⊆ S₂ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxDiff
      · exact hvS₂
      · exact hDiffSub hxDiff
    have hInsertCard : (insert v (E \ F)).card = 4 := by
      rw [Finset.card_insert_of_notMem hvDiff, hDiffCard]
    have hEq : insert v (E \ F) = S₂ :=
      Finset.eq_of_subset_of_card_le hInsertSub (by omega)
    rcases hMissing E hE F hF hEF hDisj with hMissE | hMissF
    · exact hMissE (hEq ▸ hS₂)
    · have hFcard : F.card = 4 := hBUniform hF
      have hS₁card : S₁.card = 4 := hSUniform hS₁
      have hvS₁ : v ∈ S₁ := hCenter S₁ hS₁
      have hvF : v ∉ F := hAvoid F hF
      have hInterSym : (F ∩ E).card = 1 := by
        simpa only [Finset.inter_comm] using hIntersectionOne
      have hDiffFCard : (F \ E).card = 3 := by
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
      have hvDiffF : v ∉ F \ E := by
        intro hv
        exact hvF (Finset.mem_sdiff.mp hv).1
      have hInsertFSub : insert v (F \ E) ⊆ S₁ := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxDiff
        · exact hvS₁
        · exact hDiffFSub hxDiff
      have hInsertFCard : (insert v (F \ E)).card = 4 := by
        rw [Finset.card_insert_of_notMem hvDiffF, hDiffFCard]
      have hEqF : insert v (F \ E) = S₁ :=
        Finset.eq_of_subset_of_card_le hInsertFSub (by omega)
      exact hMissF (hEqF ▸ hS₁)

/-- A centered rank-four star subfamily and a linear outside family form
an admissible family whenever every intersecting outside pair has its
opposite star edge absent.  This contains both equality constructions in
§III.C.5 as special cases. -/
theorem star_plus_linear_outside_admissible
    {S B : Family α} {v : α}
    (hSUniform : Uniform 4 S) (hBUniform : Uniform 4 B)
    (hLinear : LinearFamily B)
    (hCenter : ∀ T ∈ S, v ∈ T)
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
  · exact mixed_star_outside_impossible hSUniform hBUniform
      hLinear hCenter hAvoid hMissing hAs hCs hB₁b hDb
      hq.distinct.bd hq.sameUnion
  · exact mixed_star_outside_impossible hSUniform hBUniform
      hLinear hCenter hAvoid hMissing hAs hDs hB₁b hCb
      hq.distinct.bc (hq.sameUnion.trans (Finset.union_comm C D))
  · have hvLeft : v ∈ A ∪ B₁ :=
      Finset.mem_union_left B₁ (hCenter A hAs)
    have hvRight : v ∉ C ∪ D := by
      intro hv
      rcases Finset.mem_union.mp hv with hvC | hvD
      · exact hAvoid C hCb hvC
      · exact hAvoid D hDb hvD
    exact hvRight (hq.sameUnion ▸ hvLeft)
  · exact star_pair_not_disjoint hCenter hCs hDs hq.disjCD
  · exact mixed_star_outside_impossible hSUniform hBUniform
      hLinear hCenter hAvoid hMissing hB₁s hCs hAb hDb
      hq.distinct.ad ((Finset.union_comm B₁ A).trans hq.sameUnion)
  · exact mixed_star_outside_impossible hSUniform hBUniform
      hLinear hCenter hAvoid hMissing hB₁s hDs hAb hCb
      hq.distinct.ac ((Finset.union_comm B₁ A).trans
        (hq.sameUnion.trans (Finset.union_comm C D)))
  · have hvLeft : v ∈ A ∪ B₁ :=
      Finset.mem_union_right A (hCenter B₁ hB₁s)
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
    have hvRight : v ∈ C ∪ D :=
      Finset.mem_union_left D (hCenter C hCs)
    exact hvLeft (hq.sameUnion.symm ▸ hvRight)
  · have hvLeft : v ∉ A ∪ B₁ := by
      intro hv
      rcases Finset.mem_union.mp hv with hvA | hvB₁
      · exact hAvoid A hAb hvA
      · exact hAvoid B₁ hB₁b hvB₁
    have hvRight : v ∈ C ∪ D :=
      Finset.mem_union_right C (hCenter D hDs)
    exact hvLeft (hq.sameUnion.symm ▸ hvRight)
  · exact linear_uniform_admissible (by omega : 3 ≤ 4)
      hBUniform hLinear hAb hB₁b hCb hDb hq

/-- The two exceptional outside edges meet only in their shared vertex. -/
theorem exceptional_pair_intersection
    {P Q : Edge α} {x : α} (hPQ : Disjoint P Q) :
    insert x P ∩ insert x Q = {x} := by
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
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst y
    simp

/-- The opposite facet of the first exceptional edge is exactly P. -/
theorem exceptional_pair_difference
    {P Q : Edge α} {x : α}
    (hPQ : Disjoint P Q) (hxP : x ∉ P) :
    insert x P \ insert x Q = P := by
  ext y
  constructor
  · intro hy
    have h := Finset.mem_sdiff.mp hy
    rcases Finset.mem_insert.mp h.1 with hyx | hyP
    · exact False.elim (h.2 (hyx ▸ Finset.mem_insert_self x Q))
    · exact hyP
  · intro hyP
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_insert_of_mem hyP, ?_⟩
    intro hyQ
    rcases Finset.mem_insert.mp hyQ with hyx | hyQ'
    · exact hxP (hyx ▸ hyP)
    · exact (Finset.disjoint_left.mp hPQ) hyP hyQ'

/-- The second equality family of §III.C.5 is admissible: one star facet is
removed, two outside blocks meet at a vertex, and the remaining outside
blocks form a matching disjoint from them. -/
theorem one_missing_star_exceptional_pair_admissible
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform 4 M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    Admissible
      (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)) := by
  let S : Family α := (starFamily v 4).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  have hP4 : (insert x P).card = 4 := by
    rw [Finset.card_insert_of_notMem hxP, hPcard]
  have hQ4 : (insert x Q).card = 4 := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
  have hSU : Uniform 4 S := by
    intro E hE
    exact (mem_starFamily.mp (Finset.mem_erase.mp hE).2).1
  have hBU : Uniform 4 B := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · exact hP4
    · exact hQ4
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
    rw [exceptional_pair_intersection hPQ]
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
  have hMissingStar : insert v P ∉ S := by
    exact Finset.notMem_erase _ _
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
      rw [exceptional_pair_difference hPQ hxP]
      exact hMissingStar
    · exact False.elim (hNonDisj (hSpecPDisj F hFM))
    · right
      rw [exceptional_pair_difference hPQ hxP]
      exact hMissingStar
    · exact False.elim (hne rfl)
    · exact False.elim (hNonDisj (hSpecQDisj F hFM))
    · exact False.elim (hNonDisj (hSpecPDisj E hEM).symm)
    · exact False.elim (hNonDisj (hSpecQDisj E hEM).symm)
    · exact False.elim (hNonDisj (hMatch hEM hFM hne))
  change Admissible (S ∪ B)
  exact star_plus_linear_outside_admissible hSU hBU hBLin
    hCenter hAvoid hMissing

/-- The number of four-edges in a complete star is the number of outside
triples. -/
theorem rank_four_star_card
    [Fintype α] (v : α) :
    (starFamily v 4).card =
      ((Finset.univ.erase v : Edge α).card).choose 3 := by
  classical
  let W : Edge α := Finset.univ.erase v
  have hvW : v ∉ W := Finset.notMem_erase v Finset.univ
  have hEq : starFamily v 4 =
      (W.powersetCard 3).image (insert v) := by
    ext E
    constructor
    · intro hE
      obtain ⟨hEcard, hvE⟩ := mem_starFamily.mp hE
      have hTsub : E.erase v ⊆ W := by
        intro x hx
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
      have hTcard : (E.erase v).card = 3 := by
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
      · exact Finset.mem_insert_self v T
  have hInj : Set.InjOn (insert v)
      (↑(W.powersetCard 3) : Set (Edge α)) := by
    intro T hT S hS hEq
    have hvT : v ∉ T := fun hv =>
      hvW ((Finset.mem_powersetCard.mp hT).1 hv)
    have hvS : v ∉ S := fun hv =>
      hvW ((Finset.mem_powersetCard.mp hS).1 hv)
    have hErase := congrArg (fun E : Edge α => E.erase v) hEq
    simpa [hvT, hvS] using hErase
  rw [hEq, Finset.card_image_of_injOn hInj,
    Finset.card_powersetCard]

/-- The complete-star plus maximum outside matching equality family. -/
theorem complete_star_max_matching_extremal
    [Fintype α] {v : α} {M : Family α}
    (hMU : Uniform 4 M) (hMatch : IsMatching M)
    (hAvoid : ∀ E ∈ M, v ∉ E)
    (hMsize : M.card = (Finset.univ.erase v : Edge α).card / 4) :
    Admissible (starFamily v 4 ∪ M) ∧
      (starFamily v 4 ∪ M).card =
        ((Finset.univ.erase v : Edge α).card).choose 3 +
          (Finset.univ.erase v : Edge α).card / 4 := by
  have hAdmissible : Admissible (starFamily v 4 ∪ M) := by
    simpa only [starPlusMatching] using
      starPlusMatching_admissible (by omega : 0 < 4)
        hMU hMatch hAvoid
  have hDisj : Disjoint (starFamily v 4) M := by
    apply Finset.disjoint_left.mpr
    intro E hStar hM
    exact hAvoid E hM (mem_starFamily.mp hStar).2
  constructor
  · exact hAdmissible
  · rw [Finset.card_union_of_disjoint hDisj,
      rank_four_star_card, hMsize]

/-- The one-missing-star construction has the extremal count whenever the
auxiliary matching has one fewer block than a maximum outside matching. -/
theorem one_missing_star_exceptional_pair_card
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    (((starFamily v 4).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M)).card =
      ((Finset.univ.erase v : Edge α).card).choose 3 + M.card + 1 := by
  classical
  let S : Family α := (starFamily v 4).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  have hStarMem : insert v P ∈ starFamily v 4 := by
    apply mem_starFamily.mpr
    constructor
    · rw [Finset.card_insert_of_notMem hvP, hPcard]
    · exact Finset.mem_insert_self v P
  have hSCard : S.card + 1 =
      ((Finset.univ.erase v : Edge α).card).choose 3 := by
    have hErase := Finset.card_erase_add_one hStarMem
    rw [rank_four_star_card] at hErase
    exact hErase
  have hP4 : (insert x P).card = 4 := by
    rw [Finset.card_insert_of_notMem hxP, hPcard]
  have hQ4 : (insert x Q).card = 4 := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
  have hSpecialNe : insert x P ≠ insert x Q := by
    intro hEq
    have hInter := exceptional_pair_intersection (x := x) hPQ
    rw [hEq, Finset.inter_self] at hInter
    have hCard := congrArg Finset.card hInter
    simp [hQ4] at hCard
  have hPnotM : insert x P ∉ M := by
    intro hPM
    have hD := hMDisj (insert x P) hPM
    exact (Finset.disjoint_left.mp hD)
      (Finset.mem_insert_self x P)
      (Finset.mem_insert_self x (P ∪ Q))
  have hQnotM : insert x Q ∉ M := by
    intro hQM
    have hD := hMDisj (insert x Q) hQM
    exact (Finset.disjoint_left.mp hD)
      (Finset.mem_insert_self x Q)
      (Finset.mem_insert_self x (P ∪ Q))
  have hPnotTail : insert x P ∉ insert (insert x Q) M := by
    simp only [Finset.mem_insert]
    exact not_or.mpr ⟨hSpecialNe, hPnotM⟩
  have hBCard : B.card = M.card + 2 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hPnotTail,
      Finset.card_insert_of_notMem hQnotM]
  have hSBAvoid : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro E hES hEB
    have hvE : v ∈ E :=
      (mem_starFamily.mp (Finset.mem_erase.mp hES).2).2
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hEB
    simp only [Finset.mem_insert] at hEB
    rcases hEB with rfl | rfl | hEM
    · simp [hvx, hvP] at hvE
    · simp [hvx, hvQ] at hvE
    · exact hMAvoid E hEM hvE
  have hUnionCard := Finset.card_union_of_disjoint hSBAvoid
  change (S ∪ B).card = S.card + B.card at hUnionCard
  change (S ∪ B).card =
    ((Finset.univ.erase v : Edge α).card).choose 3 + M.card + 1
  omega

/-- The second equality construction attains the claimed rank-four count
when its ordinary matching covers the remaining outside vertices. -/
theorem one_missing_star_exceptional_pair_extremal
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform 4 M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q)))
    (hMsize : M.card + 1 =
      (Finset.univ.erase v : Edge α).card / 4) :
    Admissible
      (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)) ∧
    (((starFamily v 4).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M)).card =
      ((Finset.univ.erase v : Edge α).card).choose 3 +
        (Finset.univ.erase v : Edge α).card / 4 := by
  constructor
  · exact one_missing_star_exceptional_pair_admissible hPcard hQcard
      hPQ hxP hxQ hvx hvP hvQ hMU hMatch hMAvoid hMDisj
  · rw [one_missing_star_exceptional_pair_card hPcard hQcard
      hPQ hxP hxQ hvx hvP hvQ hMAvoid hMDisj]
    omega

end JSP523.Rank4
