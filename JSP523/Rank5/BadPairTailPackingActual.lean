import JSP523.Rank5.LocalExactDeletion

/-!
# Actual tail packing for two bad-pair roots

The two root geometries in §IV.2.1 have different tail distances. Disjoint
bad pairs give a four-set root and distance two; intersecting bad pairs give
a three-set root and distance three, provided the edge has no disjoint bad
pair. This file derives the required cleanliness from those actual premises.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- A bad two-set contains a pair root, so it has the prescribed size. -/
theorem badPair_card_of_mem
    {H : Family α} {W P : Edge α} {v : α} {r : ℕ}
    {Λ₂ : ℕ} (hP : P ∈ badMissingSets H W v r 2 Λ₂) :
    P.card = 2 :=
  (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2

/-- A singleton bad root cannot be contained in an ordinary outside edge. -/
private theorem no_bad_singleton_subset_ordinary_edge
    {H : Family α} {W E Q : Edge α} {v : α} {r : ℕ}
    (hOrd : E ⊆ W \ badSingletonVertices H W v r)
    (hQ : Q ∈ badMissingSets H W v r 1
      ((W.card - r - 1).choose (r - 2)))
    (hQE : Q ⊆ E) (hQcard : Q.card = 1) : False := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hQcard
  have hxQ : x ∈ Q := by rw [hx]; simp
  have hxE : x ∈ E := hQE hxQ
  have hxNotD : x ∉ badSingletonVertices H W v r := by
    exact (Finset.mem_sdiff.mp (hOrd hxE)).2
  have hxW : x ∈ W := (Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp hQ).1).1 hxQ
  have hxBad : ({x} : Edge α) ∈ badMissingSets H W v r 1
      ((W.card - r - 1).choose (r - 2)) := by
    simpa [hx] using hQ
  exact hxNotD (Finset.mem_filter.mpr ⟨hxW, hxBad⟩)

/-- Edges in the intersecting-root stratum: they contain no two disjoint bad
pairs. -/
noncomputable def noDisjointBadPairEdges
    (B Bad₂ : Family α) : Family α := by
  classical
  exact B.filter fun E =>
    ∀ P ∈ Bad₂, P ⊆ E → ∀ R ∈ Bad₂, R ⊆ E → ¬ Disjoint P R

theorem mem_noDisjointBadPairEdges
    {B Bad₂ : Family α} {E : Edge α} :
    E ∈ noDisjointBadPairEdges B Bad₂ ↔
      E ∈ B ∧ ∀ P ∈ Bad₂, P ⊆ E →
        ∀ R ∈ Bad₂, R ⊆ E → ¬ Disjoint P R := by
  classical
  simp [noDisjointBadPairEdges]

/-- For disjoint bad pair roots, ordinary outside edges have tail distance at
least two. The fixed-root packing lemma then gives the finite binomial cap. -/
theorem disjoint_bad_pair_root_tail_packing_bound
    {H B Bad₂ : Family α} {W P R : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hOrdinary : ∀ E ∈ B, E ⊆ W \ badSingletonVertices H W v r)
    (hvW : v ∉ W)
    (hBad₂ : Bad₂ = badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3)))
    (hP : P ∈ Bad₂) (hR : R ∈ Bad₂) (hPR : Disjoint P R) :
    (B.filter fun E => P ∪ R ⊆ E).card ≤
      if 2 ≤ r - 4 then W.card.choose (r - 4 - 2 + 1) else 1 := by
  have hPcard : P.card = 2 := by rw [hBad₂] at hP; exact badPair_card_of_mem hP
  have hRcard : R.card = 2 := by rw [hBad₂] at hR; exact badPair_card_of_mem hR
  let S := P ∪ R
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hPR, hPcard, hRcard]
  have hBound := fixed_root_fiber_packing_bound_general
    (H := H) (B := B) (W := W) (P := S) (v := v) (r := r)
    (s := 4) (d := 2) hH hBH hBuniform hW hvW hScard (by omega) (by omega)
    (by
      intro E hE hSE j hj hjs Q hQsub hQcard
      have hj1 : j = 1 := by omega
      have hQcard1 : Q.card = 1 := by omega
      intro hQmem
      have hQbad : Q ∈ badMissingSets H W v r 1
          ((W.card - r - 1).choose (r - 2)) := by
        simpa [hj1, hQcard1, show r - 1 - 1 = r - 2 by omega] using hQmem
      exact no_bad_singleton_subset_ordinary_edge (hOrdinary E hE) hQbad
        (by
          intro x hx
          exact (Finset.mem_sdiff.mp (hQsub hx)).1) hQcard1)
  have hEq : (B.filter fun E => P ∪ R ⊆ E) =
      B.filter fun E => S ⊆ E := by ext E; simp [S]
  rw [hEq]
  simpa [hScard] using hBound

/-- For intersecting bad pair roots in an edge with no disjoint bad pairs,
the union root has size three and all tails have distance at least three.
The distance-three premise follows because any bad pair in the tail would be
disjoint from the fixed bad root. -/
theorem intersecting_bad_pair_root_tail_packing_bound
    {H B Bad₂ : Family α} {W P R : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hOrdinary : ∀ E ∈ B, E ⊆ W \ badSingletonVertices H W v r)
    (hvW : v ∉ W)
    (hBad₂ : Bad₂ = badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3)))
    (hP : P ∈ Bad₂) (hR : R ∈ Bad₂)
    (hPR : P ≠ R) (hNotDisj : ¬ Disjoint P R) :
    ((noDisjointBadPairEdges B Bad₂).filter
      fun E => P ∪ R ⊆ E).card ≤
      if 3 ≤ r - 3 then W.card.choose (r - 3 - 3 + 1) else 1 := by
  have hPcard : P.card = 2 := by rw [hBad₂] at hP; exact badPair_card_of_mem hP
  have hRcard : R.card = 2 := by rw [hBad₂] at hR; exact badPair_card_of_mem hR
  have hInterCard : (P ∩ R).card = 1 := by
    have hPos : 0 < (P ∩ R).card :=
      Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hNotDisj)
    have hLe : (P ∩ R).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq hPcard
    by_contra hNe
    have hEq : (P ∩ R).card = 2 := by omega
    have hSub : P ⊆ R := by
      intro x hx
      have hxI : x ∈ P ∩ R := by
        have hPI : P ∩ R = P :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        rw [hPI]
        exact hx
      exact (Finset.mem_inter.mp hxI).2
    exact hPR (Finset.eq_of_subset_of_card_le hSub (by omega))
  let S := P ∪ R
  have hScard : S.card = 3 := by
    dsimp [S]
    have h := Finset.card_union_add_card_inter P R
    rw [hPcard, hRcard, hInterCard] at h
    omega
  let B₀ := noDisjointBadPairEdges B Bad₂
  have hB₀H : B₀ ⊆ H := by
    intro E hE
    exact hBH ((mem_noDisjointBadPairEdges.mp hE).1)
  have hB₀uniform : Uniform r B₀ := by
    intro E hE
    exact hBuniform ((mem_noDisjointBadPairEdges.mp hE).1)
  have hB₀W : ∀ E ∈ B₀, E ⊆ W := by
    intro E hE
    exact hW E ((mem_noDisjointBadPairEdges.mp hE).1)
  have hB₀ordinary : ∀ E ∈ B₀,
      E ⊆ W \ badSingletonVertices H W v r := by
    intro E hE
    exact hOrdinary E ((mem_noDisjointBadPairEdges.mp hE).1)
  have hBound := fixed_root_fiber_packing_bound_general
    (H := H) (B := B₀) (W := W) (P := S) (v := v) (r := r)
    (s := 3) (d := 3) hH hB₀H hB₀uniform hB₀W hvW hScard (by omega) (by omega)
    (by
      intro E hE hSE j hj hjs Q hQsub hQcard
      by_cases hj1 : j = 1
      · have hQcard1 : Q.card = 1 := by omega
        intro hQmem
        have hQbad : Q ∈ badMissingSets H W v r 1
            ((W.card - r - 1).choose (r - 2)) := by
          simpa [hj1, hQcard1, show r - 1 - 1 = r - 2 by omega] using hQmem
        exact no_bad_singleton_subset_ordinary_edge (hB₀ordinary E hE) hQbad
          (by
            intro x hx
            exact (Finset.mem_sdiff.mp (hQsub hx)).1) hQcard1
      · have hj2 : j = 2 := by omega
        have hQcard2 : Q.card = 2 := by omega
        intro hQmem
        have hQmem2 : Q ∈ badMissingSets H W v r 2
            ((W.card - r - 2).choose (r - 3)) := by
          simpa [hj2, hQcard2, show r - 1 - 2 = r - 3 by omega] using hQmem
        have hQbad : Q ∈ Bad₂ := by
          rw [hBad₂]
          exact hQmem2
        have hQdisj : Disjoint P Q := by
          apply Finset.disjoint_left.mpr
          intro x hxP hxQ
          have hxNotS : x ∉ S := (Finset.mem_sdiff.mp (hQsub hxQ)).2
          exact hxNotS (Finset.mem_union_left R hxP)
        exact (mem_noDisjointBadPairEdges.mp hE).2 P hP
          (fun x hx => hSE (Finset.mem_union_left R hx))
          Q hQbad (fun x hx => (Finset.mem_sdiff.mp (hQsub hx)).1) hQdisj)
  have hEq : (B₀.filter fun E => P ∪ R ⊆ E) =
      B₀.filter fun E => S ⊆ E := by ext E; simp [S]
  rw [hEq]
  simpa [hScard] using hBound

/-- Every edge containing a bad pair belongs to the unique-pair class, the
disjoint-pair class, or the intersecting-pair class filtered to edges with no
disjoint bad-pair witnesses. -/
theorem bad_pair_edges_covered_by_filtered_strata
    {B Bad₂ : Family α} :
    badPairEdges B Bad₂ ⊆
      uniqueBadPairEdges B Bad₂ ∪
        twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q) ∪
        twoBadPairEdges (noDisjointBadPairEdges B Bad₂) Bad₂
          (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q) := by
  classical
  intro E hE
  obtain ⟨P, hP, hPE⟩ := Finset.mem_biUnion.mp hE
  have hEB : E ∈ B := (Finset.mem_filter.mp hPE).1
  have hPEsub : P ⊆ E := (Finset.mem_filter.mp hPE).2
  let S := Bad₂.filter fun Q => Q ⊆ E
  have hPS : P ∈ S := Finset.mem_filter.mpr ⟨hP, hPEsub⟩
  by_cases hOne : S.card = 1
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨P, hP, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨hEB, ⟨hPEsub, by simpa [S] using hOne⟩⟩
  · have hTwo : 2 ≤ S.card := by
      have hPos : 0 < S.card := Finset.card_pos.mpr ⟨P, hPS⟩
      omega
    obtain ⟨Q, hQ, R, hR, hQR⟩ := Finset.one_lt_card.mp hTwo
    have hQE : Q ⊆ E := (Finset.mem_filter.mp hQ).2
    have hRE : R ⊆ E := (Finset.mem_filter.mp hR).2
    by_cases hSomeDisjoint : ∃ A ∈ S, ∃ C ∈ S, Disjoint A C
    · obtain ⟨A, hA, C, hC, hAC⟩ := hSomeDisjoint
      have hAE : A ⊆ E := (Finset.mem_filter.mp hA).2
      have hCE : C ⊆ E := (Finset.mem_filter.mp hC).2
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨A, (Finset.mem_filter.mp hA).1, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨C, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hC).1, hAC⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hEB, Finset.union_subset hAE hCE⟩
    · have hAllIntersect : ∀ A ∈ S, ∀ C ∈ S, ¬ Disjoint A C := by
        intro A hA C hC hDisj
        exact hSomeDisjoint ⟨A, hA, C, hC, hDisj⟩
      have hEfiltered : E ∈ noDisjointBadPairEdges B Bad₂ := by
        apply mem_noDisjointBadPairEdges.mpr
        refine ⟨hEB, ?_⟩
        intro A hA hAE C hC hCE
        exact hAllIntersect A (Finset.mem_filter.mpr ⟨hA, hAE⟩)
          C (Finset.mem_filter.mpr ⟨hC, hCE⟩)
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨Q, (Finset.mem_filter.mp hQ).1, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨R, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hR).1, ⟨hQR, hAllIntersect Q hQ R hR⟩⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hEfiltered, Finset.union_subset hQE hRE⟩

/-- Deletion budget for the filtered three strata. The intersecting-pair
fiber hypothesis is required only on the no-disjoint-pair subfamily. -/
theorem bad_pair_edges_filtered_deletion_bound
    {B Bad₂ : Family α} {C₁ C₂ C₃ : ℕ}
    (hUnique : ∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤ C₁)
    (hDisjoint : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₂)
    (hIntersectFiltered : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, P ≠ Q →
      ¬ Disjoint P Q →
      ((noDisjointBadPairEdges B Bad₂).filter
        fun E => P ∪ Q ⊆ E).card ≤ C₃) :
    (badPairEdges B Bad₂).card ≤
      Bad₂.card * C₁ + Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card * C₃) := by
  classical
  have hU : (uniqueBadPairEdges B Bad₂).card ≤ Bad₂.card * C₁ := by
    unfold uniqueBadPairEdges
    exact Finset.card_biUnion_le_card_mul Bad₂ _ C₁ hUnique
  have hD : (twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q)).card ≤
      Bad₂.card * (Bad₂.card * C₂) := by
    unfold twoBadPairEdges
    apply Finset.card_biUnion_le_card_mul
    intro P hP
    have hInner := Finset.card_biUnion_le_card_mul
      (Bad₂.filter fun Q => Disjoint P Q)
      (fun Q => B.filter fun E => P ∪ Q ⊆ E) C₂ (by
        intro Q hQ
        exact hDisjoint P hP Q (Finset.mem_filter.mp hQ).1
          (Finset.mem_filter.mp hQ).2)
    exact hInner.trans (Nat.mul_le_mul_right C₂
      (Finset.card_le_card (Finset.filter_subset _ _)))
  have hI :
      (twoBadPairEdges (noDisjointBadPairEdges B Bad₂) Bad₂
        (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q)).card ≤
        Bad₂.card * (Bad₂.card * C₃) := by
    unfold twoBadPairEdges
    apply Finset.card_biUnion_le_card_mul
    intro P hP
    have hInner := Finset.card_biUnion_le_card_mul
      (Bad₂.filter fun Q => P ≠ Q ∧ ¬ Disjoint P Q)
      (fun Q => (noDisjointBadPairEdges B Bad₂).filter
        fun E => P ∪ Q ⊆ E) C₃ (by
        intro Q hQ
        exact hIntersectFiltered P hP Q (Finset.mem_filter.mp hQ).1
          (Finset.mem_filter.mp hQ).2.1 (Finset.mem_filter.mp hQ).2.2)
    exact hInner.trans (Nat.mul_le_mul_right C₃
      (Finset.card_le_card (Finset.filter_subset _ _)))
  calc
    (badPairEdges B Bad₂).card ≤
        (uniqueBadPairEdges B Bad₂ ∪
          twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q) ∪
          twoBadPairEdges (noDisjointBadPairEdges B Bad₂) Bad₂
            (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q)).card :=
      Finset.card_le_card bad_pair_edges_covered_by_filtered_strata
    _ ≤ Bad₂.card * C₁ + Bad₂.card * (Bad₂.card * C₂) +
          Bad₂.card * (Bad₂.card * C₃) := by
      have hUnion := Finset.card_union_le
        (uniqueBadPairEdges B Bad₂)
        (twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q))
      have hUnion' := Finset.card_union_le
        (uniqueBadPairEdges B Bad₂ ∪
          twoBadPairEdges B Bad₂ (fun P Q => Disjoint P Q))
        (twoBadPairEdges (noDisjointBadPairEdges B Bad₂) Bad₂
          (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q))
      omega

/-- Aggregate deletion budget for all intersecting bad-pair witnesses in the
filtered no-disjoint-pair edge family, with the actual §IV.2.1 tail-packing
constant. -/
theorem intersecting_bad_pair_edges_actual_deletion_bound
    {H B Bad₂ : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hOrdinary : ∀ E ∈ B, E ⊆ W \ badSingletonVertices H W v r)
    (hvW : v ∉ W)
    (hBad₂ : Bad₂ = badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3))) :
    (twoBadPairEdges (noDisjointBadPairEdges B Bad₂) Bad₂
      (fun P Q => P ≠ Q ∧ ¬ Disjoint P Q)).card ≤
      Bad₂.card * (Bad₂.card *
        (if 3 ≤ r - 3 then W.card.choose (r - 3 - 3 + 1) else 1)) := by
  classical
  let C := if 3 ≤ r - 3 then W.card.choose (r - 3 - 3 + 1) else 1
  have hFiber : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂,
      P ≠ Q → ¬ Disjoint P Q →
      ((noDisjointBadPairEdges B Bad₂).filter
        fun E => P ∪ Q ⊆ E).card ≤ C := by
    intro P hP Q hQ hPQ hNotDisj
    simpa [C] using intersecting_bad_pair_root_tail_packing_bound
      hH hBH hBuniform hW hOrdinary hvW hBad₂ hP hQ hPQ hNotDisj
  unfold twoBadPairEdges
  apply Finset.card_biUnion_le_card_mul
  intro P hP
  have hInner := Finset.card_biUnion_le_card_mul
    (Bad₂.filter fun Q => P ≠ Q ∧ ¬ Disjoint P Q)
    (fun Q => (noDisjointBadPairEdges B Bad₂).filter
      fun E => P ∪ Q ⊆ E) C (by
      intro Q hQ
      exact hFiber P hP Q (Finset.mem_filter.mp hQ).1
        (Finset.mem_filter.mp hQ).2.1 (Finset.mem_filter.mp hQ).2.2)
  exact hInner.trans (Nat.mul_le_mul_right C
    (Finset.card_le_card (Finset.filter_subset _ _)))

/-- Full bad-pair deletion budget when the unique-pair and disjoint-pair
fiber estimates are supplied and the intersecting-pair estimate is discharged
from the actual filtered geometry. -/
theorem bad_pair_edges_actual_filtered_deletion_bound
    {H B Bad₂ : Family α} {W : Edge α} {v : α} {r C₁ C₂ : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H) (hBuniform : Uniform r B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hOrdinary : ∀ E ∈ B, E ⊆ W \ badSingletonVertices H W v r)
    (hvW : v ∉ W)
    (hBad₂ : Bad₂ = badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3)))
    (hUnique : ∀ P ∈ Bad₂,
      (B.filter fun E =>
        P ⊆ E ∧ (Bad₂.filter fun Q => Q ⊆ E).card = 1).card ≤ C₁)
    (hDisjoint : ∀ P ∈ Bad₂, ∀ Q ∈ Bad₂, Disjoint P Q →
      (B.filter fun E => P ∪ Q ⊆ E).card ≤ C₂) :
    (badPairEdges B Bad₂).card ≤
      Bad₂.card * C₁ + Bad₂.card * (Bad₂.card * C₂) +
        Bad₂.card * (Bad₂.card *
          (if 3 ≤ r - 3 then W.card.choose (r - 3 - 3 + 1) else 1)) := by
  apply bad_pair_edges_filtered_deletion_bound hUnique hDisjoint
  intro P hP Q hQ hPQ hNotDisj
  exact intersecting_bad_pair_root_tail_packing_bound
    hH hBH hBuniform hW hOrdinary hvW hBad₂ hP hQ hPQ hNotDisj

end JSP523
