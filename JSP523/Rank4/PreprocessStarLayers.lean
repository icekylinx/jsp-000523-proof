import JSP523.Rank4.CommonTripleCells
import JSP523.Rank4.PreprocessSmallCells
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pair-owner cleaning for finitely many rank-four star links

This isolates the finite combinatorial step in §III.A.2.  Each pair root is
assigned to an index of maximum link degree.  We retain a triple only when
all its pair roots are owned by its link; hence surviving pair shadows are
disjoint.  Every deleted triple is charged to at least one nonowner pair
incidence, giving the exact finite loss bound.
-/

namespace JSP523.Rank4

variable {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- The number of triples in link `i` containing pair root `P`. -/
def starLinkPairDegree (L : ι → Family α) (i : ι) (P : Edge α) : ℕ :=
  ((L i).filter fun T => P ⊆ T).card

/-- At one pair root, the square of the total nonowner degree is bounded by
the ordered cross products of distinct links. Diagonal nonowner terms are
charged to the owner/nonowner products using maximality. -/
theorem nonowner_degree_sum_sq_le_ordered_pair_products
    (d : ι → ℕ) (owner : ι)
    (hMax : ∀ i, d i ≤ d owner) :
    (∑ i ∈ (Finset.univ.erase owner), d i) ^ 2 ≤
      ∑ i : ι, ∑ j ∈ (Finset.univ.erase i), d i * d j := by
  classical
  let s := ∑ i ∈ (Finset.univ.erase owner), d i
  let total := ∑ i : ι, d i
  let diagonal := ∑ i : ι, d i ^ 2
  let cross := ∑ i : ι, ∑ j ∈ (Finset.univ.erase i), d i * d j
  have hTotal : total = d owner + s := by
    dsimp [total, s]
    exact (Finset.add_sum_erase Finset.univ d (Finset.mem_univ owner)).symm
  have hDiag : diagonal ≤ d owner * total := by
    dsimp [diagonal, total]
    calc
      (∑ i : ι, d i ^ 2) ≤ ∑ i : ι, d i * d owner := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [pow_two] using Nat.mul_le_mul_left (d i) (hMax i)
      _ = (∑ i : ι, d i) * d owner := by rw [Finset.sum_mul]
      _ = d owner * ∑ i : ι, d i := Nat.mul_comm _ _
  have hSquareExpansion : total ^ 2 = diagonal + cross := by
    dsimp [total, diagonal, cross]
    rw [pow_two, Finset.sum_mul_sum]
    calc
      (∑ i : ι, ∑ j : ι, d i * d j) =
          ∑ i : ι, (d i * d i +
            ∑ j ∈ (Finset.univ.erase i), d i * d j) := by
        apply Finset.sum_congr rfl
        intro i hi
        symm
        exact Finset.add_sum_erase Finset.univ (fun j => d i * d j)
          (Finset.mem_univ i)
      _ = (∑ i : ι, d i ^ 2) +
          ∑ i : ι, ∑ j ∈ (Finset.univ.erase i), d i * d j := by
        rw [Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp [pow_two]
  have hSmall : s ^ 2 + diagonal ≤ total ^ 2 := by
    rw [hTotal]
    nlinarith [hDiag]
  have hCompare : s ^ 2 + diagonal ≤ diagonal + cross := by
    calc
      s ^ 2 + diagonal ≤ total ^ 2 := hSmall
      _ = diagonal + cross := hSquareExpansion
  have hCompare' :
      (∑ i ∈ Finset.univ.erase owner, d i) ^ 2 + diagonal ≤
        diagonal +
          ∑ i : ι, ∑ j ∈ Finset.univ.erase i, d i * d j := by
    simpa [s, cross] using hCompare
  have hResult :
      (∑ i ∈ Finset.univ.erase owner, d i) ^ 2 ≤
        ∑ i : ι, ∑ j ∈ Finset.univ.erase i, d i * d j := by
    omega
  exact hResult

/-- Choose an index of maximum pair degree.  The finite maximum is realized
by `Finset.exists_max_image`; ties are resolved by its finite choice. -/
noncomputable def maximumDegreePairOwner (L : ι → Family α) [Nonempty ι]
    (P : Edge α) : ι :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun i => starLinkPairDegree L i P) Finset.univ_nonempty)

omit [DecidableEq ι] in
theorem maximumDegreePairOwner_spec (L : ι → Family α) [Nonempty ι]
    (P : Edge α) (i : ι) :
    starLinkPairDegree L i P ≤
      starLinkPairDegree L (maximumDegreePairOwner L P) P := by
  have h := Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun i => starLinkPairDegree L i P) Finset.univ_nonempty)
  exact h.2 i (Finset.mem_univ i)

/-- A triple survives in link `i` when every pair inside it is owned by `i`. -/
def pairOwnerCleanedLink (L : ι → Family α) (owner : Edge α → ι)
    (i : ι) : Family α :=
  (L i).filter fun T => ∀ P ∈ T.powersetCard 2, owner P = i

/-- Pair shadow of a link, restricted to the specified finite ground set. -/
def starLinkPairShadow (L : ι → Family α) (V : Edge α) (i : ι) : Family α :=
  (V.powersetCard 2).filter fun P => ∃ T ∈ L i, P ⊆ T

/-- The nonowner incidences that can pay for deletions in link `i`. -/
def nonownerPairIncidences (L : ι → Family α) (owner : Edge α → ι)
    (V : Edge α) (i : ι) : Family α :=
  (V.powersetCard 2).biUnion fun P =>
    if owner P ≠ i then (L i).filter fun T => P ⊆ T else ∅

omit [Fintype ι] in
/-- Every deleted 3-set contains a pair owned by a different link. -/
theorem deleted_star_link_subset_nonowner_incidence
    (L : ι → Family α) (owner : Edge α → ι) (V : Edge α) (i : ι)
    (hGround : ∀ T ∈ L i, T ∈ V.powersetCard 3) :
    L i \ pairOwnerCleanedLink L owner i ⊆
      nonownerPairIncidences L owner V i := by
  classical
  intro T hT
  have hTL : T ∈ L i := (Finset.mem_sdiff.mp hT).1
  have hNotClean : T ∉ pairOwnerCleanedLink L owner i :=
    (Finset.mem_sdiff.mp hT).2
  have hNotAll : ¬ ∀ P ∈ T.powersetCard 2, owner P = i := by
    intro hAll
    exact hNotClean (Finset.mem_filter.mpr ⟨hTL, hAll⟩)
  push Not at hNotAll
  obtain ⟨P, hPTwo, hOwner⟩ := hNotAll
  have hPTwo' := Finset.mem_powersetCard.mp hPTwo
  have hTGround := Finset.mem_powersetCard.mp (hGround T hTL)
  have hPmem : P ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨hPTwo'.1.trans hTGround.1, hPTwo'.2⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨P, hPmem, ?_⟩
  simp only [hOwner, ne_eq, not_false_eq_true, ↓reduceIte,
    Finset.mem_filter]
  exact ⟨hTL, hPTwo'.1⟩

omit [Fintype ι] in
theorem nonownerPairIncidences_card_le
    (L : ι → Family α) (owner : Edge α → ι) (V : Edge α) (i : ι) :
    (nonownerPairIncidences L owner V i).card ≤
      ∑ P ∈ V.powersetCard 2,
        if owner P ≠ i then starLinkPairDegree L i P else 0 := by
  classical
  unfold nonownerPairIncidences
  calc
    _ ≤ ∑ P ∈ V.powersetCard 2,
        (if owner P ≠ i then ((L i).filter fun T => P ⊆ T) else ∅).card :=
          Finset.card_biUnion_le
    _ = ∑ P ∈ V.powersetCard 2,
        if owner P ≠ i then starLinkPairDegree L i P else 0 := by
          apply Finset.sum_congr rfl
          intro P _
          by_cases hOwner : owner P ≠ i <;> simp [starLinkPairDegree, hOwner]

/-- The sum of deleted link sizes is at most the total number of nonowner
pair incidences.  This bound holds for any owner map; maximality is used
when selecting the owner so the bound is the smallest available one. -/
theorem pair_owner_cleaning_deletion_bound
    (L : ι → Family α) (owner : Edge α → ι) (V : Edge α)
    (hGround : ∀ i T, T ∈ L i → T ∈ V.powersetCard 3)
    (_hOwnerMax : ∀ P ∈ V.powersetCard 2, ∀ i,
      starLinkPairDegree L i P ≤ starLinkPairDegree L (owner P) P) :
    (∑ i : ι, (L i \ pairOwnerCleanedLink L owner i).card) ≤
      ∑ P ∈ V.powersetCard 2, ∑ i ∈ (Finset.univ : Finset ι),
        if owner P ≠ i then starLinkPairDegree L i P else 0 := by
  classical
  calc
    (∑ i : ι, (L i \ pairOwnerCleanedLink L owner i).card) ≤
        ∑ i : ι, (nonownerPairIncidences L owner V i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.card_le_card
        (deleted_star_link_subset_nonowner_incidence L owner V i (hGround i))
    _ ≤ ∑ i : ι, ∑ P ∈ V.powersetCard 2,
        (if owner P ≠ i then ((L i).filter fun T => P ⊆ T).card else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact nonownerPairIncidences_card_le L owner V i
    _ = ∑ P ∈ V.powersetCard 2, ∑ i ∈ (Finset.univ : Finset ι),
        if owner P ≠ i then starLinkPairDegree L i P else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro P _
      simp [starLinkPairDegree]

omit [Fintype ι] in
/-- Pair-owner cleaning makes the pair shadows of distinct surviving links
disjoint. -/
theorem pair_owner_cleaning_shadows_disjoint
    (L : ι → Family α) (owner : Edge α → ι) (V : Edge α)
    (i j : ι) (hij : i ≠ j) :
    Disjoint (starLinkPairShadow (pairOwnerCleanedLink L owner) V i)
      (starLinkPairShadow (pairOwnerCleanedLink L owner) V j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro P hPi hPj
  have hPii := Finset.mem_filter.mp hPi
  have hPjj := Finset.mem_filter.mp hPj
  obtain ⟨Ti, hTi, hPsubi⟩ := hPii.2
  obtain ⟨Tj, hTj, hPsubj⟩ := hPjj.2
  have hOwnI : owner P = i := by
    have h := Finset.mem_filter.mp hTi
    have hPc : P ∈ Ti.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hPsubi,
        (Finset.mem_powersetCard.mp hPii.1).2⟩
    exact h.2 P hPc
  have hOwnJ : owner P = j := by
    have h := Finset.mem_filter.mp hTj
    have hPc : P ∈ Tj.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hPsubj,
        (Finset.mem_powersetCard.mp hPjj.1).2⟩
    exact h.2 P hPc
  exact hij (hOwnI.symm.trans hOwnJ)

/-- The maximum degree owner map itself supplies the owner-maximality
premise of the deletion bound, so the result is a concrete finite theorem. -/
theorem maximum_pair_owner_cleaning_deletion_bound
    (L : ι → Family α) (V : Edge α) [Nonempty ι]
    (hGround : ∀ i T, T ∈ L i → T ∈ V.powersetCard 3) :
    (∑ i : ι,
      (L i \ pairOwnerCleanedLink L (maximumDegreePairOwner L) i).card) ≤
      ∑ P ∈ V.powersetCard 2, ∑ i ∈ (Finset.univ : Finset ι),
        if maximumDegreePairOwner L P ≠ i then
          starLinkPairDegree L i P else 0 := by
  apply pair_owner_cleaning_deletion_bound L (maximumDegreePairOwner L) V
    hGround
  intro P hP i
  exact maximumDegreePairOwner_spec L P i

/-- Cauchy-Schwarz turns the owner deletion bound into a squared bound by
the ordered pairwise cross moments of the link degrees. -/
theorem maximum_pair_owner_cleaning_loss_sq_le_cross_moment
    (L : ι → Family α) (owner : Edge α → ι) (V : Edge α) [Nonempty ι]
    (hGround : ∀ i T, T ∈ L i → T ∈ V.powersetCard 3)
    (hOwnerMax : ∀ P ∈ V.powersetCard 2, ∀ i,
      starLinkPairDegree L i P ≤ starLinkPairDegree L (owner P) P) :
    (∑ i : ι, (L i \ pairOwnerCleanedLink L owner i).card) ^ 2 ≤
      (V.powersetCard 2).card *
        ∑ P ∈ V.powersetCard 2, ∑ i : ι,
          ∑ j ∈ (Finset.univ.erase i),
            starLinkPairDegree L i P * starLinkPairDegree L j P := by
  classical
  let nonownerSum : Edge α → ℕ := fun P =>
    ∑ i ∈ (Finset.univ.erase (owner P)), starLinkPairDegree L i P
  have hNonownerAt (P : Edge α) :
      (∑ i : ι, if owner P ≠ i then starLinkPairDegree L i P else 0) =
        nonownerSum P := by
    calc
      _ = (if owner P ≠ owner P then starLinkPairDegree L (owner P) P else 0) +
          ∑ i ∈ (Finset.univ.erase (owner P)),
            (if owner P ≠ i then starLinkPairDegree L i P else 0) :=
          (Finset.add_sum_erase Finset.univ
            (fun i => if owner P ≠ i then starLinkPairDegree L i P else 0)
            (Finset.mem_univ (owner P))).symm
      _ = nonownerSum P := by
        have hHead :
            (if owner P ≠ owner P then starLinkPairDegree L (owner P) P else 0) = 0 := by
          simp
        have hTail :
            (∑ i ∈ Finset.univ.erase (owner P),
              (if owner P ≠ i then starLinkPairDegree L i P else 0)) =
              ∑ i ∈ Finset.univ.erase (owner P), starLinkPairDegree L i P := by
          apply Finset.sum_congr rfl
          intro i hi
          have hNe : owner P ≠ i := (Finset.mem_erase.mp hi).1.symm
          simp [hNe]
        rw [hHead, zero_add]
        simpa [nonownerSum] using hTail
  have hNonownerTotal :
      (∑ P ∈ V.powersetCard 2,
        ∑ i : ι, if owner P ≠ i then starLinkPairDegree L i P else 0) =
      ∑ P ∈ V.powersetCard 2, nonownerSum P := by
    apply Finset.sum_congr rfl
    intro P hP
    exact hNonownerAt P
  have hLoss := pair_owner_cleaning_deletion_bound L owner V hGround hOwnerMax
  rw [hNonownerTotal] at hLoss
  have hCauchy :
      (∑ P ∈ V.powersetCard 2, nonownerSum P) ^ 2 ≤
        (V.powersetCard 2).card *
          ∑ P ∈ V.powersetCard 2, nonownerSum P ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (V.powersetCard 2) nonownerSum (fun _ => 1)
    simpa [Finset.sum_const, mul_comm] using h
  have hSquares :
      (∑ P ∈ V.powersetCard 2, nonownerSum P ^ 2) ≤
        ∑ P ∈ V.powersetCard 2, ∑ i : ι,
          ∑ j ∈ (Finset.univ.erase i),
            starLinkPairDegree L i P * starLinkPairDegree L j P := by
    apply Finset.sum_le_sum
    intro P hP
    exact nonowner_degree_sum_sq_le_ordered_pair_products
      (fun i => starLinkPairDegree L i P) (owner P)
      (fun i => hOwnerMax P hP i)
  calc
    (∑ i : ι, (L i \ pairOwnerCleanedLink L owner i).card) ^ 2 ≤
        (∑ P ∈ V.powersetCard 2, nonownerSum P) ^ 2 :=
          by simpa [pow_two] using Nat.mul_le_mul hLoss hLoss
    _ ≤ (V.powersetCard 2).card *
        ∑ P ∈ V.powersetCard 2, nonownerSum P ^ 2 := hCauchy
    _ ≤ (V.powersetCard 2).card *
        ∑ P ∈ V.powersetCard 2, ∑ i : ι,
          ∑ j ∈ (Finset.univ.erase i),
            starLinkPairDegree L i P * starLinkPairDegree L j P :=
          Nat.mul_le_mul_left _ hSquares

/-- If every ordered pair of distinct links has cross moment at most `B`,
the pair-owner cleaning loss has the following explicit squared bound. -/
theorem maximum_pair_owner_cleaning_loss_sq_le_uniform_pair_moment
    (L : ι → Family α) (owner : Edge α → ι) (V : Edge α) [Nonempty ι]
    (hGround : ∀ i T, T ∈ L i → T ∈ V.powersetCard 3)
    (hOwnerMax : ∀ P ∈ V.powersetCard 2, ∀ i,
      starLinkPairDegree L i P ≤ starLinkPairDegree L (owner P) P)
    (B : ℕ)
    (hMoment : ∀ i j, i ≠ j →
      (∑ P ∈ V.powersetCard 2,
        starLinkPairDegree L i P * starLinkPairDegree L j P) ≤ B) :
    (∑ i : ι, (L i \ pairOwnerCleanedLink L owner i).card) ^ 2 ≤
      (V.powersetCard 2).card *
        ((Fintype.card ι * (Fintype.card ι - 1)) * B) := by
  classical
  have hSquare := maximum_pair_owner_cleaning_loss_sq_le_cross_moment
    L owner V hGround hOwnerMax
  have hAllMoments :
      (∑ P ∈ V.powersetCard 2, ∑ i : ι,
        ∑ j ∈ Finset.univ.erase i,
          starLinkPairDegree L i P * starLinkPairDegree L j P) ≤
        (Fintype.card ι * (Fintype.card ι - 1)) * B := by
    calc
      _ = ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
          ∑ P ∈ V.powersetCard 2,
            starLinkPairDegree L i P * starLinkPairDegree L j P := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_comm]
      _ ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i, B := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            exact hMoment i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = (Fintype.card ι * (Fintype.card ι - 1)) * B := by
            simp [Finset.sum_const, Finset.card_erase_of_mem, Nat.mul_assoc]
  exact hSquare.trans (Nat.mul_le_mul_left _ hAllMoments)

/-- Weak-cell clearing followed by the actual common-cell theorem gives a
finite unique label on every surviving nonempty pair cell, with the explicit
deletion cost from §III.A.6. -/
theorem clear_small_cells_and_get_unique_labels
    {H : Family α} (V : Edge α) (t D : ℕ)
    (hH : Admissible H)
    (hCap : ∀ T : Edge α, T.card = 3 →
      (facetCompletions H V T).card ≤ D)
    (hLarge : 9 * D < t) :
    ∃ K : Family α,
      K ⊆ H ∧
      (H \ K).card ≤ 2 * (t - 1) * V.card.choose 2 ∧
      (∀ P ∈ V.powersetCard 2,
        (commonRootCell K V P).card = 0 ∨
          ∃! z : α, ∀ ⦃T : Edge α⦄,
            T ∈ commonRootCell K V P → z ∈ T) := by
  classical
  obtain ⟨K, hKH, hCells, hLoss⟩ := clear_all_small_commonCells H V t
  refine ⟨K, hKH, hLoss, ?_⟩
  have hKAdmissible : Admissible K := admissible_mono hKH hH
  have hCapK : ∀ T : Edge α, T.card = 3 →
      (facetCompletions K V T).card ≤ D := by
    intro T hT
    have hSub : facetCompletions K V T ⊆ facetCompletions H V T := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx'.1, hKH hx'.2⟩
    exact (Finset.card_le_card hSub).trans (hCap T hT)
  intro P hP
  rcases hCells P hP with hZero | hBig
  · exact Or.inl hZero
  · have hPcard : P.card = 2 :=
      (Finset.mem_powersetCard.mp hP).2
    let ab := pairRootRep P hPcard
    have hRootEq : commonRootCell K V P =
        commonTripleCell K V ab.1 ab.2 := by
      simp [commonRootCell, hPcard, ab]
    have hCellBig : 9 * D <
        (commonTripleCell K V ab.1 ab.2).card := by
      rw [← hRootEq]
      omega
    have hab : ab.1 ≠ ab.2 := (pairRootRep_spec P hPcard).1
    obtain ⟨z, hz⟩ :=
      commonTripleCell_large_has_center_of_facet_cap
        hKAdmissible hab hCapK hCellBig
    have hPairCap : ∀ Q : Edge α, Q.card = 2 →
        triplePairDegree (commonTripleCell K V ab.1 ab.2) Q ≤ D :=
      commonTripleCell_pairDegree_le_of_facet_cap hCapK
    refine Or.inr ⟨z, ?_, ?_⟩
    · intro T hT
      rw [hRootEq] at hT
      exact hz hT
    · intro y hy
      have hy' : ∀ ⦃T : Edge α⦄,
          T ∈ commonTripleCell K V ab.1 ab.2 → y ∈ T := by
        intro T hT
        exact hy (hRootEq.symm ▸ hT)
      exact (commonTripleCell_center_unique hPairCap
        (by omega : D < (commonTripleCell K V ab.1 ab.2).card)
        hz hy').symm

end JSP523.Rank4
