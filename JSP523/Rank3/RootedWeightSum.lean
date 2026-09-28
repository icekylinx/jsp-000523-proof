import JSP523.Rank3.ChargeTransfer
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Summing actual signed weights over graph links

This file develops the finite graph sum exchange behind equation (II.4) of the
all-rank manuscript. The source graph is the actual link at each root.
-/

namespace JSP523.Rank3

section RootedWeightSum

variable {α : Type*} [DecidableEq α]

private theorem graph_neighbor_sum_swap
    (U : Finset α) (N : α → Finset α)
    (hN : ∀ x ∈ U, N x ⊆ U)
    (hSym : ∀ x ∈ U, ∀ y ∈ U, y ∈ N x ↔ x ∈ N y)
    (g : α → α → ℚ) :
    (∑ x ∈ U, ∑ y ∈ N x, g x y) =
      ∑ x ∈ U, ∑ y ∈ N x, g y x := by
  have hExpand (f : α → α → ℚ) :
      (∑ x ∈ U, ∑ y ∈ N x, f x y) =
        ∑ x ∈ U, ∑ y ∈ U,
          if y ∈ N x then f x y else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hFilter : U.filter (fun y => y ∈ N x) = N x := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨hN x hx h, h⟩
    calc
      (∑ y ∈ N x, f x y) =
          ∑ y ∈ U.filter (fun y => y ∈ N x), f x y := by rw [hFilter]
      _ = ∑ y ∈ U, if y ∈ N x then f x y else 0 := by
        simp only [Finset.sum_filter]
  rw [hExpand g, hExpand (fun x y => g y x)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [(hSym x hx y hy)]

/-- Double-count length-two walks by their middle vertex and by their
    ordered pair of endpoints. -/
private theorem graph_wedge_sum
    (U : Finset α) (N : α → Finset α)
    (hN : ∀ x ∈ U, N x ⊆ U)
    (hSym : ∀ x ∈ U, ∀ y ∈ U, y ∈ N x ↔ x ∈ N y) :
    (∑ x ∈ U, ∑ y ∈ N x,
      ∑ u ∈ (N y).erase x,
        weightFraction (N x ∩ N u).card) =
      ∑ x ∈ U, ∑ u ∈ U.erase x,
        linkSurplus (N x ∩ N u).card := by
  apply Finset.sum_congr rfl
  intro x hx
  have hInner (y : α) (hy : y ∈ N x) :
      (∑ u ∈ (N y).erase x,
        weightFraction (N x ∩ N u).card) =
        ∑ u ∈ U.erase x,
          if u ∈ N y then weightFraction (N x ∩ N u).card else 0 := by
    have hyU : y ∈ U := hN x hx hy
    have hFilter : (U.erase x).filter (fun u => u ∈ N y) =
        (N y).erase x := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hux, _⟩, huN⟩
        exact ⟨hux, huN⟩
      · rintro ⟨hux, huN⟩
        exact ⟨⟨hux, hN y hyU huN⟩, huN⟩
    calc
      (∑ u ∈ (N y).erase x,
          weightFraction (N x ∩ N u).card) =
          ∑ u ∈ (U.erase x).filter (fun u => u ∈ N y),
            weightFraction (N x ∩ N u).card := by rw [hFilter]
      _ = ∑ u ∈ U.erase x,
            if u ∈ N y then weightFraction (N x ∩ N u).card else 0 := by
          simp only [Finset.sum_filter]
  calc
    (∑ y ∈ N x,
      ∑ u ∈ (N y).erase x,
        weightFraction (N x ∩ N u).card) =
        ∑ y ∈ N x, ∑ u ∈ U.erase x,
          if u ∈ N y then weightFraction (N x ∩ N u).card else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hInner y hy
    _ = ∑ u ∈ U.erase x, ∑ y ∈ N x,
          if u ∈ N y then weightFraction (N x ∩ N u).card else 0 :=
      Finset.sum_comm
    _ = ∑ u ∈ U.erase x,
          linkSurplus (N x ∩ N u).card := by
      apply Finset.sum_congr rfl
      intro u hu
      have huU : u ∈ U := (Finset.mem_erase.mp hu).2
      have hSymInner :
          (∑ y ∈ N x,
            if u ∈ N y then weightFraction (N x ∩ N u).card else 0) =
          ∑ y ∈ N x,
            if y ∈ N u then weightFraction (N x ∩ N u).card else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyU : y ∈ U := hN x hx hy
        simp only [(hSym y hyU u huU)]
      rw [hSymInner]
      have hFilter : (N x).filter (fun y => y ∈ N u) = N x ∩ N u := by
        ext y
        simp
      calc
        (∑ y ∈ N x,
            if y ∈ N u then weightFraction (N x ∩ N u).card else 0) =
            ∑ y ∈ N x ∩ N u,
              weightFraction (N x ∩ N u).card := by
          rw [← hFilter]
          simp only [Finset.sum_filter]
        _ = linkSurplus (N x ∩ N u).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact card_mul_weight_fraction_eq_link_surplus _

/-- The signed weight summed over both orientations of every link edge
    at one root. -/
def rootedOrientedWeightTotal
    (H : Family α) (V : Edge α) (z : α) : ℚ :=
  ∑ x ∈ V.erase z,
    ∑ y ∈ rootNeighbors H V z x,
      rootedSignedWeight H V z x y

/-- For a fixed root, summing signed weights over oriented link edges gives
    twice the ordered-pair common-neighbor surplus minus twice the pair
    budget around that root.  This is the oriented form of the manuscript's
    root-link summation immediately before equation (II.4). -/
theorem rooted_oriented_weight_sum
    (H : Family α) (V : Edge α) (z : α) :
    rootedOrientedWeightTotal H V z =
      2 * (∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
        linkSurplus (rootCommonNeighbors H V z x u).card) -
      2 * (∑ x ∈ V.erase z,
        pairBudget (rootNeighbors H V z x).card) := by
  let U := V.erase z
  let N : α → Edge α := fun x => rootNeighbors H V z x
  have hN : ∀ x ∈ U, N x ⊆ U := by
    intro x hx y hy
    apply Finset.mem_erase.mpr
    constructor
    · intro hyz
      subst y
      exact root_neighbors_not_root H V z x hy
    · exact root_neighbors_subset_ground H V z x hy
  have hSym : ∀ x ∈ U, ∀ y ∈ U, y ∈ N x ↔ x ∈ N y := by
    intro x hx y hy
    constructor
    · exact root_neighbors_mem_symm H V
        (Finset.mem_erase.mp hx).2
        (Ne.symm (Finset.mem_erase.mp hx).1)
    · exact root_neighbors_mem_symm H V
        (Finset.mem_erase.mp hy).2
        (Ne.symm (Finset.mem_erase.mp hy).1)
  let A : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    ∑ u ∈ (N y).erase x,
      weightFraction (rootCommonNeighbors H V z x u).card
  let B : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    ∑ u ∈ (N x).erase y,
      weightFraction (rootCommonNeighbors H V z y u).card
  let C : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    weightPairBudget (N x).card
  let D : ℚ := ∑ x ∈ U, ∑ y ∈ N x,
    weightPairBudget (N y).card
  have hB : B = A := by
    exact graph_neighbor_sum_swap U N hN hSym
      (fun x y => ∑ u ∈ (N x).erase y,
        weightFraction (rootCommonNeighbors H V z y u).card)
  have hD : D = C := by
    exact graph_neighbor_sum_swap U N hN hSym
      (fun x y => weightPairBudget (N y).card)
  have hC : C = ∑ x ∈ U, pairBudget (N x).card := by
    dsimp [C]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_const, nsmul_eq_mul]
    exact card_mul_weight_pair_budget_eq_pair_budget _
  have hA : A = ∑ x ∈ U, ∑ u ∈ U.erase x,
      linkSurplus (rootCommonNeighbors H V z x u).card := by
    have hWedge := graph_wedge_sum U N hN hSym
    dsimp [A, N] at hWedge ⊢
    calc
      (∑ x ∈ U, ∑ y ∈ rootNeighbors H V z x,
        ∑ u ∈ (rootNeighbors H V z y).erase x,
          weightFraction (rootCommonNeighbors H V z x u).card) =
          ∑ x ∈ U, ∑ y ∈ rootNeighbors H V z x,
            ∑ u ∈ (rootNeighbors H V z y).erase x,
              weightFraction
                (rootNeighbors H V z x ∩ rootNeighbors H V z u).card := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.sum_congr rfl
          intro u hu
          rw [root_common_neighbors_eq_inter_root_neighbors]
      _ = ∑ x ∈ U, ∑ u ∈ U.erase x,
            linkSurplus
              (rootNeighbors H V z x ∩ rootNeighbors H V z u).card :=
          hWedge
      _ = ∑ x ∈ U, ∑ u ∈ U.erase x,
            linkSurplus (rootCommonNeighbors H V z x u).card := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro u hu
          rw [root_common_neighbors_eq_inter_root_neighbors]
  have hExpand : rootedOrientedWeightTotal H V z = A + B - C - D := by
    simp only [rootedOrientedWeightTotal, rootedSignedWeight,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    dsimp [A, B, C, D, U, N]
  rw [hExpand, hB, hD, hC, hA]
  ring

/-- Reindex the finite sum over three distinct vertices so the cell pair
    appears outside the root. -/
private theorem distinct_triple_sum_swap
    (V : Finset α) (f : α → α → α → ℚ) :
    (∑ z ∈ V, ∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
      f z x u) =
      ∑ x ∈ V, ∑ u ∈ V.erase x,
        ∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
          f z x u := by
  calc
    (∑ z ∈ V, ∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
        f z x u) =
        ∑ x ∈ V, ∑ z ∈ V.erase x, ∑ u ∈ (V.erase z).erase x,
          f z x u := by
      apply Finset.sum_comm'
      intro z x
      constructor
      · rintro ⟨hz, hx⟩
        have h := Finset.mem_erase.mp hx
        exact ⟨Finset.mem_erase.mpr ⟨Ne.symm h.1, hz⟩, h.2⟩
      · rintro ⟨hz, hx⟩
        have h := Finset.mem_erase.mp hz
        exact ⟨h.2, Finset.mem_erase.mpr ⟨Ne.symm h.1, hx⟩⟩
    _ = ∑ x ∈ V, ∑ u ∈ V.erase x,
          ∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
            f z x u := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_comm'
      intro z u
      constructor
      · rintro ⟨hz, hu⟩
        obtain ⟨hzNeX, hzV⟩ := Finset.mem_erase.mp hz
        obtain ⟨huNeX, huEraseZ⟩ := Finset.mem_erase.mp hu
        obtain ⟨huNeZ, huV⟩ := Finset.mem_erase.mp huEraseZ
        exact ⟨Finset.mem_filter.mpr
          ⟨hzV, hzNeX, Ne.symm huNeZ⟩,
          Finset.mem_erase.mpr ⟨huNeX, huV⟩⟩
      · rintro ⟨hz, hu⟩
        obtain ⟨hzV, hzNeX, hzNeU⟩ := Finset.mem_filter.mp hz
        obtain ⟨huNeX, huV⟩ := Finset.mem_erase.mp hu
        exact ⟨Finset.mem_erase.mpr ⟨hzNeX, hzV⟩,
          Finset.mem_erase.mpr
            ⟨huNeX, Finset.mem_erase.mpr ⟨Ne.symm hzNeU, huV⟩⟩⟩

/-- Every unordered pair occurs in the ordered distinct-pair sum twice. -/
theorem ordered_pair_sum_eq_twice_unordered
    (V : Edge α) (F : Edge α → ℚ) :
    (∑ x ∈ V, ∑ u ∈ V.erase x, F ({x, u} : Edge α)) =
      2 * (∑ p ∈ V.powersetCard 2, F p) := by
  let P := V.powersetCard 2
  have hInner (x : α) (hx : x ∈ V) :
      (∑ u ∈ V.erase x, F ({x, u} : Edge α)) =
        ∑ p ∈ P.filter (fun p => x ∈ p), F p := by
    apply Finset.sum_bij (fun u _ => ({x, u} : Edge α))
    · intro u hu
      obtain ⟨hux, huV⟩ := Finset.mem_erase.mp hu
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro t ht
          rcases Finset.mem_insert.mp ht with htx | htu
          · exact htx ▸ hx
          · exact (Finset.mem_singleton.mp htu) ▸ huV
        · exact Finset.card_pair (Ne.symm hux)
      · simp
    · intro u hu v hv heq
      have hux : u ≠ x := (Finset.mem_erase.mp hu).1
      have huMem : u ∈ ({x, u} : Edge α) := by simp
      have huOther : u ∈ ({x, v} : Edge α) := heq ▸ huMem
      rcases Finset.mem_insert.mp huOther with hux' | huv
      · exact False.elim (hux hux')
      · exact Finset.mem_singleton.mp huv
    · intro p hp
      obtain ⟨hpP, hxP⟩ := Finset.mem_filter.mp hp
      have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpP).2
      have hmore : (p.erase x).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one hxP
        omega
      obtain ⟨u, huErase⟩ := hmore
      have hux : u ≠ x := (Finset.mem_erase.mp huErase).1
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpP).1 huP
      have heq : ({x, u} : Edge α) = p := by
        apply Finset.eq_of_subset_of_card_le
        · intro t ht
          rcases Finset.mem_insert.mp ht with htx | htu
          · exact htx ▸ hxP
          · exact (Finset.mem_singleton.mp htu) ▸ huP
        · rw [Finset.card_pair (Ne.symm hux), hp2]
      exact ⟨u, Finset.mem_erase.mpr ⟨hux, huV⟩, heq⟩
    · intro u hu
      rfl
  calc
    (∑ x ∈ V, ∑ u ∈ V.erase x, F ({x, u} : Edge α)) =
        ∑ x ∈ V, ∑ p ∈ P.filter (fun p => x ∈ p), F p := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hInner x hx
    _ = ∑ p ∈ P, ∑ x ∈ p, F p := by
      apply Finset.sum_comm'
      intro x p
      constructor
      · rintro ⟨hxV, hp⟩
        exact ⟨(Finset.mem_filter.mp hp).2,
          (Finset.mem_filter.mp hp).1⟩
      · rintro ⟨hxP, hpP⟩
        have hxV : x ∈ V := (Finset.mem_powersetCard.mp hpP).1 hxP
        exact ⟨hxV, Finset.mem_filter.mpr ⟨hpP, hxP⟩⟩
    _ = 2 * (∑ p ∈ P, F p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const, nsmul_eq_mul]
      have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
      rw [hp2]
      norm_num

/-- The all-roots signed-weight identity in ordered-pair form.  The first
    inner sum is the actual common-link surplus at each ambient cell; the
    second is the actual completion-pair budget at each ambient pair. -/
theorem all_roots_oriented_weight_sum
    {H : Family α} (V : Edge α) (hH : Admissible H) :
    (∑ z ∈ V, rootedOrientedWeightTotal H V z) =
      2 * (∑ x ∈ V, ∑ u ∈ V.erase x,
        linkSurplus (commonLink H V ({x, u} : Edge α)).card) -
      2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
        pairBudget (rootNeighbors H V z x).card) := by
  have hSum := distinct_triple_sum_swap V
    (fun z x u => linkSurplus (rootCommonNeighbors H V z x u).card)
  calc
    (∑ z ∈ V, rootedOrientedWeightTotal H V z) =
        ∑ z ∈ V,
          (2 * (∑ x ∈ V.erase z, ∑ u ∈ (V.erase z).erase x,
            linkSurplus (rootCommonNeighbors H V z x u).card) -
           2 * (∑ x ∈ V.erase z,
             pairBudget (rootNeighbors H V z x).card)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact rooted_oriented_weight_sum H V z
    _ = 2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            ∑ u ∈ (V.erase z).erase x,
              linkSurplus (rootCommonNeighbors H V z x u).card) -
          2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            pairBudget (rootNeighbors H V z x).card) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ x ∈ V, ∑ u ∈ V.erase x,
            ∑ z ∈ V.filter (fun z => z ≠ x ∧ z ≠ u),
              linkSurplus (rootCommonNeighbors H V z x u).card) -
          2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            pairBudget (rootNeighbors H V z x).card) := by rw [hSum]
    _ = 2 * (∑ x ∈ V, ∑ u ∈ V.erase x,
            linkSurplus (commonLink H V ({x, u} : Edge α)).card) -
          2 * (∑ z ∈ V, ∑ x ∈ V.erase z,
            pairBudget (rootNeighbors H V z x).card) := by
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro u hu
      have huV : u ∈ V := (Finset.mem_erase.mp hu).2
      have hxu : x ≠ u := Ne.symm (Finset.mem_erase.mp hu).1
      exact sum_root_link_surplus_eq_link_surplus hH hx huV hxu

/-- An ambient cell outside the actual support has zero link surplus. -/
private theorem all_pair_link_surplus_eq_actual_link_surplus
    (H : Family α) (V : Edge α) :
    (∑ q ∈ V.powersetCard 2,
      linkSurplus (commonLink H V q).card) =
      actualLinkSurplus H V := by
  unfold actualLinkSurplus
  symm
  apply Finset.sum_subset (used_cells_subset H V)
  intro q hq hnot
  have hEmpty : commonLink H V q = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hnot ((mem_used_cells_iff_common_link_nonempty H V q).mpr
      ⟨hq, hn⟩)
  simp [hEmpty, linkSurplus]

/-- An ambient pair outside the actual pair support has no completion
    vertex and hence zero quadratic budget. -/
theorem all_pair_budget_eq_actual_pair_budget
    (H : Family α) (V : Edge α) :
    (∑ p ∈ V.powersetCard 2,
      pairBudget (completionVertices H V p).card) =
      actualPairBudget H V := by
  unfold actualPairBudget
  symm
  apply Finset.sum_subset (used_pairs_subset H V)
  intro p hp hnot
  have hEmpty : completionVertices H V p = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨_, _, hxEdge⟩ := Finset.mem_filter.mp hx
    have hUsed : p ∈ usedPairs H V := by
      apply Finset.mem_filter.mpr
      exact ⟨hp, ⟨p ∪ {x}, hxEdge, Finset.subset_union_left⟩⟩
    exact hnot hUsed
  simp [hEmpty, pairBudget]

/-- Equation (II.4) of the all-rank manuscript, with every graph edge
    counted in both orientations.  Thus the right side is twice the
    manuscript's unordered-edge signed-weight total. -/
theorem all_roots_oriented_weight_sum_eq_actual_ledgers
    {H : Family α} (V : Edge α) (hH : Admissible H) :
    (∑ z ∈ V, rootedOrientedWeightTotal H V z) =
      4 * actualLinkSurplus H V - 4 * actualPairBudget H V := by
  have hGlobal := all_roots_oriented_weight_sum V hH
  have hLinkPairs := ordered_pair_sum_eq_twice_unordered V
    (fun q => linkSurplus (commonLink H V q).card)
  have hBudgetPairs := ordered_pair_sum_eq_twice_unordered V
    (fun p => pairBudget (completionVertices H V p).card)
  have hL := all_pair_link_surplus_eq_actual_link_surplus H V
  have hB := all_pair_budget_eq_actual_pair_budget H V
  simp only [rootNeighbors] at hGlobal
  rw [hLinkPairs, hBudgetPairs, hL, hB] at hGlobal
  nlinarith

end RootedWeightSum

end JSP523.Rank3
