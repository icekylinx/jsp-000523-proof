import JSP523.Rank3.RootedWeightSum
import JSP523.Rank3.FirstMoment

/-!
# Pair-budget part of the local payment ledger

§II.3 of the all-rank manuscript defines one local defect for each triple. Its
pair-budget term sums `b(d(p))/d(p)` over the three pairs of that triple.
This file proves directly from the actual triple incidence relation that
these local terms sum to the global pair budget.
-/

namespace JSP523.Rank3

section LocalPaymentLedger

variable {α : Type*} [DecidableEq α]

/-- Each triple contributes the normalized budget of each of its three
    pairs.  Summing over actual triples gives exactly the global budget. -/
theorem local_pair_budget_sum_eq_actualPairBudget
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ E ∈ H, ∑ p ∈ E.powersetCard 2,
      weightPairBudget (completionVertices H V p).card) =
      actualPairBudget H V := by
  let P : Family α := V.powersetCard 2
  have hSwap :
      (∑ E ∈ H, ∑ p ∈ E.powersetCard 2,
        weightPairBudget (completionVertices H V p).card) =
      ∑ p ∈ P, ∑ E ∈ containingEdges H p,
        weightPairBudget (completionVertices H V p).card := by
    apply Finset.sum_comm'
    intro E p
    constructor
    · rintro ⟨hE, hpE⟩
      obtain ⟨hpSub, hpCard⟩ := Finset.mem_powersetCard.mp hpE
      have hpP : p ∈ P :=
        Finset.mem_powersetCard.mpr
          ⟨hpSub.trans (hground E hE), hpCard⟩
      exact ⟨Finset.mem_filter.mpr ⟨hE, hpSub⟩, hpP⟩
    · rintro ⟨hContain, hpP⟩
      obtain ⟨hE, hpSub⟩ := Finset.mem_filter.mp hContain
      have hpCard : p.card = 2 := (Finset.mem_powersetCard.mp hpP).2
      exact ⟨hE, Finset.mem_powersetCard.mpr ⟨hpSub, hpCard⟩⟩
  calc
    (∑ E ∈ H, ∑ p ∈ E.powersetCard 2,
      weightPairBudget (completionVertices H V p).card) =
        ∑ p ∈ P, ∑ E ∈ containingEdges H p,
          weightPairBudget (completionVertices H V p).card := hSwap
    _ = ∑ p ∈ P,
          pairBudget (completionVertices H V p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard := completionVertices_card_eq_containingEdges
        H V p hUniform hground hp
      rw [← hcard]
      exact card_mul_weightPairBudget_eq_pairBudget _
    _ = actualPairBudget H V :=
      all_pair_budget_eq_actualPairBudget H V

/-- A weighted version of the completion-vertex bijection: for a fixed
    grounded pair `{z,x}`, the unique vertex of each containing triple
    outside that pair runs over the actual root neighbors of `x`. -/
theorem weighted_root_completion_sum
    (H : Family α) (V : Edge α) {z x : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hzx : z ≠ x)
    (f : α → ℚ) :
    (∑ E ∈ containingEdges H ({z, x} : Edge α),
      ∑ y ∈ (E.erase z).erase x, f y) =
      ∑ y ∈ rootNeighbors H V z x, f y := by
  let p : Edge α := {z, x}
  have hp2 : p.card = 2 := Finset.card_pair hzx
  calc
    (∑ E ∈ containingEdges H p,
      ∑ y ∈ (E.erase z).erase x, f y) =
        ∑ y ∈ rootNeighbors H V z x,
          ∑ E ∈ ({p ∪ {y}} : Family α), f y := by
      apply Finset.sum_comm'
      intro E y
      constructor
      · rintro ⟨hContain, hyErase⟩
        obtain ⟨hEH, hpE⟩ := Finset.mem_filter.mp hContain
        obtain ⟨hyNeX, hyEraseZ⟩ := Finset.mem_erase.mp hyErase
        obtain ⟨hyNeZ, hyE⟩ := Finset.mem_erase.mp hyEraseZ
        have hyNotP : y ∉ p := by simp [p, hyNeZ, hyNeX]
        have hEq : p ∪ {y} = E :=
          pair_extension_eq_triple hp2 (hUniform hEH) hpE hyE hyNotP
        have hyNeighbor : y ∈ rootNeighbors H V z x :=
          Finset.mem_filter.mpr
            ⟨hground E hEH hyE, hyNotP, hEq.symm ▸ hEH⟩
        exact ⟨Finset.mem_singleton.mpr hEq.symm, hyNeighbor⟩
      · rintro ⟨hSingle, hyNeighbor⟩
        have hEq : E = p ∪ {y} := Finset.mem_singleton.mp hSingle
        obtain ⟨_, hyNotP, hExt⟩ := Finset.mem_filter.mp hyNeighbor
        have hyNeZ : y ≠ z := by
          intro h
          exact hyNotP (by simp [h])
        have hyNeX : y ≠ x := by
          intro h
          exact hyNotP (by simp [h])
        have hContain : E ∈ containingEdges H p := by
          apply Finset.mem_filter.mpr
          constructor
          · exact hEq.symm ▸ hExt
          · intro t ht
            rw [hEq]
            exact Finset.mem_union.mpr (Or.inl ht)
        have hyErase : y ∈ (E.erase z).erase x := by
          apply Finset.mem_erase.mpr
          refine ⟨hyNeX, Finset.mem_erase.mpr ⟨hyNeZ, ?_⟩⟩
          rw [hEq]
          simp
        exact ⟨hContain, hyErase⟩
    _ = ∑ y ∈ rootNeighbors H V z x, f y := by simp

/-- Reindex oriented incidences of actual triples as oriented graph-link
    edges at their roots.  The equality holds for any weight on `(z,x,y)`;
    no signed-weight algebra or admissibility is used. -/
theorem triple_incidence_eq_root_link_sum
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (f : α → α → α → ℚ) :
    (∑ E ∈ H, ∑ z ∈ E, ∑ x ∈ E.erase z,
      ∑ y ∈ (E.erase z).erase x, f z x y) =
      ∑ z ∈ V, ∑ x ∈ V.erase z,
        ∑ y ∈ rootNeighbors H V z x, f z x y := by
  have hRootSwap :
      (∑ E ∈ H, ∑ z ∈ E, ∑ x ∈ E.erase z,
        ∑ y ∈ (E.erase z).erase x, f z x y) =
        ∑ z ∈ V, ∑ E ∈ H.filter (fun E => z ∈ E),
          ∑ x ∈ E.erase z,
            ∑ y ∈ (E.erase z).erase x, f z x y := by
    apply Finset.sum_comm'
    intro E z
    constructor
    · rintro ⟨hE, hzE⟩
      exact ⟨Finset.mem_filter.mpr ⟨hE, hzE⟩,
        hground E hE hzE⟩
    · rintro ⟨hzFilter, _⟩
      exact Finset.mem_filter.mp hzFilter
  have hPairSwap (z : α) :
      (∑ E ∈ H.filter (fun E => z ∈ E),
        ∑ x ∈ E.erase z,
          ∑ y ∈ (E.erase z).erase x, f z x y) =
        ∑ x ∈ V.erase z,
          ∑ E ∈ containingEdges H ({z, x} : Edge α),
            ∑ y ∈ (E.erase z).erase x, f z x y := by
    apply Finset.sum_comm'
    intro E x
    constructor
    · rintro ⟨hEFilter, hxErase⟩
      obtain ⟨hE, hzE⟩ := Finset.mem_filter.mp hEFilter
      obtain ⟨hxNeZ, hxE⟩ := Finset.mem_erase.mp hxErase
      have hpair : ({z, x} : Edge α) ⊆ E := by
        intro t ht
        rcases Finset.mem_insert.mp ht with htz | htx
        · exact htz ▸ hzE
        · exact (Finset.mem_singleton.mp htx) ▸ hxE
      exact ⟨Finset.mem_filter.mpr ⟨hE, hpair⟩,
        Finset.mem_erase.mpr ⟨hxNeZ, hground E hE hxE⟩⟩
    · rintro ⟨hContain, hxErase⟩
      obtain ⟨hE, hpair⟩ := Finset.mem_filter.mp hContain
      have hzE : z ∈ E := hpair (by simp)
      have hxE : x ∈ E := hpair (by simp)
      exact ⟨Finset.mem_filter.mpr ⟨hE, hzE⟩,
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxErase).1, hxE⟩⟩
  calc
    (∑ E ∈ H, ∑ z ∈ E, ∑ x ∈ E.erase z,
      ∑ y ∈ (E.erase z).erase x, f z x y) =
        ∑ z ∈ V, ∑ E ∈ H.filter (fun E => z ∈ E),
          ∑ x ∈ E.erase z,
            ∑ y ∈ (E.erase z).erase x, f z x y := hRootSwap
    _ = ∑ z ∈ V, ∑ x ∈ V.erase z,
          ∑ E ∈ containingEdges H ({z, x} : Edge α),
            ∑ y ∈ (E.erase z).erase x, f z x y := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hPairSwap z
    _ = ∑ z ∈ V, ∑ x ∈ V.erase z,
          ∑ y ∈ rootNeighbors H V z x, f z x y := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro x hx
      exact weighted_root_completion_sum H V hUniform hground
        (Ne.symm (Finset.mem_erase.mp hx).1) (fun y => f z x y)

/-- The negative part of an actual rooted signed weight. -/
def negativeRootedWeight
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  max (-rootedSignedWeight H V z x y) 0

/-- Total positive weight with both orientations of every rooted graph
    edge counted. -/
def orientedPositiveWeightTotal
    (H : Family α) (V : Edge α) : ℚ :=
  ∑ z ∈ V, ∑ x ∈ V.erase z,
    ∑ y ∈ rootNeighbors H V z x,
      positiveRootedWeight H V z x y

/-- Total absolute negative weight with the same orientation convention. -/
def orientedNegativeWeightTotal
    (H : Family α) (V : Edge α) : ℚ :=
  ∑ z ∈ V, ∑ x ∈ V.erase z,
    ∑ y ∈ rootNeighbors H V z x,
      negativeRootedWeight H V z x y

/-- Local absolute negative weight of a triple, again with both
    orientations of each of its three rooted edges counted. -/
def localOrientedNegativePayment
    (H : Family α) (V E : Edge α) : ℚ :=
  ∑ z ∈ E, ∑ x ∈ E.erase z,
    ∑ y ∈ (E.erase z).erase x,
      negativeRootedWeight H V z x y

/-- The local defect from equation (II.5).  The factor `1/2` removes the two
    orientations of each rooted edge; endpoint symmetry is proved in
    `RootedSignedWeights`. -/
def localSignedDefect
    (H : Family α) (V E : Edge α) : ℚ :=
  localOrientedNegativePayment H V E / 2 -
    ∑ p ∈ E.powersetCard 2,
      weightPairBudget (completionVertices H V p).card

theorem sum_local_oriented_negative_eq_global
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ E ∈ H, localOrientedNegativePayment H V E) =
      orientedNegativeWeightTotal H V := by
  exact triple_incidence_eq_root_link_sum H V hUniform hground
    (fun z x y => negativeRootedWeight H V z x y)

/-- Equation (5)'s exact global ledger: local defects sum to absolute
    negative weight minus the actual pair budget, under the orientation
    normalization used throughout this formalization. -/
theorem sum_localSignedDefect_eq_negative_sub_budget
    (H : Family α) (V : Edge α)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    (∑ E ∈ H, localSignedDefect H V E) =
      orientedNegativeWeightTotal H V / 2 -
        actualPairBudget H V := by
  have hNegative := sum_local_oriented_negative_eq_global
    H V hUniform hground
  have hBudget := local_pair_budget_sum_eq_actualPairBudget
    H V hUniform hground
  have hHalf :
      (∑ E ∈ H, localOrientedNegativePayment H V E / 2) =
        (∑ E ∈ H, localOrientedNegativePayment H V E) / 2 := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp only [localSignedDefect, Finset.sum_sub_distrib]
  rw [hHalf, hNegative, hBudget]

private theorem signed_eq_positive_sub_negative (w : ℚ) :
    w = max w 0 - max (-w) 0 := by
  by_cases hw : w ≤ 0
  · rw [max_eq_right hw, max_eq_left (by linarith : 0 ≤ -w)]
    ring
  · have hwNonneg : 0 ≤ w := le_of_lt (lt_of_not_ge hw)
    rw [max_eq_left hwNonneg,
      max_eq_right (by linarith : -w ≤ 0)]
    ring

/-- Summing positive minus absolute negative parts recovers the signed
    oriented weight total. -/
theorem oriented_signed_eq_positive_sub_negative
    (H : Family α) (V : Edge α) :
    (∑ z ∈ V, rootedOrientedWeightTotal H V z) =
      orientedPositiveWeightTotal H V -
        orientedNegativeWeightTotal H V := by
  calc
    (∑ z ∈ V, rootedOrientedWeightTotal H V z) =
        ∑ z ∈ V, ∑ x ∈ V.erase z,
          ∑ y ∈ rootNeighbors H V z x,
            (positiveRootedWeight H V z x y -
              negativeRootedWeight H V z x y) := by
      apply Finset.sum_congr rfl
      intro z hz
      unfold rootedOrientedWeightTotal
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact signed_eq_positive_sub_negative _
    _ = orientedPositiveWeightTotal H V -
          orientedNegativeWeightTotal H V := by
      simp only [orientedPositiveWeightTotal, orientedNegativeWeightTotal,
        Finset.sum_sub_distrib]

/-- Equation (6) of the manuscript on actual finite supports.  The factor
    `1/2` converts the positive oriented total to its unoriented value. -/
theorem signed_payment_identity_on_actual_supports
    {H : Family α} (V : Edge α)
    (hH : Admissible H)
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    2 * actualLinkSurplus H V - actualPairBudget H V =
      orientedPositiveWeightTotal H V / 2 -
        ∑ E ∈ H, localSignedDefect H V E := by
  have hSigned := all_roots_oriented_weight_sum_eq_actual_ledgers V hH
  have hSplit := oriented_signed_eq_positive_sub_negative H V
  have hDefect := sum_localSignedDefect_eq_negative_sub_budget
    H V hUniform hground
  linarith

end LocalPaymentLedger

end JSP523.Rank3
