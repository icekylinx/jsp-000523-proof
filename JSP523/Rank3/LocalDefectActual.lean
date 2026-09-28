import JSP523.Rank3.LocalTripartiteActual
import JSP523.Rank3.LocalGraphMarkedScalar

/-!
# From the tripartite graph payment to the signed defect

The graph theorem pays three part budgets with the three negative rooted
weights.  The local ledger uses an unoriented triple and a sum over its
three pairs.  This module identifies those two finite presentations.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem triple_pair_sets_distinct
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b} : Edge α) ≠ {a, c} ∧
      ({a, b} : Edge α) ≠ {b, c} ∧
      ({a, c} : Edge α) ≠ {b, c} := by
  constructor
  · intro h
    have hb : b ∈ ({a, c} : Edge α) := by rw [← h]; simp
    simp [hab.symm, hbc] at hb
  constructor
  · intro h
    have ha : a ∈ ({b, c} : Edge α) := by rw [← h]; simp
    simp [hab, hac] at ha
  · intro h
    have ha : a ∈ ({b, c} : Edge α) := by rw [← h]; simp
    simp [hab, hac] at ha

private theorem triple_powersetCard_two
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Edge α).powersetCard 2 =
      ({{a, b}, {a, c}, {b, c}} : Family α) := by
  classical
  have hSub :
      ({{a, b}, {a, c}, {b, c}} : Family α) ⊆
        ({a, b, c} : Edge α).powersetCard 2 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Finset.mem_powersetCard.mpr
        ⟨by simp, Finset.card_pair hab⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨by simp, Finset.card_pair hac⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨by simp, Finset.card_pair hbc⟩
  have hTriple : ({a, b, c} : Edge α).card = 3 := by
    simp [hab, hac, hbc]
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    triple_pair_sets_distinct a b c hab hac hbc
  have hRight :
      ({{a, b}, {a, c}, {b, c}} : Family α).card = 3 := by
    simp [hABAC, hABBC, hACBC]
  symm
  apply Finset.eq_of_subset_of_card_le hSub
  rw [hRight, Finset.card_powersetCard, hTriple]
  norm_num

private theorem negativeRootedWeight_comm
    (H : Family α) (V : Edge α) (z x y : α) :
    negativeRootedWeight H V z x y =
      negativeRootedWeight H V z y x := by
  unfold negativeRootedWeight
  rw [rootedSignedWeight_comm]

private theorem oriented_negative_payment_triple
    (H : Family α) (V : Edge α) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    localOrientedNegativePayment H V ({a, b, c} : Edge α) / 2 =
      negativeRootedWeight H V a b c +
        negativeRootedWeight H V b a c +
        negativeRootedWeight H V c a b := by
  have hEraseBC : (({a, b, c} : Edge α).erase b).erase c = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxc, hxb, hxa | hxb' | hxc'⟩
      · exact hxa
      · exact False.elim (hxb hxb')
      · exact False.elim (hxc hxc')
    · intro hxa
      subst x
      exact ⟨hac, hab, Or.inl rfl⟩
  simp [localOrientedNegativePayment, hab, hac, hbc,
    Finset.sum_insert, hEraseBC, negativeRootedWeight_comm]
  ring_nf

private theorem completionBudget_eq_erasedGraphBudget
    (H : Family α) (V p : Edge α) (x : α)
    (hx : x ∈ completionVertices H V p) :
    weightPairBudget (completionVertices H V p).card =
      localGraphBudget ((completionVertices H V p).erase x).card := by
  have hCard := Finset.card_erase_add_one hx
  rw [show (completionVertices H V p).card =
    ((completionVertices H V p).erase x).card + 1 by omega]
  exact (localGraphBudget_eq_shifted_pairBudget _).symm

private theorem completionBudget_triple_partA
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    weightPairBudget
        (completionVertices H V ({b, c} : Edge α)).card =
      localGraphBudget (actualLocalPartA H V a b c).card := by
  have haV : a ∈ V := hground _ hE (by simp)
  have haComp : a ∈ completionVertices H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hab, hac]
    · have hEq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hE
  have h := completionBudget_eq_erasedGraphBudget
    H V ({b, c} : Edge α) a haComp
  rw [← actualLocalPartA_eq_completionVertices_erase H V a b c]
    at h
  exact h

private theorem completionBudget_triple_partB
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    weightPairBudget
        (completionVertices H V ({a, c} : Edge α)).card =
      localGraphBudget (actualLocalPartB H V a b c).card := by
  have hbV : b ∈ V := hground _ hE (by simp)
  have hbComp : b ∈ completionVertices H V ({a, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨hbV, ?_, ?_⟩
    · simp [hab.symm, hbc]
    · have hEq : ({a, c} : Edge α) ∪ {b} = {a, b, c} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hE
  have h := completionBudget_eq_erasedGraphBudget
    H V ({a, c} : Edge α) b hbComp
  rw [← actualLocalPartB_eq_completionVertices_erase H V a b c]
    at h
  exact h

private theorem completionBudget_triple_partC
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    weightPairBudget
        (completionVertices H V ({a, b} : Edge α)).card =
      localGraphBudget (actualLocalPartC H V a b c).card := by
  have hcV : c ∈ V := hground _ hE (by simp)
  have hcComp : c ∈ completionVertices H V ({a, b} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨hcV, ?_, ?_⟩
    · simp [hac.symm, hbc.symm]
    · have hEq : ({a, b} : Edge α) ∪ {c} = {a, b, c} := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      rw [hEq]
      exact hE
  have h := completionBudget_eq_erasedGraphBudget
    H V ({a, b} : Edge α) c hcComp
  rw [← actualLocalPartC_eq_completionVertices_erase H V a b c]
    at h
  exact h

private theorem local_pair_budget_triple_eq_graph_budgets
    (H : Family α) (V : Edge α) (a b c : α)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    (∑ p ∈ ({a, b, c} : Edge α).powersetCard 2,
      weightPairBudget (completionVertices H V p).card) =
      localGraphBudget (actualLocalPartA H V a b c).card +
        localGraphBudget (actualLocalPartB H V a b c).card +
        localGraphBudget (actualLocalPartC H V a b c).card := by
  rw [triple_powersetCard_two a b c hab hac hbc]
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    triple_pair_sets_distinct a b c hab hac hbc
  have hAB :
      weightPairBudget
          (completionVertices H V ({a, b} : Edge α)).card =
        localGraphBudget (actualLocalPartC H V a b c).card :=
    completionBudget_triple_partC H V a b c hground hac hbc hE
  have hAC :
      weightPairBudget
          (completionVertices H V ({a, c} : Edge α)).card =
        localGraphBudget (actualLocalPartB H V a b c).card :=
    completionBudget_triple_partB H V a b c hground hab hbc hE
  have hBC :
      weightPairBudget
          (completionVertices H V ({b, c} : Edge α)).card =
        localGraphBudget (actualLocalPartA H V a b c).card :=
    completionBudget_triple_partA H V a b c hground hab hac hE
  simp [hABAC, hABBC, hACBC, hAB, hAC, hBC]
  ring

/-- The actual triple's signed defect is exactly the surplus of its three
finite pair-type graphs.  This retains the full amount available to pay a
bridge, beyond the nonnegative conclusion used in §II.A. -/
theorem actual_local_defect_eq_graph_surplus
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    localSignedDefect H V ({a, b, c} : Edge α) =
      tripartiteLocalSurplus (actualLocalTripartite H V a b c)
        (actualLocalPartA H V a b c)
        (actualLocalPartB H V a b c)
        (actualLocalPartC H V a b c) := by
  have hOrient := oriented_negative_payment_triple
    H V a b c hab hac hbc
  have hBudget := local_pair_budget_triple_eq_graph_budgets
    H V a b c hground hab hac hbc hE
  have hAB := actual_AB_signed_weight_eq_graph_score
    hUniform hground hab hac hbc hE
  have hAC := actual_AC_signed_weight_eq_graph_score
    hUniform hground hab hac hbc hE
  have hBC := actual_BC_signed_weight_eq_graph_score
    hUniform hground hab hac hbc hE
  unfold localSignedDefect tripartiteLocalSurplus
  rw [hOrient, hBudget]
  unfold negativeRootedWeight
  rw [hAB, hAC, hBC]
  unfold localGraphPayment
  ring_nf

/-- The marked graph surplus is available in the actual signed defect of
an admissible triple.  The listed neighborhood hypotheses are the finite
graph conditions that the bridge construction must supply. -/
theorem actual_local_defect_ge_marked_graph_gain
    {H : Family α} {V : Edge α} {a b c x y z : α}
    {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hx : x ∈ actualLocalPartA H V a b c)
    (hy : y ∈ actualLocalPartB H V a b c)
    (hz : z ∈ actualLocalPartC H V a b c)
    (hAB : (actualLocalPartB H V a b c).filter
      (fun t => (x, t) ∈ (actualLocalTripartite H V a b c).ab) = {y})
    (hAC : (actualLocalPartC H V a b c).filter
      (fun t => (x, t) ∈ (actualLocalTripartite H V a b c).ac) = {z})
    (hrDegree : bipRightDegree (actualLocalTripartite H V a b c).ab
      ((actualLocalPartA H V a b c).erase x) y = r)
    (hsDegree : bipRightDegree (actualLocalTripartite H V a b c).ac
      ((actualLocalPartA H V a b c).erase x) z = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hDisj : Disjoint
      (((actualLocalPartA H V a b c).erase x).filter
        (fun t => (t, y) ∈ (actualLocalTripartite H V a b c).ab))
      (((actualLocalPartA H V a b c).erase x).filter
        (fun t => (t, z) ∈ (actualLocalTripartite H V a b c).ac))) :
    min (localPhi (r + 1)) (localPhi (s + 1)) ≤
      localSignedDefect H V ({a, b, c} : Edge α) := by
  rw [actual_local_defect_eq_graph_surplus hUniform hground
    hab hac hbc hE]
  exact marked_mixed_local_surplus
    (actualLocalTripartite H V a b c)
    (actualLocalPartA H V a b c)
    (actualLocalPartB H V a b c)
    (actualLocalPartC H V a b c)
    x y z r s
    (actualLocalTripartite_mixed_degree_two
      hH hUniform hab hac hbc)
    hx hy hz hAB hAC hrDegree hsDegree hr hs hDisj

/-- Equation (II.5)'s local signed defect is nonnegative for every actual
triple in an admissible rank-three family.  This is the full §II.A
input to the global support ledger. -/
theorem localSignedDefect_nonneg_of_admissible_triple
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    0 ≤ localSignedDefect H V ({a, b, c} : Edge α) := by
  have hPay := actual_three_root_negative_payment
    hH hUniform hground hab hac hbc hE
  have hOrient := oriented_negative_payment_triple
    H V a b c hab hac hbc
  have hBudget := local_pair_budget_triple_eq_graph_budgets
    H V a b c hground hab hac hbc hE
  unfold localSignedDefect
  rw [hOrient, hBudget]
  linarith

/-- The local defect is nonnegative for every member of the family, with
no chosen ordering of its three vertices. -/
theorem localSignedDefect_nonneg
    {H : Family α} {V : Edge α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    {E : Edge α} (hE : E ∈ H) :
    0 ≤ localSignedDefect H V E := by
  obtain ⟨a, b, c, hab, hac, hbc, hEq⟩ :=
    Finset.card_eq_three.mp (hUniform hE)
  rw [hEq]
  exact localSignedDefect_nonneg_of_admissible_triple
    hH hUniform hground hab hac hbc (hEq ▸ hE)

/-- §II.A removes the local-defect subtraction from equation (II.6)
on genuine supports.  The remaining global task is to bound the positive
weights by the available receiver capacities and bridge payments. -/
theorem signed_payment_upper_of_admissible
    (H : Family α) (V : Edge α)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V) :
    2 * actualLinkSurplus H V - actualPairBudget H V ≤
      orientedPositiveWeightTotal H V / 2 := by
  have hId := signed_payment_identity_on_actual_supports
    V hH hUniform hground
  have hNonneg : 0 ≤ ∑ E ∈ H, localSignedDefect H V E := by
    apply Finset.sum_nonneg
    intro E hE
    exact localSignedDefect_nonneg hH hUniform hground hE
  linarith

end JSP523.Rank3
