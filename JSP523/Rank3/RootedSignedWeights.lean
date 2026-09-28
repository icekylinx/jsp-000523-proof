import JSP523.Rank3.SignedWeightAlgebra
import JSP523.Rank3.LinkFiberBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual signed weights on root links of a triple family

This instantiates the weight (II.2) and deficit (II.3) of
`paper/proof.pdf`, §II.3, using the actual completion vertices.
The common-neighbor sets come from genuine triples, and each deficit
summand is nonnegative because it is bounded by
its endpoint's completion degree.
-/

namespace JSP523.Rank3

section RootedSignedWeights

variable {α : Type*} [DecidableEq α]

/-- Pair edges of the graph link at a root. -/
def rootLink (H : Family α) (V : Edge α) (z : α) : Family α :=
  (V.powersetCard 2).filter (fun p => z ∉ p ∧ p ∪ {z} ∈ H)

/-- The graph neighbors of `x` in the link at `z` are exactly the
    completion vertices of the pair `{z,x}`. -/
def rootNeighbors (H : Family α) (V : Edge α) (z x : α) : Edge α :=
  completionVertices H V ({z, x} : Edge α)

theorem root_neighbors_subset_ground
    (H : Family α) (V : Edge α) (z x : α) :
    rootNeighbors H V z x ⊆ V :=
  completion_vertices_subset_ground H V _

theorem root_neighbors_not_root
    (H : Family α) (V : Edge α) (z x : α) :
    z ∉ rootNeighbors H V z x := by
  intro hz
  exact (Finset.mem_filter.mp hz).2.1 (by simp)

theorem root_neighbors_not_self
    (H : Family α) (V : Edge α) (z x : α) :
    x ∉ rootNeighbors H V z x := by
  intro hx
  exact (Finset.mem_filter.mp hx).2.1 (by simp)

/-- Adjacency in the graph link is symmetric on vertices distinct from
    its root. -/
theorem root_neighbors_mem_symm
    (H : Family α) (V : Edge α) {z x y : α}
    (hxV : x ∈ V) (hzx : z ≠ x)
    (hy : y ∈ rootNeighbors H V z x) :
    x ∈ rootNeighbors H V z y := by
  obtain ⟨_, hyOut, htrip⟩ := Finset.mem_filter.mp hy
  have hyz : y ≠ z := by
    intro h
    exact hyOut (by simp [h])
  have hyx : y ≠ x := by
    intro h
    exact hyOut (by simp [h])
  apply Finset.mem_filter.mpr
  refine ⟨hxV, ?_, ?_⟩
  · simp [Ne.symm hzx, Ne.symm hyx]
  · have heq : ({z, y} : Edge α) ∪ {x} =
        ({z, x} : Edge α) ∪ {y} := by
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ htrip

private theorem triple_rotate (a b c : α) :
    ({a, b} : Edge α) ∪ {c} = ({b, c} : Edge α) ∪ {a} := by
  ext w
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Every actual rooted common neighbor is a completion of each endpoint
    pair, so its count never exceeds either endpoint degree. -/
theorem root_common_neighbors_subset_root_neighbors_left
    (H : Family α) (V : Edge α) (z x u : α) :
    rootCommonNeighbors H V z x u ⊆ rootNeighbors H V z x := by
  intro t ht
  obtain ⟨htV, htz, htx, _, hxtz, _⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htV, ?_, ?_⟩
  · simp [htz, htx]
  · rw [triple_rotate z x t]
    exact hxtz

theorem root_common_neighbors_subset_root_neighbors_right
    (H : Family α) (V : Edge α) (z x u : α) :
    rootCommonNeighbors H V z x u ⊆ rootNeighbors H V z u := by
  intro t ht
  obtain ⟨htV, htz, _, htu, _, hutz⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htV, ?_, ?_⟩
  · simp [htz, htu]
  · rw [triple_rotate z u t]
    exact hutz

/-- The actual common-neighbor set agrees with the intersection of graph
    neighborhoods, independently of admissibility. -/
theorem root_common_neighbors_eq_inter_root_neighbors
    (H : Family α) (V : Edge α) (z x u : α) :
    rootCommonNeighbors H V z x u =
      rootNeighbors H V z x ∩ rootNeighbors H V z u := by
  ext t
  constructor
  · intro ht
    exact Finset.mem_inter.mpr
      ⟨root_common_neighbors_subset_root_neighbors_left H V z x u ht,
        root_common_neighbors_subset_root_neighbors_right H V z x u ht⟩
  · intro ht
    obtain ⟨htx, htu⟩ := Finset.mem_inter.mp ht
    obtain ⟨htV, htNotZX, hxtz⟩ := Finset.mem_filter.mp htx
    obtain ⟨_, htNotZU, hutz⟩ := Finset.mem_filter.mp htu
    have htz : t ≠ z := by
      intro h
      exact htNotZX (by simp [h])
    have htx' : t ≠ x := by
      intro h
      exact htNotZX (by simp [h])
    have htu' : t ≠ u := by
      intro h
      exact htNotZU (by simp [h])
    apply Finset.mem_filter.mpr
    refine ⟨htV, htz, htx', htu', ?_, ?_⟩
    · rw [← triple_rotate z x t]
      exact hxtz
    · rw [← triple_rotate z u t]
      exact hutz

/-- Formula (II.2) of `paper/proof.pdf`, for an oriented edge `{x,y}` of a
    root link.  The formula itself is meaningful even outside that link. -/
def rootedSignedWeight
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  (∑ u ∈ (rootNeighbors H V z y).erase x,
      weightFraction (rootCommonNeighbors H V z x u).card) +
    (∑ v ∈ (rootNeighbors H V z x).erase y,
      weightFraction (rootCommonNeighbors H V z y v).card) -
    weightPairBudget (rootNeighbors H V z x).card -
    weightPairBudget (rootNeighbors H V z y).card

/-- Reversing the endpoints of a rooted graph edge leaves its signed
    weight unchanged.  This justifies doubling when summing orientations. -/
theorem rooted_signed_weight_comm
    (H : Family α) (V : Edge α) (z x y : α) :
    rootedSignedWeight H V z x y =
      rootedSignedWeight H V z y x := by
  unfold rootedSignedWeight
  ring

/-- The nonnegative deficit from replacing every common-neighbor count
    by the corresponding endpoint completion degree. -/
def rootedWeightDeficit
    (H : Family α) (V : Edge α) (z x y : α) : ℚ :=
  (∑ u ∈ (rootNeighbors H V z y).erase x,
      (weightFraction (rootNeighbors H V z x).card -
        weightFraction (rootCommonNeighbors H V z x u).card)) +
    (∑ v ∈ (rootNeighbors H V z x).erase y,
      (weightFraction (rootNeighbors H V z y).card -
        weightFraction (rootCommonNeighbors H V z y v).card))

theorem rooted_weight_deficit_nonneg
    (H : Family α) (V : Edge α) (z x y : α) :
    0 ≤ rootedWeightDeficit H V z x y := by
  unfold rootedWeightDeficit
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro u hu
    apply sub_nonneg.mpr
    exact weight_fraction_mono (Finset.card_le_card
      (root_common_neighbors_subset_root_neighbors_left H V z x u))
  · apply Finset.sum_nonneg
    intro v hv
    apply sub_nonneg.mpr
    exact weight_fraction_mono (Finset.card_le_card
      (root_common_neighbors_subset_root_neighbors_left H V z y v))

/-- A rooted link edge is seen at both endpoint neighborhoods. -/
theorem root_link_edge_in_endpoint_neighbors
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y) :
    y ∈ rootNeighbors H V z x ∧ x ∈ rootNeighbors H V z y := by
  obtain ⟨hxyV, hzOut, hxyz⟩ := Finset.mem_filter.mp hxy
  have hxV : x ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
  have hyV : y ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
  have hzx : z ≠ x := by
    intro h
    exact hzOut (by simp [h])
  have hzy : z ≠ y := by
    intro h
    exact hzOut (by simp [h])
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨hyV, ?_, ?_⟩
    · simp [Ne.symm hzy, Ne.symm hxyNe]
    · rw [triple_rotate z x y]
      exact hxyz
  · apply Finset.mem_filter.mpr
    refine ⟨hxV, ?_, ?_⟩
    · simp [Ne.symm hzx, hxyNe]
    · have heq : ({z, y} : Edge α) ∪ {x} =
          ({x, y} : Edge α) ∪ {z} := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq.symm ▸ hxyz

/-- On a ground vertex different from the root, adjacency in the rooted
    graph is exactly membership of the corresponding pair in the root link. -/
theorem mem_root_neighbors_iff_mem_root_link
    (H : Family α) (V : Edge α) {z x y : α}
    (hxV : x ∈ V) (hzx : z ≠ x) :
    y ∈ rootNeighbors H V z x ↔
      ({x, y} : Edge α) ∈ rootLink H V z := by
  constructor
  · intro hy
    obtain ⟨hyV, hyOut, htrip⟩ := Finset.mem_filter.mp hy
    have hyz : y ≠ z := by
      intro h
      exact hyOut (by simp [h])
    have hyx : y ≠ x := by
      intro h
      exact hyOut (by simp [h])
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro t ht
        rcases Finset.mem_insert.mp ht with htx | hty
        · exact htx ▸ hxV
        · exact (Finset.mem_singleton.mp hty) ▸ hyV
      · exact Finset.card_pair (Ne.symm hyx)
    · constructor
      · simp [hzx, Ne.symm hyz]
      · rw [← triple_rotate z x y]
        exact htrip
  · intro hxy
    have hxyNe : x ≠ y := by
      intro h
      have hp2 : ({x, y} : Edge α).card = 2 :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hxy).1).2
      simp [h] at hp2
    exact (root_link_edge_in_endpoint_neighbors H V hxy hxyNe).1

/-- Formula (II.3) of `paper/proof.pdf` for an actual root-link edge. -/
theorem rooted_signed_weight_eq_base_sub_deficit
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y) :
    rootedSignedWeight H V z x y =
      baseWeight (rootNeighbors H V z x).card
        (rootNeighbors H V z y).card -
      rootedWeightDeficit H V z x y := by
  obtain ⟨hyNx, hxNy⟩ := root_link_edge_in_endpoint_neighbors H V hxy hxyNe
  let Nx := rootNeighbors H V z x
  let Ny := rootNeighbors H V z y
  let dx := Nx.card
  let dy := Ny.card
  have hxCard : ((Ny.erase x).card : ℚ) = (dy : ℚ) - 1 := by
    have hNat : (Ny.erase x).card + 1 = Ny.card :=
      Finset.card_erase_add_one hxNy
    have hQ : ((Ny.erase x).card : ℚ) + 1 = (Ny.card : ℚ) := by
      exact_mod_cast hNat
    dsimp [dy]
    linarith
  have hyCard : ((Nx.erase y).card : ℚ) = (dx : ℚ) - 1 := by
    have hNat : (Nx.erase y).card + 1 = Nx.card :=
      Finset.card_erase_add_one hyNx
    have hQ : ((Nx.erase y).card : ℚ) + 1 = (Nx.card : ℚ) := by
      exact_mod_cast hNat
    dsimp [dx]
    linarith
  have hSumX :
      (∑ u ∈ Ny.erase x, weightFraction dx) =
        ((dy : ℚ) - 1) * weightFraction dx := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hxCard]
  have hSumY :
      (∑ v ∈ Nx.erase y, weightFraction dy) =
        ((dx : ℚ) - 1) * weightFraction dy := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hyCard]
  have hBudgetX := weight_pair_budget_eq dx
  have hBudgetY := weight_pair_budget_eq dy
  have hsum : rootedSignedWeight H V z x y +
      rootedWeightDeficit H V z x y = baseWeight dx dy := by
    simp only [rootedSignedWeight, rootedWeightDeficit,
      Finset.sum_sub_distrib]
    change
      ((∑ u ∈ Ny.erase x,
          weightFraction (rootCommonNeighbors H V z x u).card) +
        (∑ v ∈ Nx.erase y,
          weightFraction (rootCommonNeighbors H V z y v).card) -
        weightPairBudget dx - weightPairBudget dy) +
        ((∑ u ∈ Ny.erase x, weightFraction dx) -
          (∑ u ∈ Ny.erase x,
            weightFraction (rootCommonNeighbors H V z x u).card) +
          ((∑ v ∈ Nx.erase y, weightFraction dy) -
            (∑ v ∈ Nx.erase y,
              weightFraction (rootCommonNeighbors H V z y v).card))) =
        baseWeight dx dy
    rw [hSumX, hSumY, hBudgetX, hBudgetY]
    unfold baseWeight
    ring
  dsimp [Nx, Ny, dx, dy] at hsum
  linarith

theorem rooted_signed_weight_le_twice_min
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y) :
    rootedSignedWeight H V z x y ≤
      2 * min (weightFraction (rootNeighbors H V z x).card)
        (weightFraction (rootNeighbors H V z y).card) := by
  have hEq := rooted_signed_weight_eq_base_sub_deficit H V hxy hxyNe
  have hDef := rooted_weight_deficit_nonneg H V z x y
  have hBase := base_weight_le_twice_min
    (rootNeighbors H V z x).card (rootNeighbors H V z y).card
  linarith

/-- Every positive signed weight has both endpoint completion degrees at
    least four.  This is the first structural cutoff in the charging proof. -/
theorem positive_rooted_signed_weight_high_degrees
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y)
    (hpositive : 0 < rootedSignedWeight H V z x y) :
    4 ≤ (rootNeighbors H V z x).card ∧
      4 ≤ (rootNeighbors H V z y).card := by
  have hbound := rooted_signed_weight_le_twice_min H V hxy hxyNe
  have hminpos : 0 < min
      (weightFraction (rootNeighbors H V z x).card)
      (weightFraction (rootNeighbors H V z y).card) := by
    linarith
  have hxpos : 0 < weightFraction (rootNeighbors H V z x).card :=
    lt_of_lt_of_le hminpos (min_le_left _ _)
  have hypos : 0 < weightFraction (rootNeighbors H V z y).card :=
    lt_of_lt_of_le hminpos (min_le_right _ _)
  constructor
  · by_contra h
    have hsmall : (rootNeighbors H V z x).card ≤ 3 := by omega
    rw [weight_fraction_eq_zero_of_le_three hsmall] at hxpos
    exact (not_lt_of_ge le_rfl) hxpos
  · by_contra h
    have hsmall : (rootNeighbors H V z y).card ≤ 3 := by omega
    rw [weight_fraction_eq_zero_of_le_three hsmall] at hypos
    exact (not_lt_of_ge le_rfl) hypos

theorem rooted_signed_weight_lt_two
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y) :
    rootedSignedWeight H V z x y < 2 := by
  have hbound := rooted_signed_weight_le_twice_min H V hxy hxyNe
  have hxlt := weight_fraction_lt_one (rootNeighbors H V z x).card
  have hminlt : min
      (weightFraction (rootNeighbors H V z x).card)
      (weightFraction (rootNeighbors H V z y).card) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) hxlt
  linarith

/-- Weak alternatives in the first orientation of a rooted link edge:
    their opposite endpoints have at most three common neighbors. -/
def weakLeftAlternatives
    (H : Family α) (V : Edge α) (z x y : α) : Edge α :=
  ((rootNeighbors H V z y).erase x).filter
    (fun u => (rootCommonNeighbors H V z x u).card ≤ 3)

/-- The symmetric orientation's weak alternatives. -/
def weakRightAlternatives
    (H : Family α) (V : Edge α) (z x y : α) : Edge α :=
  ((rootNeighbors H V z x).erase y).filter
    (fun v => (rootCommonNeighbors H V z y v).card ≤ 3)

private theorem weak_deficit_sum_bound
    {β : Type*} [DecidableEq β]
    (S : Finset β) (d : ℕ) (degree : β → ℕ)
    (hdegree : ∀ t ∈ S, degree t ≤ d)
    (m : ℚ) (hm : m ≤ weightFraction d) :
    ((S.filter (fun t => degree t ≤ 3)).card : ℚ) * m ≤
      ∑ t ∈ S, (weightFraction d - weightFraction (degree t)) := by
  let W := S.filter (fun t => degree t ≤ 3)
  have hWsub : W ⊆ S := Finset.filter_subset _ _
  have hweak : (∑ t ∈ W, m) ≤
      ∑ t ∈ W, (weightFraction d - weightFraction (degree t)) := by
    apply Finset.sum_le_sum
    intro t ht
    have hsmall : degree t ≤ 3 := (Finset.mem_filter.mp ht).2
    rw [weight_fraction_eq_zero_of_le_three hsmall]
    linarith
  have hrest :
      (∑ t ∈ W, (weightFraction d - weightFraction (degree t))) ≤
        ∑ t ∈ S, (weightFraction d - weightFraction (degree t)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hWsub
    intro t htS htW
    exact sub_nonneg.mpr (weight_fraction_mono (hdegree t htS))
  have hconst : ((W.card : ℚ) * m) = ∑ t ∈ W, m := by
    simp [Finset.sum_const, nsmul_eq_mul]
  exact hconst.trans_le (hweak.trans hrest)

/-- Each weak alternative consumes at least the smaller endpoint fraction
    of the nonnegative deficit.  Both orientations are counted separately. -/
theorem rooted_weight_deficit_ge_weak_count
    (H : Family α) (V : Edge α) (z x y : α) :
    (((weakLeftAlternatives H V z x y).card : ℚ) +
      ((weakRightAlternatives H V z x y).card : ℚ)) *
        min (weightFraction (rootNeighbors H V z x).card)
          (weightFraction (rootNeighbors H V z y).card) ≤
      rootedWeightDeficit H V z x y := by
  let dx := (rootNeighbors H V z x).card
  let dy := (rootNeighbors H V z y).card
  let m := min (weightFraction dx) (weightFraction dy)
  have hleft : ((weakLeftAlternatives H V z x y).card : ℚ) * m ≤
      ∑ u ∈ (rootNeighbors H V z y).erase x,
        (weightFraction dx -
          weightFraction (rootCommonNeighbors H V z x u).card) := by
    exact weak_deficit_sum_bound _ dx
      (fun u => (rootCommonNeighbors H V z x u).card)
      (by
        intro u hu
        exact Finset.card_le_card
          (root_common_neighbors_subset_root_neighbors_left H V z x u))
      m (min_le_left _ _)
  have hright : ((weakRightAlternatives H V z x y).card : ℚ) * m ≤
      ∑ v ∈ (rootNeighbors H V z x).erase y,
        (weightFraction dy -
          weightFraction (rootCommonNeighbors H V z y v).card) := by
    exact weak_deficit_sum_bound _ dy
      (fun v => (rootCommonNeighbors H V z y v).card)
      (by
        intro v hv
        exact Finset.card_le_card
          (root_common_neighbors_subset_root_neighbors_left H V z y v))
      m (min_le_right _ _)
  change _ ≤ _ + _
  nlinarith [hleft, hright]

/-- Two weak alternatives force the signed weight to be nonpositive. -/
theorem rooted_signed_weight_nonpos_of_two_weak_alternatives
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y)
    (hweak : 2 ≤ (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card) :
    rootedSignedWeight H V z x y ≤ 0 := by
  let m := min (weightFraction (rootNeighbors H V z x).card)
    (weightFraction (rootNeighbors H V z y).card)
  have hm : 0 ≤ m :=
    le_min (weight_fraction_nonneg _) (weight_fraction_nonneg _)
  have hcount : (2 : ℚ) ≤
      ((weakLeftAlternatives H V z x y).card : ℚ) +
        ((weakRightAlternatives H V z x y).card : ℚ) := by
    exact_mod_cast hweak
  have hdef := rooted_weight_deficit_ge_weak_count H V z x y
  have hbase := base_weight_le_twice_min
    (rootNeighbors H V z x).card (rootNeighbors H V z y).card
  have hEq := rooted_signed_weight_eq_base_sub_deficit H V hxy hxyNe
  have hmul := mul_le_mul_of_nonneg_right hcount hm
  dsimp [m] at hm hmul
  nlinarith

/-- A positive rooted weight can have at most one weak alternative. -/
theorem positive_rooted_signed_weight_weak_count_le_one
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y)
    (hpositive : 0 < rootedSignedWeight H V z x y) :
    (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card ≤ 1 := by
  by_contra h
  have htwo : 2 ≤ (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card := by omega
  have hnonpos := rooted_signed_weight_nonpos_of_two_weak_alternatives
    H V hxy hxyNe htwo
  linarith

/-- One weak alternative already lowers the signed weight below one. -/
theorem rooted_signed_weight_lt_one_of_weak_alternative
    (H : Family α) (V : Edge α) {z x y : α}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y)
    (hweak : 1 ≤ (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card) :
    rootedSignedWeight H V z x y < 1 := by
  let m := min (weightFraction (rootNeighbors H V z x).card)
    (weightFraction (rootNeighbors H V z y).card)
  have hm : 0 ≤ m :=
    le_min (weight_fraction_nonneg _) (weight_fraction_nonneg _)
  have hcount : (1 : ℚ) ≤
      ((weakLeftAlternatives H V z x y).card : ℚ) +
        ((weakRightAlternatives H V z x y).card : ℚ) := by
    exact_mod_cast hweak
  have hdef := rooted_weight_deficit_ge_weak_count H V z x y
  have hbase := base_weight_le_twice_min
    (rootNeighbors H V z x).card (rootNeighbors H V z y).card
  have hEq := rooted_signed_weight_eq_base_sub_deficit H V hxy hxyNe
  have hmul := mul_le_mul_of_nonneg_right hcount hm
  have hmlt : m < 1 :=
    lt_of_le_of_lt (min_le_left _ _)
      (weight_fraction_lt_one (rootNeighbors H V z x).card)
  dsimp [m] at hm hmul hmlt
  nlinarith

/-- A base pair in the oriented common link at `(z,v)` is an edge of the
    graph link at `z`. -/
theorem oriented_common_link_pair_mem_root_link
    (H : Family α) (V : Edge α) {z v x y : α}
    (hxy : ({x, y} : Edge α) ∈ orientedCommonLink H V z v) :
    ({x, y} : Edge α) ∈ rootLink H V z := by
  obtain ⟨hxyV, hdis, hxz, _⟩ := Finset.mem_filter.mp hxy
  have hzNot : z ∉ ({x, y} : Edge α) := by
    intro hz
    exact (Finset.disjoint_left.mp hdis) hz (by simp)
  exact Finset.mem_filter.mpr ⟨hxyV, hzNot, hxz⟩

/-- The second book pair in `J_{zv}` is a weak alternative to the first
    source edge.  The common-neighbor cutoff is the actual admissibility
    consequence proved in `LinkFiberBound`. -/
theorem second_book_pair_mem_weak_right_alternatives
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V z v) :
    u ∈ weakRightAlternatives H V z x y := by
  have hxuRoot := oriented_common_link_pair_mem_root_link H V hxuLink
  have huNeighbor :=
    (root_link_edge_in_endpoint_neighbors H V hxuRoot hxu).1
  have hmu := root_common_neighbors_card_le_two_of_two_book_pairs
    hH hzV hvV hzv hxy hxu hyu hxyLink hxuLink
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_erase.mpr ⟨Ne.symm hyu, huNeighbor⟩
  · omega

/-- A genuine two-pair book at a receiving cell caps the source weight by
    one, as used in the rank-three charge estimate. -/
theorem rooted_signed_weight_lt_one_of_second_book_pair
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V z v) :
    rootedSignedWeight H V z x y < 1 := by
  have hweak : u ∈ weakRightAlternatives H V z x y :=
    second_book_pair_mem_weak_right_alternatives hH hzV hvV hzv
      hxy hxu hyu hxyLink hxuLink
  have hcount : 1 ≤ (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card := by
    have : 0 < (weakRightAlternatives H V z x y).card :=
      Finset.card_pos.mpr ⟨u, hweak⟩
    omega
  exact rooted_signed_weight_lt_one_of_weak_alternative H V
    (oriented_common_link_pair_mem_root_link H V hxyLink) hxy hcount

end RootedSignedWeights

end JSP523.Rank3
