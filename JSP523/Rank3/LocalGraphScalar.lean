import JSP523.Rank3.LocalPaymentLedger

/-!
# Scalar estimates for the local signed graph theorem

§II.A of the all-rank manuscript uses `φ(t) = (t-2)_+/(t+1)` and
`H(n) = (n-1)φ(n)`.  These are the signed-weight fraction and normalized
pair budget shifted by one.  The complete-bipartite surplus bound and the
merging formulas below are the arithmetic inputs to its tripartite graph
argument.
-/

namespace JSP523.Rank3

/-- The local graph vertex contribution in §II.A. -/
def localPhi (n : ℕ) : ℚ := weightFraction (n + 1)

/-- The local graph part-size budget in §II.A. -/
def localGraphBudget (n : ℕ) : ℚ := ((n : ℚ) - 1) * localPhi n

theorem localPhi_nonneg (n : ℕ) : 0 ≤ localPhi n :=
  weightFraction_nonneg (n + 1)

theorem localPhi_mono {m n : ℕ} (hmn : m ≤ n) :
    localPhi m ≤ localPhi n :=
  weightFraction_mono (Nat.add_le_add_right hmn 1)

/-- Enlarging a part cannot reduce its available local budget.  This
allows isolated pure nodes to be reinstated after the active pair types
have been counted. -/
theorem localGraphBudget_mono {m n : ℕ} (hmn : m ≤ n) :
    localGraphBudget m ≤ localGraphBudget n := by
  by_cases hm : m = 0
  · subst m
    have hZero : localGraphBudget 0 = 0 := by
      norm_num [localGraphBudget, localPhi, weightFraction]
    rw [hZero]
    by_cases hn : n = 0
    · subst n; norm_num [localGraphBudget, localPhi, weightFraction]
    · have hnPos : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hnCast : (1 : ℚ) ≤ n := by exact_mod_cast hnPos
      unfold localGraphBudget
      exact mul_nonneg (by linarith) (localPhi_nonneg n)
  · have hmPos : 1 ≤ m := Nat.pos_of_ne_zero hm
    have hmCast : (1 : ℚ) ≤ m := by exact_mod_cast hmPos
    have hCast : (m : ℚ) ≤ n := by exact_mod_cast hmn
    have hPhi : localPhi m ≤ localPhi n := localPhi_mono hmn
    have hFirst := mul_le_mul_of_nonneg_left hPhi
      (show 0 ≤ (m : ℚ) - 1 by linarith)
    have hSecond := mul_le_mul_of_nonneg_right
      (show (m : ℚ) - 1 ≤ (n : ℚ) - 1 by linarith)
      (localPhi_nonneg n)
    unfold localGraphBudget
    linarith

theorem localGraphBudget_eq_shifted_pairBudget (n : ℕ) :
    localGraphBudget n = weightPairBudget (n + 1) := by
  rw [weightPairBudget_eq]
  unfold localGraphBudget localPhi
  push_cast
  ring

/-- Above the zero range, `φ` has the manuscript's rational formula. -/
theorem localPhi_eq_formula {n : ℕ} (hn : 2 ≤ n) :
    localPhi n = ((n : ℚ) - 2) / ((n : ℚ) + 1) := by
  by_cases hn2 : n = 2
  · subst n
    norm_num [localPhi, weightFraction]
  · have hlarge : ¬ n + 1 ≤ 3 := by omega
    simp only [localPhi, weightFraction, ite_eq_right hlarge]
    push_cast
    ring

theorem localGraphBudget_eq_formula {n : ℕ} (hn : 2 ≤ n) :
    localGraphBudget n =
      (((n : ℚ) - 1) * ((n : ℚ) - 2)) / ((n : ℚ) + 1) := by
  rw [localGraphBudget, localPhi_eq_formula hn]
  ring

/-- The exact discrete increment used in §II.A's low-degree and
    mixed-node estimates. -/
theorem localPhi_succ_sub_eq
    {n : ℕ} (hn : 2 ≤ n) :
    localPhi (n + 1) - localPhi n =
      3 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
  rw [localPhi_eq_formula (by omega : 2 ≤ n + 1),
    localPhi_eq_formula hn]
  have hn1Pos : (0 : ℚ) < (n : ℚ) + 1 := by
    have : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
    linarith
  have hn2Pos : (0 : ℚ) < (n : ℚ) + 2 := by linarith
  push_cast
  field_simp
  ring

/-- Every single added neighbor raises a local graph contribution by at
    most one quarter. -/
theorem localPhi_succ_sub_le_quarter (n : ℕ) :
    localPhi (n + 1) - localPhi n ≤ (1 : ℚ) / 4 := by
  by_cases hn : n ≤ 1
  · rcases (by omega : n = 0 ∨ n = 1) with h | h
    · subst n; norm_num [localPhi, weightFraction]
    · subst n; norm_num [localPhi, weightFraction]
  · have hn2 : 2 ≤ n := by omega
    rw [localPhi_succ_sub_eq hn2]
    have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hden : 0 < ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
      apply mul_pos <;> linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith

/-- The excess of a complete bipartite pair type is the same degree-only
    base weight that appears in the global deficit formula. -/
theorem complete_bipartite_excess_eq_baseWeight (x y : ℕ) :
    (x : ℚ) * localPhi y + (y : ℚ) * localPhi x -
      localGraphBudget x - localGraphBudget y =
      baseWeight (x + 1) (y + 1) := by
  unfold localGraphBudget localPhi baseWeight
  push_cast
  ring

/-- equation (II.A.5): a complete bipartite pair type has excess at most twice
    the smaller endpoint contribution. -/
theorem complete_bipartite_excess_le_twice_min (x y : ℕ) :
    (x : ℚ) * localPhi y + (y : ℚ) * localPhi x -
      localGraphBudget x - localGraphBudget y ≤
      2 * min (localPhi x) (localPhi y) := by
  rw [complete_bipartite_excess_eq_baseWeight]
  exact baseWeight_le_twice_min (x + 1) (y + 1)

/-- equation (II.A.6): exact budget gain when two part sizes are at least two. -/
theorem localGraphBudget_merge_exact
    {x u : ℕ} (hx : 2 ≤ x) (hu : 2 ≤ u) :
    localGraphBudget (x + u) - localGraphBudget x -
        localGraphBudget u =
      2 * localPhi x + 2 * localPhi u +
        6 / (((x + u : ℕ) : ℚ) + 1) := by
  have hxu : 2 ≤ x + u := by omega
  rw [localGraphBudget_eq_formula hxu,
    localGraphBudget_eq_formula hx,
    localGraphBudget_eq_formula hu,
    localPhi_eq_formula hx, localPhi_eq_formula hu]
  have hxPos : (0 : ℚ) < (x : ℚ) + 1 := by
    have : (0 : ℚ) ≤ x := by exact_mod_cast (Nat.zero_le x)
    linarith
  have huPos : (0 : ℚ) < (u : ℚ) + 1 := by
    have : (0 : ℚ) ≤ u := by exact_mod_cast (Nat.zero_le u)
    linarith
  have hxuPos : (0 : ℚ) < ((x + u : ℕ) : ℚ) + 1 := by
    have : (0 : ℚ) ≤ (x + u : ℕ) := by
      exact_mod_cast (Nat.zero_le (x + u))
    linarith
  push_cast
  field_simp
  ring

/-- The size-one boundary case used in equation (II.A.7). -/
theorem localGraphBudget_merge_one
    {u : ℕ} (hu : 2 ≤ u) :
    localGraphBudget (1 + u) - localGraphBudget 1 -
      localGraphBudget u - localPhi 1 - localPhi u =
      (3 * (u : ℚ)) / (((u : ℚ) + 1) * ((u : ℚ) + 2)) := by
  have hplus : 2 ≤ 1 + u := by omega
  rw [localGraphBudget_eq_formula hplus,
    localGraphBudget_eq_formula hu, localPhi_eq_formula hu]
  have hOneBudget : localGraphBudget 1 = 0 := by
    norm_num [localGraphBudget]
  have hOnePhi : localPhi 1 = 0 := by
    norm_num [localPhi, weightFraction]
  rw [hOneBudget, hOnePhi]
  have hu1Pos : (0 : ℚ) < (u : ℚ) + 1 := by
    have : (0 : ℚ) ≤ u := by exact_mod_cast (Nat.zero_le u)
    linarith
  have hu2Pos : (0 : ℚ) < (u : ℚ) + 2 := by linarith
  push_cast
  field_simp
  ring

/-- equation (II.A.7): merging positive part sizes pays both local vertex
    contributions. -/
theorem localGraphBudget_merge_lower
    {x u : ℕ} (hx : 0 < x) (hu : 0 < u) :
    localGraphBudget (x + u) ≥ localGraphBudget x +
      localGraphBudget u + localPhi x + localPhi u := by
  rcases (by omega : x = 1 ∨ 2 ≤ x) with hx1 | hx2
  · subst x
    rcases (by omega : u = 1 ∨ 2 ≤ u) with hu1 | hu2
    · subst u
      norm_num [localGraphBudget, localPhi, weightFraction]
    · have hExact := localGraphBudget_merge_one hu2
      have huq : (0 : ℚ) ≤ u := by exact_mod_cast (Nat.zero_le u)
      have hden : 0 < ((u : ℚ) + 1) * ((u : ℚ) + 2) := by
        apply mul_pos <;> linarith
      have hNonneg : 0 ≤ (3 * (u : ℚ)) /
          (((u : ℚ) + 1) * ((u : ℚ) + 2)) :=
        div_nonneg (by positivity) hden.le
      linarith
  · rcases (by omega : u = 1 ∨ 2 ≤ u) with hu1 | hu2
    · subst u
      have hExact := localGraphBudget_merge_one hx2
      have hxq : (0 : ℚ) ≤ x := by exact_mod_cast (Nat.zero_le x)
      have hden : 0 < ((x : ℚ) + 1) * ((x : ℚ) + 2) := by
        apply mul_pos <;> linarith
      have hNonneg : 0 ≤ (3 * (x : ℚ)) /
          (((x : ℚ) + 1) * ((x : ℚ) + 2)) :=
        div_nonneg (by positivity) hden.le
      have hsum : x + 1 = 1 + x := Nat.add_comm x 1
      rw [hsum]
      linarith
    · have hExact := localGraphBudget_merge_exact hx2 hu2
      have hPhiX := localPhi_nonneg x
      have hPhiU := localPhi_nonneg u
      have hDen : (0 : ℚ) < ((x + u : ℕ) : ℚ) + 1 := by
        have : (0 : ℚ) ≤ (x + u : ℕ) := by
          exact_mod_cast (Nat.zero_le (x + u))
        linarith
      have hFrac : 0 ≤ 6 / (((x + u : ℕ) : ℚ) + 1) :=
        div_nonneg (by norm_num) hDen.le
      linarith

/-- The exact growth of the local part budget when a mixed node is added,
    as used in equation (II.A.8). -/
theorem localGraphBudget_succ_sub_eq
    {a : ℕ} (ha : 2 ≤ a) :
    localGraphBudget (a + 1) - localGraphBudget a =
      1 - 6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) := by
  rw [localGraphBudget_eq_formula (by omega : 2 ≤ a + 1),
    localGraphBudget_eq_formula ha]
  have ha1Pos : (0 : ℚ) < (a : ℚ) + 1 := by
    have : (0 : ℚ) ≤ a := by exact_mod_cast (Nat.zero_le a)
    linarith
  have ha2Pos : (0 : ℚ) < (a : ℚ) + 2 := by linarith
  push_cast
  field_simp
  ring

/-- From size two onward, adding a node creates at least one half of a
    unit of budget. -/
theorem localGraphBudget_succ_sub_ge_half
    {a : ℕ} (ha : 2 ≤ a) :
    (1 : ℚ) / 2 ≤ localGraphBudget (a + 1) -
      localGraphBudget a := by
  rw [localGraphBudget_succ_sub_eq ha]
  have haq : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have hden : 0 < ((a : ℚ) + 1) * ((a : ℚ) + 2) := by
    apply mul_pos <;> linarith
  have hdenBound : (12 : ℚ) ≤
      ((a : ℚ) + 1) * ((a : ℚ) + 2) := by nlinarith
  have hFrac : 6 / (((a : ℚ) + 1) * ((a : ℚ) + 2)) ≤
      (1 : ℚ) / 2 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  linarith

/-- Degrees zero and one remain below `φ`'s positive threshold after a
    single new neighbor. -/
theorem localPhi_succ_sub_eq_zero_of_le_one
    {d : ℕ} (hd : d ≤ 1) :
    localPhi (d + 1) - localPhi d = 0 := by
  rcases (by omega : d = 0 ∨ d = 1) with h | h
  · subst d; norm_num [localPhi, weightFraction]
  · subst d; norm_num [localPhi, weightFraction]

/-- equation (II.A.8), in its precise numerical form: two existing neighbors
    of degrees at most the old part size cannot gain more than the budget
    created by adding one mixed vertex. -/
theorem two_neighbor_increment_le_budget_increment
    (a d₁ d₂ : ℕ)
    (hd₁ : d₁ ≤ a) (hd₂ : d₂ ≤ a) :
    (localPhi (d₁ + 1) - localPhi d₁) +
      (localPhi (d₂ + 1) - localPhi d₂) ≤
      localGraphBudget (a + 1) - localGraphBudget a := by
  by_cases ha : a ≤ 1
  · have hd₁' : d₁ ≤ 1 := hd₁.trans ha
    have hd₂' : d₂ ≤ 1 := hd₂.trans ha
    rw [localPhi_succ_sub_eq_zero_of_le_one hd₁',
      localPhi_succ_sub_eq_zero_of_le_one hd₂']
    rcases (by omega : a = 0 ∨ a = 1) with h | h
    · subst a; norm_num [localGraphBudget, localPhi, weightFraction]
    · subst a; norm_num [localGraphBudget, localPhi, weightFraction]
  · have ha2 : 2 ≤ a := by omega
    have h₁ := localPhi_succ_sub_le_quarter d₁
    have h₂ := localPhi_succ_sub_le_quarter d₂
    have hBudget := localGraphBudget_succ_sub_ge_half ha2
    linarith

/-- Total `φ` contribution of a complete bipartite pair type. -/
def completePairScore (x y : ℕ) : ℚ :=
  (x : ℚ) * localPhi y + (y : ℚ) * localPhi x

theorem completePairScore_comm (x y : ℕ) :
    completePairScore x y = completePairScore y x := by
  unfold completePairScore
  ac_rfl

/-- The weaker form of (II.A.5) used when all three pair types are
    present. -/
theorem completePairScore_le_budgets_add_phis (x y : ℕ) :
    completePairScore x y ≤
      localGraphBudget x + localGraphBudget y +
        localPhi x + localPhi y := by
  have hExcess := complete_bipartite_excess_le_twice_min x y
  have hMinX : min (localPhi x) (localPhi y) ≤ localPhi x := min_le_left _ _
  have hMinY : min (localPhi x) (localPhi y) ≤ localPhi y := min_le_right _ _
  dsimp [completePairScore]
  linarith

/-- For a nonempty side, its own budget covers one `φ` contribution. -/
theorem localPhi_le_localGraphBudget_of_pos
    {n : ℕ} (hn : 0 < n) :
    localPhi n ≤ localGraphBudget n := by
  rcases (by omega : n = 1 ∨ 2 ≤ n) with hOne | hTwo
  · subst n
    norm_num [localPhi, localGraphBudget, weightFraction]
  · have hcast : (0 : ℚ) ≤ (n : ℚ) - 2 := by
      have hq : (2 : ℚ) ≤ n := by exact_mod_cast hTwo
      linarith
    have hprod := mul_nonneg hcast (localPhi_nonneg n)
    unfold localGraphBudget
    nlinarith

theorem localPhi_le_localGraphBudget (n : ℕ) :
    localPhi n ≤ localGraphBudget n := by
  by_cases hn : n = 0
  · subst n
    norm_num [localPhi, localGraphBudget, weightFraction]
  · exact localPhi_le_localGraphBudget_of_pos (Nat.pos_of_ne_zero hn)

/-- A pair type with one vertex on its first side contributes exactly
    `φ` of the opposite side. -/
theorem completePairScore_one_left (y : ℕ) :
    completePairScore 1 y = localPhi y := by
  norm_num [completePairScore, localPhi, weightFraction]

/-- The pure three-type case of §II.A.4.  Six positive side sizes
    describe the disjoint allocations of the three original parts. -/
theorem three_complete_pair_types_le_part_budgets
    {a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    completePairScore a₁ b₁ +
      completePairScore a₂ c₁ +
      completePairScore b₂ c₂ ≤
      localGraphBudget (a₁ + a₂) +
      localGraphBudget (b₁ + b₂) +
      localGraphBudget (c₁ + c₂) := by
  have hAB := completePairScore_le_budgets_add_phis a₁ b₁
  have hAC := completePairScore_le_budgets_add_phis a₂ c₁
  have hBC := completePairScore_le_budgets_add_phis b₂ c₂
  have hA := localGraphBudget_merge_lower ha₁ ha₂
  have hB := localGraphBudget_merge_lower hb₁ hb₂
  have hC := localGraphBudget_merge_lower hc₁ hc₂
  linarith

/-- If both side sets at the shared original part have size at least two,
    the two complete pair types satisfy an untruncated total bound. -/
theorem two_complete_pair_types_le_part_budgets_large
    {x u y v : ℕ} (hx : 2 ≤ x) (hu : 2 ≤ u) :
    completePairScore x y + completePairScore u v ≤
      localGraphBudget (x + u) +
      localGraphBudget y + localGraphBudget v := by
  have hXY := complete_bipartite_excess_le_twice_min x y
  have hUV := complete_bipartite_excess_le_twice_min u v
  have hMinX : min (localPhi x) (localPhi y) ≤ localPhi x := min_le_left _ _
  have hMinU : min (localPhi u) (localPhi v) ≤ localPhi u := min_le_left _ _
  have hMerge := localGraphBudget_merge_exact hx hu
  have hDen : (0 : ℚ) < (((x + u : ℕ) : ℚ) + 1) := by
    have hNat : (0 : ℚ) ≤ (x + u : ℕ) := by
      exact_mod_cast (Nat.zero_le (x + u))
    linarith
  have hFrac : 0 ≤ 6 / (((x + u : ℕ) : ℚ) + 1) :=
    div_nonneg (by norm_num) hDen.le
  dsimp [completePairScore]
  linarith

/-- The exact two-type statement needed for (II.A.2).  Truncating each pair
    contribution at its two-part budget handles the size-one boundary. -/
theorem two_complete_pair_types_capped
    {x u y v : ℕ}
    (hx : 0 < x) (hu : 0 < u)
    (hy : 0 < y) (hv : 0 < v) :
    min (completePairScore x y)
          (localGraphBudget (x + u) + localGraphBudget y) +
      min (completePairScore u v)
          (localGraphBudget (x + u) + localGraphBudget v) ≤
      localGraphBudget (x + u) +
        localGraphBudget y + localGraphBudget v := by
  rcases (by omega : x = 1 ∨ 2 ≤ x) with hxOne | hxLarge
  · subst x
    have hFirst : completePairScore 1 y ≤ localGraphBudget y := by
      rw [completePairScore_one_left]
      exact localPhi_le_localGraphBudget_of_pos hy
    have hMinFirst := min_le_left (completePairScore 1 y)
      (localGraphBudget (1 + u) + localGraphBudget y)
    have hMinSecond := min_le_right (completePairScore u v)
      (localGraphBudget (1 + u) + localGraphBudget v)
    linarith
  · rcases (by omega : u = 1 ∨ 2 ≤ u) with huOne | huLarge
    · subst u
      have hSecond : completePairScore 1 v ≤ localGraphBudget v := by
        rw [completePairScore_one_left]
        exact localPhi_le_localGraphBudget_of_pos hv
      have hMinFirst := min_le_right (completePairScore x y)
        (localGraphBudget (x + 1) + localGraphBudget y)
      have hMinSecond := min_le_left (completePairScore 1 v)
        (localGraphBudget (x + 1) + localGraphBudget v)
      linarith
    · have hTotal := two_complete_pair_types_le_part_budgets_large
        hxLarge huLarge (y := y) (v := v)
      have hMinFirst := min_le_left (completePairScore x y)
        (localGraphBudget (x + u) + localGraphBudget y)
      have hMinSecond := min_le_left (completePairScore u v)
        (localGraphBudget (x + u) + localGraphBudget v)
      linarith

/-- The part-size budget is nonnegative, including the empty part. -/
theorem localGraphBudget_nonneg (n : ℕ) :
    0 ≤ localGraphBudget n := by
  by_cases hn : n = 0
  · subst n
    norm_num [localGraphBudget, localPhi, weightFraction]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hcast : (0 : ℚ) ≤ (n : ℚ) - 1 := by
      have : (1 : ℚ) ≤ n := by exact_mod_cast hnPos
      linarith
    exact mul_nonneg hcast (localPhi_nonneg n)

/-- The local signed payment from inequality (II.A.2), before identifying its
    graph scores with actual rooted signed weights. -/
def localGraphPayment
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) : ℚ :=
  max (localGraphBudget nA + localGraphBudget nB - tAB) 0 +
  max (localGraphBudget nA + localGraphBudget nC - tAC) 0 +
  max (localGraphBudget nB + localGraphBudget nC - tBC) 0

theorem localGraphPayment_swap_first_two
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) :
    localGraphPayment nA nB nC tAB tAC tBC =
      localGraphPayment nB nA nC tAB tBC tAC := by
  unfold localGraphPayment
  ac_rfl

theorem localGraphPayment_swap_last_two
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) :
    localGraphPayment nA nB nC tAB tAC tBC =
      localGraphPayment nA nC nB tAC tAB tBC := by
  unfold localGraphPayment
  ac_rfl

/-- Completing edges raises pair-type scores and can only make the
local signed-payment inequality harder. -/
theorem localGraphPayment_antitone_scores
    (nA nB nC : ℕ)
    {tAB tAC tBC sAB sAC sBC : ℚ}
    (hAB : tAB ≤ sAB) (hAC : tAC ≤ sAC) (hBC : tBC ≤ sBC) :
    localGraphPayment nA nB nC sAB sAC sBC ≤
      localGraphPayment nA nB nC tAB tAC tBC := by
  have hAB' :
      max (localGraphBudget nA + localGraphBudget nB - sAB) 0 ≤
        max (localGraphBudget nA + localGraphBudget nB - tAB) 0 :=
    max_le_max (by linarith) le_rfl
  have hAC' :
      max (localGraphBudget nA + localGraphBudget nC - sAC) 0 ≤
        max (localGraphBudget nA + localGraphBudget nC - tAC) 0 :=
    max_le_max (by linarith) le_rfl
  have hBC' :
      max (localGraphBudget nB + localGraphBudget nC - sBC) 0 ≤
        max (localGraphBudget nB + localGraphBudget nC - tBC) 0 :=
    max_le_max (by linarith) le_rfl
  unfold localGraphPayment
  linarith

theorem max_budget_sub_score_eq_sub_min (budget score : ℚ) :
    max (budget - score) 0 = budget - min score budget := by
  by_cases h : score ≤ budget
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
  · have h' : budget ≤ score := le_of_not_ge h
    rw [min_eq_right h', max_eq_right (sub_nonpos.mpr h')]
    ring

/-- inequality (II.A.2) is exactly a capped-score inequality. -/
theorem localGraphPayment_ge_iff_capped_scores
    (nA nB nC : ℕ) (tAB tAC tBC : ℚ) :
    localGraphBudget nA + localGraphBudget nB +
        localGraphBudget nC ≤
      localGraphPayment nA nB nC tAB tAC tBC ↔
    min tAB (localGraphBudget nA + localGraphBudget nB) +
      min tAC (localGraphBudget nA + localGraphBudget nC) +
      min tBC (localGraphBudget nB + localGraphBudget nC) ≤
        localGraphBudget nA + localGraphBudget nB +
          localGraphBudget nC := by
  unfold localGraphPayment
  rw [max_budget_sub_score_eq_sub_min,
    max_budget_sub_score_eq_sub_min,
    max_budget_sub_score_eq_sub_min]
  constructor <;> intro h <;> linarith

/-- The zero- or one-type pure base case of §II.A.4 requires no
restriction on the one possibly nonzero pair score. -/
theorem one_pair_type_local_payment
    (nA nB nC : ℕ) (tAB : ℚ) :
    localGraphBudget nA + localGraphBudget nB +
        localGraphBudget nC ≤
      localGraphPayment nA nB nC tAB 0 0 := by
  rw [localGraphPayment_ge_iff_capped_scores]
  have hAC : 0 ≤ localGraphBudget nA + localGraphBudget nC :=
    add_nonneg (localGraphBudget_nonneg nA) (localGraphBudget_nonneg nC)
  have hBC : 0 ≤ localGraphBudget nB + localGraphBudget nC :=
    add_nonneg (localGraphBudget_nonneg nB) (localGraphBudget_nonneg nC)
  rw [min_eq_left hAC, min_eq_left hBC]
  have hAB := min_le_right tAB
    (localGraphBudget nA + localGraphBudget nB)
  have hC := localGraphBudget_nonneg nC
  linarith

theorem one_pair_type_AC_local_payment
    (nA nB nC : ℕ) (tAC : ℚ) :
    localGraphBudget nA + localGraphBudget nB +
        localGraphBudget nC ≤
      localGraphPayment nA nB nC 0 tAC 0 := by
  rw [localGraphPayment_swap_last_two nA nB nC 0 tAC 0]
  have h := one_pair_type_local_payment nA nC nB tAC
  convert h using 1
  ring

theorem one_pair_type_BC_local_payment
    (nA nB nC : ℕ) (tBC : ℚ) :
    localGraphBudget nA + localGraphBudget nB +
        localGraphBudget nC ≤
      localGraphPayment nA nB nC 0 0 tBC := by
  rw [localGraphPayment_swap_first_two nA nB nC 0 0 tBC,
    localGraphPayment_swap_last_two nB nA nC 0 tBC 0]
  have h := one_pair_type_local_payment nB nC nA tBC
  convert h using 1
  ring

/-- The two complete pair-type pure graph, including size-one side sets,
    satisfies the local signed payment inequality. -/
theorem two_complete_pair_types_local_payment
    {x u y v : ℕ}
    (hx : 0 < x) (hu : 0 < u)
    (hy : 0 < y) (hv : 0 < v) :
    localGraphBudget (x + u) +
        localGraphBudget y + localGraphBudget v ≤
      localGraphPayment (x + u) y v
        (completePairScore x y) (completePairScore u v) 0 := by
  rw [localGraphPayment_ge_iff_capped_scores]
  have hCapped := two_complete_pair_types_capped hx hu hy hv
  have hNonneg : 0 ≤ localGraphBudget y + localGraphBudget v :=
    add_nonneg (localGraphBudget_nonneg y) (localGraphBudget_nonneg v)
  rw [min_eq_left hNonneg]
  simpa using hCapped

/-- The three complete pair-type pure graph satisfies the stronger
    untruncated inequality and therefore inequality (II.A.2). -/
theorem three_complete_pair_types_local_payment
    {a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    localGraphBudget (a₁ + a₂) +
        localGraphBudget (b₁ + b₂) +
        localGraphBudget (c₁ + c₂) ≤
      localGraphPayment (a₁ + a₂) (b₁ + b₂) (c₁ + c₂)
        (completePairScore a₁ b₁)
        (completePairScore a₂ c₁)
        (completePairScore b₂ c₂) := by
  rw [localGraphPayment_ge_iff_capped_scores]
  have hTotal := three_complete_pair_types_le_part_budgets
    ha₁ ha₂ hb₁ hb₂ hc₁ hc₂
  have hAB := min_le_left (completePairScore a₁ b₁)
    (localGraphBudget (a₁ + a₂) + localGraphBudget (b₁ + b₂))
  have hAC := min_le_left (completePairScore a₂ c₁)
    (localGraphBudget (a₁ + a₂) + localGraphBudget (c₁ + c₂))
  have hBC := min_le_left (completePairScore b₂ c₂)
    (localGraphBudget (b₁ + b₂) + localGraphBudget (c₁ + c₂))
  linarith

/-- The two-type pure payment remains valid for any actual graph scores
bounded by the corresponding complete bipartite pair types. -/
theorem two_bounded_pair_types_local_payment
    {x u y v : ℕ} {tAB tAC : ℚ}
    (hx : 0 < x) (hu : 0 < u)
    (hy : 0 < y) (hv : 0 < v)
    (hAB : tAB ≤ completePairScore x y)
    (hAC : tAC ≤ completePairScore u v) :
    localGraphBudget (x + u) +
        localGraphBudget y + localGraphBudget v ≤
      localGraphPayment (x + u) y v tAB tAC 0 := by
  have hComplete := two_complete_pair_types_local_payment hx hu hy hv
  have hMono := localGraphPayment_antitone_scores (x + u) y v
    hAB hAC (le_refl (0 : ℚ))
  linarith

/-- The analogous three-type payment with all three actual scores below
their complete bipartite envelopes. -/
theorem three_bounded_pair_types_local_payment
    {a₁ a₂ b₁ b₂ c₁ c₂ : ℕ}
    {tAB tAC tBC : ℚ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hAB : tAB ≤ completePairScore a₁ b₁)
    (hAC : tAC ≤ completePairScore a₂ c₁)
    (hBC : tBC ≤ completePairScore b₂ c₂) :
    localGraphBudget (a₁ + a₂) +
        localGraphBudget (b₁ + b₂) +
        localGraphBudget (c₁ + c₂) ≤
      localGraphPayment (a₁ + a₂) (b₁ + b₂) (c₁ + c₂)
        tAB tAC tBC := by
  have hComplete := three_complete_pair_types_local_payment
    ha₁ ha₂ hb₁ hb₂ hc₁ hc₂
  have hMono := localGraphPayment_antitone_scores
    (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) hAB hAC hBC
  linarith

/-- Pure two-type payment remains valid after adding isolated vertices to
any of the original three parts.  The size-one cases use the capped form
of the inequality, since the uncapped sum need not be bounded. -/
theorem two_bounded_pair_types_local_payment_with_isolates
    {x u y v nA nB nC : ℕ} {tAB tAC : ℚ}
    (hx : 0 < x) (hu : 0 < u)
    (hA : x + u ≤ nA) (hB : y ≤ nB) (hC : v ≤ nC)
    (hAB : tAB ≤ completePairScore x y)
    (hAC : tAC ≤ completePairScore u v) :
    localGraphBudget nA + localGraphBudget nB +
        localGraphBudget nC ≤
      localGraphPayment nA nB nC tAB tAC 0 := by
  rw [localGraphPayment_ge_iff_capped_scores]
  have hBC : 0 ≤ localGraphBudget nB + localGraphBudget nC :=
    add_nonneg (localGraphBudget_nonneg nB) (localGraphBudget_nonneg nC)
  rw [min_eq_left hBC]
  have hBudgetA := localGraphBudget_mono hA
  have hBudgetB := localGraphBudget_mono hB
  have hBudgetC := localGraphBudget_mono hC
  rcases (by omega : x = 1 ∨ 2 ≤ x) with hxOne | hxLarge
  · subst x
    have hFirst : tAB ≤ localGraphBudget nB := by
      calc
        tAB ≤ completePairScore 1 y := hAB
        _ = localPhi y := completePairScore_one_left y
        _ ≤ localGraphBudget y := localPhi_le_localGraphBudget y
        _ ≤ localGraphBudget nB := hBudgetB
    have hMinFirst := min_le_left tAB
      (localGraphBudget nA + localGraphBudget nB)
    have hMinSecond := min_le_right tAC
      (localGraphBudget nA + localGraphBudget nC)
    linarith
  · rcases (by omega : u = 1 ∨ 2 ≤ u) with huOne | huLarge
    · subst u
      have hSecond : tAC ≤ localGraphBudget nC := by
        calc
          tAC ≤ completePairScore 1 v := hAC
          _ = localPhi v := completePairScore_one_left v
          _ ≤ localGraphBudget v := localPhi_le_localGraphBudget v
          _ ≤ localGraphBudget nC := hBudgetC
      have hMinFirst := min_le_right tAB
        (localGraphBudget nA + localGraphBudget nB)
      have hMinSecond := min_le_left tAC
        (localGraphBudget nA + localGraphBudget nC)
      linarith
    · have hTotal := two_complete_pair_types_le_part_budgets_large
        hxLarge huLarge (y := y) (v := v)
      have hMinFirst := min_le_left tAB
        (localGraphBudget nA + localGraphBudget nB)
      have hMinSecond := min_le_left tAC
        (localGraphBudget nA + localGraphBudget nC)
      linarith

/-- The analogous three-type payment with arbitrary isolated vertices in
each original part. -/
theorem three_bounded_pair_types_local_payment_with_isolates
    {a₁ a₂ b₁ b₂ c₁ c₂ nA nB nC : ℕ}
    {tAB tAC tBC : ℚ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hA : a₁ + a₂ ≤ nA)
    (hB : b₁ + b₂ ≤ nB)
    (hC : c₁ + c₂ ≤ nC)
    (hAB : tAB ≤ completePairScore a₁ b₁)
    (hAC : tAC ≤ completePairScore a₂ c₁)
    (hBC : tBC ≤ completePairScore b₂ c₂) :
    localGraphBudget nA + localGraphBudget nB +
        localGraphBudget nC ≤
      localGraphPayment nA nB nC tAB tAC tBC := by
  rw [localGraphPayment_ge_iff_capped_scores]
  have hTotal := three_complete_pair_types_le_part_budgets
    ha₁ ha₂ hb₁ hb₂ hc₁ hc₂
  have hBudgetA := localGraphBudget_mono hA
  have hBudgetB := localGraphBudget_mono hB
  have hBudgetC := localGraphBudget_mono hC
  have hMinAB := min_le_left tAB
    (localGraphBudget nA + localGraphBudget nB)
  have hMinAC := min_le_left tAC
    (localGraphBudget nA + localGraphBudget nC)
  have hMinBC := min_le_left tBC
    (localGraphBudget nB + localGraphBudget nC)
  linarith

end JSP523.Rank3
