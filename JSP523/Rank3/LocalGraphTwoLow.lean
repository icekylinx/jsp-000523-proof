import JSP523.Rank3.LocalGraphTwoLowScalar

/-!
# The two-low-vertices bipartite lemma

The manuscript's proof of Lemma II.A.1 (§II.A.2) completes high-degree edges
and evaluating two rational expressions.  A coarser bound is enough: the
low vertices contribute zero, while every other vertex contributes at most
`φ` of the opposite part size.  The exact remaining gap factors into an
integer size difference and a monotone `φ` difference.
-/

namespace JSP523.Rank3

theorem local_phi_eq_zero_of_le_one
    {d : ℕ} (hd : d ≤ 1) : localPhi d = 0 := by
  rcases (by omega : d = 0 ∨ d = 1) with h | h
  · subst d; norm_num [localPhi, weightFraction]
  · subst d; norm_num [localPhi, weightFraction]

/-- The coarse bound needed when both low vertices lie in the first part. -/
theorem two_low_same_part_coarse
    (a b : ℕ) :
    ((a : ℚ) - 2) * localPhi b +
      (b : ℚ) * localPhi a ≤
        localGraphBudget a + localGraphBudget b := by
  have hGap : localGraphBudget a + localGraphBudget b -
      (((a : ℚ) - 2) * localPhi b +
        (b : ℚ) * localPhi a) =
      ((a : ℚ) - b - 1) * (localPhi a - localPhi b) := by
    unfold localGraphBudget
    ring
  rw [← sub_nonneg, hGap]
  by_cases h : b + 1 ≤ a
  · have hCast : (b : ℚ) + 1 ≤ a := by exact_mod_cast h
    have hPhi : localPhi b ≤ localPhi a :=
      local_phi_mono (by omega : b ≤ a)
    exact mul_nonneg (by linarith) (by linarith)
  · have hNat : a ≤ b := by omega
    have hCast : (a : ℚ) ≤ b := by exact_mod_cast hNat
    have hPhi : localPhi a ≤ localPhi b := local_phi_mono hNat
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- The coarse bound needed when the two low vertices lie in opposite
    parts. -/
theorem two_low_opposite_parts_coarse
    (a b : ℕ) :
    ((a : ℚ) - 1) * localPhi b +
      ((b : ℚ) - 1) * localPhi a ≤
        localGraphBudget a + localGraphBudget b := by
  have hGap : localGraphBudget a + localGraphBudget b -
      (((a : ℚ) - 1) * localPhi b +
        ((b : ℚ) - 1) * localPhi a) =
      ((a : ℚ) - b) * (localPhi a - localPhi b) := by
    unfold localGraphBudget
    ring
  rw [← sub_nonneg, hGap]
  rcases le_total a b with hab | hba
  · have hCast : (a : ℚ) ≤ b := by exact_mod_cast hab
    have hPhi : localPhi a ≤ localPhi b := local_phi_mono hab
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have hCast : (b : ℚ) ≤ a := by exact_mod_cast hba
    have hPhi : localPhi b ≤ localPhi a := local_phi_mono hba
    exact mul_nonneg (by linarith) (by linarith)

section BipartiteGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Degree in the first part of an actual finite bipartite edge set. -/
def bipLeftDegree (G : Finset (α × β)) (B : Finset β) (x : α) : ℕ :=
  (B.filter fun y => (x, y) ∈ G).card

/-- Degree in the second part of an actual finite bipartite edge set. -/
def bipRightDegree (G : Finset (α × β)) (A : Finset α) (y : β) : ℕ :=
  (A.filter fun x => (x, y) ∈ G).card

/-- The pair-type graph score from §II.A.1. -/
def bipartitePhiTotal
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) : ℚ :=
  (∑ x ∈ A, localPhi (bipLeftDegree G B x)) +
    ∑ y ∈ B, localPhi (bipRightDegree G A y)

/-- Reverse the orientation of a finite bipartite edge set. -/
def bipTranspose {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) : Finset (β × α) :=
  G.image Prod.swap

theorem mem_bip_transpose {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (y : β) (x : α) :
    (y, x) ∈ bipTranspose G ↔ (x, y) ∈ G := by
  simp [bipTranspose, Finset.mem_image]

theorem bip_left_degree_transpose {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (A : Finset α) (y : β) :
    bipLeftDegree (bipTranspose G) A y =
      bipRightDegree G A y := by
  simp [bipLeftDegree, bipRightDegree, mem_bip_transpose]

theorem bip_right_degree_transpose {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (B : Finset β) (x : α) :
    bipRightDegree (bipTranspose G) B x =
      bipLeftDegree G B x := by
  simp [bipLeftDegree, bipRightDegree, mem_bip_transpose]

theorem bipartite_phi_total_transpose {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) :
    bipartitePhiTotal (bipTranspose G) B A =
      bipartitePhiTotal G A B := by
  have hLeft (y : β) :
      bipLeftDegree (bipTranspose G) A y =
        bipRightDegree G A y := by
    exact bip_left_degree_transpose G A y
  have hRight (x : α) :
      bipRightDegree (bipTranspose G) B x =
        bipLeftDegree G B x := by
    exact bip_right_degree_transpose G B x
  simp only [bipartitePhiTotal, hLeft, hRight]
  ac_rfl

theorem bipartite_phi_total_empty
    (A : Finset α) (B : Finset β) :
    bipartitePhiTotal (∅ : Finset (α × β)) A B = 0 := by
  simp [bipartitePhiTotal, bipLeftDegree, bipRightDegree,
    localPhi, weightFraction]

/-- Edges outside the chosen two parts are irrelevant to the score. -/
theorem bipartite_phi_total_eq_zero_of_no_relevant_edge
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (hNo : ∀ x ∈ A, ∀ y ∈ B, (x, y) ∉ G) :
    bipartitePhiTotal G A B = 0 := by
  have hLeft (x : α) (hx : x ∈ A) :
      bipLeftDegree G B x = 0 := by
    unfold bipLeftDegree
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro y hyB hxy
    exact hNo x hx y hyB hxy
  have hRight (y : β) (hy : y ∈ B) :
      bipRightDegree G A y = 0 := by
    unfold bipRightDegree
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x hxA hxy
    exact hNo x hxA y hy hxy
  unfold bipartitePhiTotal
  have hL : (∑ x ∈ A, localPhi (bipLeftDegree G B x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hLeft x hx]
    exact local_phi_eq_zero_of_le_one (by omega)
  have hR : (∑ y ∈ B, localPhi (bipRightDegree G A y)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hRight y hy]
    exact local_phi_eq_zero_of_le_one (by omega)
  rw [hL, hR]
  ring

theorem bipartite_phi_total_nonneg
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) :
    0 ≤ bipartitePhiTotal G A B := by
  unfold bipartitePhiTotal
  apply add_nonneg <;> apply Finset.sum_nonneg
  · intro x hx
    exact local_phi_nonneg _
  · intro y hy
    exact local_phi_nonneg _

theorem bip_left_degree_le_card
    (G : Finset (α × β)) (B : Finset β) (x : α) :
    bipLeftDegree G B x ≤ B.card :=
  Finset.card_filter_le _ _

theorem bip_right_degree_le_card
    (G : Finset (α × β)) (A : Finset α) (y : β) :
    bipRightDegree G A y ≤ A.card :=
  Finset.card_filter_le _ _

/-- Completing a bipartite pair type can only increase its `φ` score.
This is the graph-to-complete-pair comparison used in the pure base case
of §II.A.4, with both tagged sides counted separately. -/
theorem bipartite_phi_total_le_complete_pair_score
    (G : Finset (α × β)) (A : Finset α) (B : Finset β) :
    bipartitePhiTotal G A B ≤ completePairScore A.card B.card := by
  have hLeft :
      (∑ x ∈ A, localPhi (bipLeftDegree G B x)) ≤
        (A.card : ℚ) * localPhi B.card := by
    calc
      (∑ x ∈ A, localPhi (bipLeftDegree G B x)) ≤
          ∑ _x ∈ A, localPhi B.card := by
            apply Finset.sum_le_sum
            intro x _
            exact local_phi_mono (bip_left_degree_le_card G B x)
      _ = (A.card : ℚ) * localPhi B.card := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hRight :
      (∑ y ∈ B, localPhi (bipRightDegree G A y)) ≤
        (B.card : ℚ) * localPhi A.card := by
    calc
      (∑ y ∈ B, localPhi (bipRightDegree G A y)) ≤
          ∑ _y ∈ B, localPhi A.card := by
            apply Finset.sum_le_sum
            intro y _
            exact local_phi_mono (bip_right_degree_le_card G A y)
      _ = (B.card : ℚ) * localPhi A.card := by
            simp [Finset.sum_const, nsmul_eq_mul]
  unfold bipartitePhiTotal completePairScore
  linarith

/-- A pair-type score is bounded by the complete graph on any two
subsets that contain all of its relevant edges.  Vertices outside those
subsets contribute zero, even if they are present in the ambient parts. -/
theorem bipartite_phi_total_le_complete_pair_score_of_support
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (A' : Finset α) (B' : Finset β)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hEdges : ∀ x ∈ A, ∀ y ∈ B,
      (x, y) ∈ G → x ∈ A' ∧ y ∈ B') :
    bipartitePhiTotal G A B ≤
      completePairScore A'.card B'.card := by
  have hLeftDeg (x : α) (hx : x ∈ A) :
      bipLeftDegree G B x ≤ B'.card := by
    unfold bipLeftDegree
    apply Finset.card_le_card
    intro y hy
    exact (hEdges x hx y (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hy).2).2
  have hRightDeg (y : β) (hy : y ∈ B) :
      bipRightDegree G A y ≤ A'.card := by
    unfold bipRightDegree
    apply Finset.card_le_card
    intro x hx
    exact (hEdges x (Finset.mem_filter.mp hx).1 y hy
      (Finset.mem_filter.mp hx).2).1
  have hLeftZero (x : α) (hx : x ∈ A) (hxNot : x ∉ A') :
      localPhi (bipLeftDegree G B x) = 0 := by
    have hDeg : bipLeftDegree G B x = 0 := by
      by_contra hNe
      have hPos : 0 < (B.filter fun y => (x, y) ∈ G).card :=
        Nat.pos_of_ne_zero hNe
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hPos
      exact hxNot ((hEdges x hx y (Finset.mem_filter.mp hy).1
        (Finset.mem_filter.mp hy).2).1)
    rw [hDeg]
    exact local_phi_eq_zero_of_le_one (by omega)
  have hRightZero (y : β) (hy : y ∈ B) (hyNot : y ∉ B') :
      localPhi (bipRightDegree G A y) = 0 := by
    have hDeg : bipRightDegree G A y = 0 := by
      by_contra hNe
      have hPos : 0 < (A.filter fun x => (x, y) ∈ G).card :=
        Nat.pos_of_ne_zero hNe
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hPos
      exact hyNot ((hEdges x (Finset.mem_filter.mp hx).1 y hy
        (Finset.mem_filter.mp hx).2).2)
    rw [hDeg]
    exact local_phi_eq_zero_of_le_one (by omega)
  have hLeftSplit :
      (∑ x ∈ A, localPhi (bipLeftDegree G B x)) =
      ∑ x ∈ A', localPhi (bipLeftDegree G B x) := by
    symm
    apply Finset.sum_subset hA'
    intro x hxA hxNot
    exact hLeftZero x hxA hxNot
  have hRightSplit :
      (∑ y ∈ B, localPhi (bipRightDegree G A y)) =
      ∑ y ∈ B', localPhi (bipRightDegree G A y) := by
    symm
    apply Finset.sum_subset hB'
    intro y hyB hyNot
    exact hRightZero y hyB hyNot
  have hLeftBound :
      (∑ x ∈ A', localPhi (bipLeftDegree G B x)) ≤
      (A'.card : ℚ) * localPhi B'.card := by
    calc
      (∑ x ∈ A', localPhi (bipLeftDegree G B x)) ≤
          ∑ _x ∈ A', localPhi B'.card := by
            apply Finset.sum_le_sum
            intro x hx
            exact local_phi_mono (hLeftDeg x (hA' hx))
      _ = (A'.card : ℚ) * localPhi B'.card := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hRightBound :
      (∑ y ∈ B', localPhi (bipRightDegree G A y)) ≤
      (B'.card : ℚ) * localPhi A'.card := by
    calc
      (∑ y ∈ B', localPhi (bipRightDegree G A y)) ≤
          ∑ _y ∈ B', localPhi A'.card := by
            apply Finset.sum_le_sum
            intro y hy
            exact local_phi_mono (hRightDeg y (hB' hy))
      _ = (B'.card : ℚ) * localPhi A'.card := by
            simp [Finset.sum_const, nsmul_eq_mul]
  unfold bipartitePhiTotal completePairScore
  rw [hLeftSplit, hRightSplit]
  linarith

/-- Lemma II.A.1 (in §II.A.2), same-part case, for an arbitrary actual finite
    bipartite graph. -/
theorem bipartite_two_low_same_part
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {x y : α}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y)
    (hdx : bipLeftDegree G B x ≤ 1)
    (hdy : bipLeftDegree G B y ≤ 1) :
    bipartitePhiTotal G A B ≤
      localGraphBudget A.card + localGraphBudget B.card := by
  let f : α → ℚ := fun z => localPhi (bipLeftDegree G B z)
  let g : β → ℚ := fun z => localPhi (bipRightDegree G A z)
  have hfx : f x = 0 := local_phi_eq_zero_of_le_one hdx
  have hfy : f y = 0 := local_phi_eq_zero_of_le_one hdy
  have hyErase : y ∈ A.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hLeftSplit : (∑ z ∈ A, f z) =
      ∑ z ∈ (A.erase x).erase y, f z := by
    calc
      (∑ z ∈ A, f z) = (∑ z ∈ A.erase x, f z) + f x :=
        (Finset.sum_erase_add A f hx).symm
      _ = ((∑ z ∈ (A.erase x).erase y, f z) + f y) + f x := by
        rw [← Finset.sum_erase_add (A.erase x) f hyErase]
      _ = ∑ z ∈ (A.erase x).erase y, f z := by rw [hfx, hfy]; ring
  have hLeftBound : (∑ z ∈ (A.erase x).erase y, f z) ≤
      (((A.erase x).erase y).card : ℚ) * localPhi B.card := by
    calc
      (∑ z ∈ (A.erase x).erase y, f z) ≤
          ∑ _z ∈ (A.erase x).erase y, localPhi B.card := by
            apply Finset.sum_le_sum
            intro z hz
            exact local_phi_mono (bip_left_degree_le_card G B z)
      _ = (((A.erase x).erase y).card : ℚ) * localPhi B.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hRightBound : (∑ z ∈ B, g z) ≤
      (B.card : ℚ) * localPhi A.card := by
    calc
      (∑ z ∈ B, g z) ≤ ∑ _z ∈ B, localPhi A.card := by
        apply Finset.sum_le_sum
        intro z hz
        exact local_phi_mono (bip_right_degree_le_card G A z)
      _ = (B.card : ℚ) * localPhi A.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hCardX := Finset.card_erase_add_one hx
  have hCardY := Finset.card_erase_add_one hyErase
  have hCardQ : (((A.erase x).erase y).card : ℚ) =
      (A.card : ℚ) - 2 := by
    have hNat : ((A.erase x).erase y).card + 2 = A.card := by omega
    have hRat : (((A.erase x).erase y).card : ℚ) + 2 =
        (A.card : ℚ) := by exact_mod_cast hNat
    linarith
  have hScalar := two_low_same_part_coarse A.card B.card
  unfold bipartitePhiTotal
  change (∑ z ∈ A, f z) + (∑ z ∈ B, g z) ≤ _
  rw [hLeftSplit]
  rw [hCardQ] at hLeftBound
  linarith

/-- Lemma II.A.1 (in §II.A.2), opposite-parts case. -/
theorem bipartite_two_low_opposite_parts
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {x : α} {y : β}
    (hx : x ∈ A) (hy : y ∈ B)
    (hdx : bipLeftDegree G B x ≤ 1)
    (hdy : bipRightDegree G A y ≤ 1) :
    bipartitePhiTotal G A B ≤
      localGraphBudget A.card + localGraphBudget B.card := by
  let f : α → ℚ := fun z => localPhi (bipLeftDegree G B z)
  let g : β → ℚ := fun z => localPhi (bipRightDegree G A z)
  have hfx : f x = 0 := local_phi_eq_zero_of_le_one hdx
  have hgy : g y = 0 := local_phi_eq_zero_of_le_one hdy
  have hLeftSplit : (∑ z ∈ A, f z) = ∑ z ∈ A.erase x, f z := by
    calc
      (∑ z ∈ A, f z) = (∑ z ∈ A.erase x, f z) + f x :=
        (Finset.sum_erase_add A f hx).symm
      _ = ∑ z ∈ A.erase x, f z := by rw [hfx]; ring
  have hRightSplit : (∑ z ∈ B, g z) = ∑ z ∈ B.erase y, g z := by
    calc
      (∑ z ∈ B, g z) = (∑ z ∈ B.erase y, g z) + g y :=
        (Finset.sum_erase_add B g hy).symm
      _ = ∑ z ∈ B.erase y, g z := by rw [hgy]; ring
  have hLeftBound : (∑ z ∈ A.erase x, f z) ≤
      ((A.erase x).card : ℚ) * localPhi B.card := by
    calc
      (∑ z ∈ A.erase x, f z) ≤
          ∑ _z ∈ A.erase x, localPhi B.card := by
            apply Finset.sum_le_sum
            intro z hz
            exact local_phi_mono (bip_left_degree_le_card G B z)
      _ = ((A.erase x).card : ℚ) * localPhi B.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hRightBound : (∑ z ∈ B.erase y, g z) ≤
      ((B.erase y).card : ℚ) * localPhi A.card := by
    calc
      (∑ z ∈ B.erase y, g z) ≤
          ∑ _z ∈ B.erase y, localPhi A.card := by
            apply Finset.sum_le_sum
            intro z hz
            exact local_phi_mono (bip_right_degree_le_card G A z)
      _ = ((B.erase y).card : ℚ) * localPhi A.card := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hCardX := Finset.card_erase_add_one hx
  have hCardY := Finset.card_erase_add_one hy
  have hCardAQ : ((A.erase x).card : ℚ) = (A.card : ℚ) - 1 := by
    have hRat : ((A.erase x).card : ℚ) + 1 = (A.card : ℚ) := by
      exact_mod_cast hCardX
    linarith
  have hCardBQ : ((B.erase y).card : ℚ) = (B.card : ℚ) - 1 := by
    have hRat : ((B.erase y).card : ℚ) + 1 = (B.card : ℚ) := by
      exact_mod_cast hCardY
    linarith
  have hScalar := two_low_opposite_parts_coarse A.card B.card
  unfold bipartitePhiTotal
  change (∑ z ∈ A, f z) + (∑ z ∈ B, g z) ≤ _
  rw [hLeftSplit, hRightSplit]
  rw [hCardAQ] at hLeftBound
  rw [hCardBQ] at hRightBound
  linarith

/-- Exchange the two parts of a finite bipartite graph. -/
def flipBipartiteGraph (G : Finset (α × β)) : Finset (β × α) :=
  G.image fun e => (e.2, e.1)

theorem mem_flip_bipartite_graph
    (G : Finset (α × β)) (x : α) (y : β) :
    (y, x) ∈ flipBipartiteGraph G ↔ (x, y) ∈ G := by
  classical
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    rcases e with ⟨u, v⟩
    cases Prod.mk.inj heq with
    | intro hv hu =>
      change u = x at hu
      change v = y at hv
      simpa only [hu, hv] using he
  · intro h
    exact Finset.mem_image.mpr ⟨(x, y), h, rfl⟩

theorem flip_bip_left_degree
    (G : Finset (α × β)) (A : Finset α)
    (y : β) :
    bipLeftDegree (flipBipartiteGraph G) A y =
      bipRightDegree G A y := by
  unfold bipLeftDegree bipRightDegree
  congr 1
  ext x
  simp [mem_flip_bipartite_graph]

theorem flip_bip_right_degree
    (G : Finset (α × β)) (B : Finset β) (x : α) :
    bipRightDegree (flipBipartiteGraph G) B x =
      bipLeftDegree G B x := by
  unfold bipLeftDegree bipRightDegree
  congr 1
  ext y
  simp [mem_flip_bipartite_graph]

theorem flip_bipartite_phi_total
    (G : Finset (α × β)) (A : Finset α)
    (B : Finset β) :
    bipartitePhiTotal (flipBipartiteGraph G) B A =
      bipartitePhiTotal G A B := by
  unfold bipartitePhiTotal
  simp_rw [flip_bip_left_degree, flip_bip_right_degree]
  ring

/-- Lemma II.A.1 (in §II.A.2), same-part case in the second part. -/
theorem bipartite_two_low_same_right_part
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {x y : β}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y)
    (hdx : bipRightDegree G A x ≤ 1)
    (hdy : bipRightDegree G A y ≤ 1) :
    bipartitePhiTotal G A B ≤
      localGraphBudget A.card + localGraphBudget B.card := by
  have hFlip := bipartite_two_low_same_part
    (flipBipartiteGraph G) B A hx hy hxy
    (by rw [flip_bip_left_degree]; exact hdx)
    (by rw [flip_bip_left_degree]; exact hdy)
  rw [flip_bipartite_phi_total] at hFlip
  linarith

/-- The tagged vertex set lets equal physical labels in different parts
    remain distinct graph nodes. -/
def bipartiteVertexInParts
    (A : Finset α) (B : Finset β) : Sum α β → Prop
  | Sum.inl x => x ∈ A
  | Sum.inr y => y ∈ B

def bipartiteVertexDegree
    (G : Finset (α × β)) (A : Finset α)
    (B : Finset β) : Sum α β → ℕ
  | Sum.inl x => bipLeftDegree G B x
  | Sum.inr y => bipRightDegree G A y

/-- Lemma II.A.1 (in §II.A.2) in full: any two distinct tagged nodes of degree at
    most one force the pair-type score below its two-part budget. -/
theorem bipartite_two_low_vertices
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (u v : Sum α β)
    (hu : bipartiteVertexInParts A B u)
    (hv : bipartiteVertexInParts A B v)
    (huv : u ≠ v)
    (hdu : bipartiteVertexDegree G A B u ≤ 1)
    (hdv : bipartiteVertexDegree G A B v ≤ 1) :
    bipartitePhiTotal G A B ≤
      localGraphBudget A.card + localGraphBudget B.card := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      have hxy : x ≠ y := by
        intro h
        exact huv (by rw [h])
      exact bipartite_two_low_same_part G A B hu hv hxy hdu hdv
    | inr y =>
      exact bipartite_two_low_opposite_parts G A B hu hv hdu hdv
  | inr x =>
    cases v with
    | inl y =>
      exact bipartite_two_low_opposite_parts G A B hv hu hdv hdu
    | inr y =>
      have hxy : x ≠ y := by
        intro h
        exact huv (by rw [h])
      exact bipartite_two_low_same_right_part G A B hu hv hxy hdu hdv

/-- A pair type with positive excess has at most one tagged node of degree
    at most one. -/
theorem positive_pair_type_at_most_one_low
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (hPositive : localGraphBudget A.card + localGraphBudget B.card <
      bipartitePhiTotal G A B)
    {u v : Sum α β}
    (hu : bipartiteVertexInParts A B u)
    (hv : bipartiteVertexInParts A B v)
    (hdu : bipartiteVertexDegree G A B u ≤ 1)
    (hdv : bipartiteVertexDegree G A B v ≤ 1) :
    u = v := by
  by_contra hNe
  have hBound := bipartite_two_low_vertices G A B
    u v hu hv hNe hdu hdv
  exact (not_le.mpr hPositive) hBound

/-- If no left node has an edge into the displayed right part, its graph
    score is zero. -/
theorem bipartite_phi_total_eq_zero_of_left_degrees_zero
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    (hZero : ∀ x ∈ A, bipLeftDegree G B x = 0) :
    bipartitePhiTotal G A B = 0 := by
  have hRightZero : ∀ y ∈ B, bipRightDegree G A y = 0 := by
    intro y hy
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
    have hxy : (x, y) ∈ G := (Finset.mem_filter.mp hx).2
    have hLeftPos : 0 < bipLeftDegree G B x := by
      apply Finset.card_pos.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
    have hLeftZero := hZero x hxA
    omega
  unfold bipartitePhiTotal
  have hLeftSum : (∑ x ∈ A, localPhi (bipLeftDegree G B x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hZero x hx]
    exact local_phi_eq_zero_of_le_one (by omega)
  have hRightSum : (∑ y ∈ B, localPhi (bipRightDegree G A y)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    rw [hRightZero y hy]
    exact local_phi_eq_zero_of_le_one (by omega)
  rw [hLeftSum, hRightSum]
  ring

/-- A bipartite star, even with missing spokes, contributes at most
    `φ` of its right part size. -/
theorem bipartite_star_score_le_phi_right
    (G : Finset (α × β)) (A : Finset α) (B : Finset β)
    {c : α} (hc : c ∈ A)
    (hStar : ∀ x ∈ A, x ≠ c → bipLeftDegree G B x = 0) :
    bipartitePhiTotal G A B ≤ localPhi B.card := by
  have hRightOne : ∀ y ∈ B, bipRightDegree G A y ≤ 1 := by
    intro y hy
    have hsub : A.filter (fun x => (x, y) ∈ G) ⊆ ({c} : Finset α) := by
      intro x hx
      have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
      have hxy : (x, y) ∈ G := (Finset.mem_filter.mp hx).2
      by_contra hxNotC
      have hxc : x ≠ c := by
        intro h
        exact hxNotC (by simp [h])
      have hLeftPos : 0 < bipLeftDegree G B x := by
        apply Finset.card_pos.mpr
        exact ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩
      have hLeftZero := hStar x hxA hxc
      omega
    exact (Finset.card_le_card hsub).trans (by simp)
  have hLeftSum : (∑ x ∈ A, localPhi (bipLeftDegree G B x)) =
      localPhi (bipLeftDegree G B c) := by
    apply Finset.sum_eq_single_of_mem c hc
    intro x hx hxc
    rw [hStar x hx hxc]
    exact local_phi_eq_zero_of_le_one (by omega)
  have hRightSum :
      (∑ y ∈ B, localPhi (bipRightDegree G A y)) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    exact local_phi_eq_zero_of_le_one (hRightOne y hy)
  have hCenterBound : localPhi (bipLeftDegree G B c) ≤
      localPhi B.card := local_phi_mono (bip_left_degree_le_card G B c)
  unfold bipartitePhiTotal
  rw [hLeftSum, hRightSum]
  simpa using hCenterBound

end BipartiteGraph

end JSP523.Rank3
