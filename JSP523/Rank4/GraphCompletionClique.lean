import Mathlib.Tactic

/-!
# Finite completion-clique color patterns

At a cleaned rank-four facet the completion clique is colored by its
completion-pair labels. The structural input says each triangle is either
monochromatic or rainbow. This file isolates the finite K3/K4 consequence
used by the unique-pair record construction.
-/

namespace JSP523.Rank4

abbrev CliqueColor := Fin 3

/-- Triangle colors are either all equal or pairwise distinct. -/
def monoOrRainbow (a b c : CliqueColor) : Prop :=
  (a = b ∧ b = c) ∨ (a ≠ b ∧ a ≠ c ∧ b ≠ c)

/-- Edge occurrences carrying a fixed label. The index type distinguishes
parallel records at the bookkeeping level even when labels are compared. -/
def colorSlotRecords {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label : ι → CliqueColor) (c : CliqueColor) : Finset ι :=
  Finset.univ.filter fun i => label i = c

/-- The three unordered completion pairs of a rainbow triangle, with one
index for each pair. -/
def rainbowTriangleEdgeColor (a b c : CliqueColor) (i : Fin 3) : CliqueColor :=
  if i = 0 then a else if i = 1 then b else c

/-- The finite record slots carrying color `x` in a rainbow triangle. -/
def rainbowTriangleColorRecords (a b c x : CliqueColor) : Finset (Fin 3) :=
  Finset.univ.filter fun i => rainbowTriangleEdgeColor a b c i = x

/-- The six unordered completion pairs of a properly colored K4. Their
colors are listed in the order `ab, ac, ad, bc, bd, cd`. -/
def properK4EdgeColor (a b c : CliqueColor) (i : Fin 6) : CliqueColor :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then c else if i = 4 then b else a

/-- The three completion-edge endpoint indices, ordered `01, 02, 12`. -/
def completionTriangleIndexPair (i : Fin 3) : Fin 3 × Fin 3 :=
  if i = 0 then (0, 1) else if i = 1 then (0, 2) else (1, 2)

/-- The six completion-edge endpoint indices, ordered `01, 02, 03, 12, 13, 23`. -/
def completionK4IndexPair (i : Fin 6) : Fin 4 × Fin 4 :=
  if i = 0 then (0, 1) else if i = 1 then (0, 2) else
  if i = 2 then (0, 3) else if i = 3 then (1, 2) else
  if i = 4 then (1, 3) else (2, 3)

/-- The finite record slots carrying color `x` in a proper K4. -/
def properK4ColorRecords (a b c x : CliqueColor) : Finset (Fin 6) :=
  Finset.univ.filter fun i => properK4EdgeColor a b c i = x

theorem completionTriangleIndexPair_injective :
    Function.Injective completionTriangleIndexPair := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [completionTriangleIndexPair] at *

theorem completionK4IndexPair_injective :
    Function.Injective completionK4IndexPair := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [completionK4IndexPair] at *

/-- The actual pair keys produced by the occurrences in one color slot. -/
def coloredSlotRecordImage {ι ρ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq ρ] (slots : Finset ι) (record : ι → ρ) : Finset ρ :=
  slots.image record

theorem coloredSlotRecordImage_card {ι ρ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq ρ] (slots : Finset ι) (record : ι → ρ)
    (hinj : Function.Injective record) :
    (coloredSlotRecordImage slots record).card = slots.card := by
  exact Finset.card_image_of_injective slots hinj

theorem coloredSlotRecordImage_disjoint {ι ρ : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq ρ]
    (left right : Finset ι) (record : ι → ρ)
    (hinj : Function.Injective record) (hdisj : Disjoint left right) :
    Disjoint (coloredSlotRecordImage left record)
      (coloredSlotRecordImage right record) := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hs
  have hij : i = j := hinj (hir.trans hjr.symm)
  subst j
  exact (Finset.disjoint_left.mp hdisj) hi hj

theorem rainbowTriangleColorRecords_card (a b c : CliqueColor)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∀ x : CliqueColor, (rainbowTriangleColorRecords a b c x).card = 1 := by
  intro x
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;>
    norm_num [rainbowTriangleColorRecords, rainbowTriangleEdgeColor] at *
  all_goals decide

theorem properK4ColorRecords_card (a b c : CliqueColor)
    (hAdj : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∀ x : CliqueColor, (properK4ColorRecords a b c x).card = 2 := by
  intro x
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;>
    norm_num [properK4ColorRecords, properK4EdgeColor] at *
  all_goals decide

/-- A rainbow triangle color record survives completely when all three
completion vertices are selected; otherwise losing its sole record costs
at most one. -/
def selectedRainbowColorRecords (a b c x : CliqueColor) (S : Finset (Fin 3)) :
    Finset (Fin 3) :=
  (rainbowTriangleColorRecords a b c x).filter fun i =>
    (completionTriangleIndexPair i).1 ∈ S ∧ (completionTriangleIndexPair i).2 ∈ S

theorem selected_rainbow_records_lower_bound
    (a b c : CliqueColor) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (S : Finset (Fin 3)) (x : CliqueColor) :
    1 - (if S.card < 3 then 1 else 0) ≤
      (selectedRainbowColorRecords a b c x S).card := by
  by_cases hFull : S.card = 3
  · have hS : S = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro z
      by_contra hz
      have hSub : S ⊆ Finset.univ.erase z := by
        intro w hw
        simp only [Finset.mem_erase, Finset.mem_univ]
        constructor
        · intro heq
          subst w
          exact hz hw
        · trivial
      have hle := Finset.card_le_card hSub
      simp at hle
      omega
    have hEq : selectedRainbowColorRecords a b c x S =
        rainbowTriangleColorRecords a b c x := by
      ext i
      simp [selectedRainbowColorRecords, completionTriangleIndexPair, hS]
    rw [hFull]
    simp
    rw [hEq]
    have hCard := rainbowTriangleColorRecords_card a b c h x
    have hpos : 0 < (rainbowTriangleColorRecords a b c x).card := by
      rw [hCard]
      decide
    exact Finset.card_pos.mp hpos
  · have hle : S.card ≤ 3 := Finset.card_le_univ S
    have hsmall : S.card < 3 := by omega
    simp [hsmall]

def selectedProperK4ColorRecords (a b c x : CliqueColor) (S : Finset (Fin 4)) :
    Finset (Fin 6) :=
  (properK4ColorRecords a b c x).filter fun i =>
    (completionK4IndexPair i).1 ∈ S ∧ (completionK4IndexPair i).2 ∈ S

theorem selected_proper_k4_records_lower_bound
    (a b c : CliqueColor) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (S : Finset (Fin 4)) (x : CliqueColor) :
    2 - min 2 (4 - S.card) ≤
      (selectedProperK4ColorRecords a b c x S).card := by
  by_cases hFull : S.card = 4
  · have hS : S = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro z
      by_contra hz
      have hSub : S ⊆ Finset.univ.erase z := by
        intro w hw
        simp only [Finset.mem_erase, Finset.mem_univ]
        constructor
        · intro heq
          subst w
          exact hz hw
        · trivial
      have hle := Finset.card_le_card hSub
      simp at hle
      omega
    have hEq : selectedProperK4ColorRecords a b c x S =
        properK4ColorRecords a b c x := by
      ext i
      simp [selectedProperK4ColorRecords, completionK4IndexPair, hS]
    rw [hFull]
    simp
    rw [hEq]
    have hCard := properK4ColorRecords_card a b c h x
    have hpos : 0 < (properK4ColorRecords a b c x).card := by
      rw [hCard]
      decide
    have hle : 2 ≤ (properK4ColorRecords a b c x).card := by rw [hCard]
    omega
  · by_cases hThree : S.card = 3
    · have hMissCard : (Sᶜ).card = 1 := by simp [Finset.card_compl, hThree]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hMissCard
      have hzNot : z ∉ S := by
        have : z ∈ Sᶜ := by rw [hz]; simp
        exact (Finset.mem_compl.mp this)
      have hOther : ∀ w : Fin 4, w ≠ z → w ∈ S := by
        intro w hw
        by_contra hwS
        have hwCompl : w ∈ Sᶜ := Finset.mem_compl.mpr hwS
        rw [hz] at hwCompl
        have hwEq : w = z := Finset.mem_singleton.mp hwCompl
        exact hw hwEq
      have hAvoid : ∀ z : Fin 4, ∃ i : Fin 6,
          properK4EdgeColor a b c i = x ∧
          (completionK4IndexPair i).1 ≠ z ∧
          (completionK4IndexPair i).2 ≠ z := by
        intro z
        fin_cases a <;> fin_cases b <;> fin_cases c <;>
          fin_cases x <;> fin_cases z
        all_goals norm_num at h
        all_goals decide
      obtain ⟨i, hiColor, hi₁, hi₂⟩ := hAvoid z
      have hBase : i ∈ properK4ColorRecords a b c x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiColor⟩
      have hSelected : i ∈ selectedProperK4ColorRecords a b c x S :=
        Finset.mem_filter.mpr ⟨hBase, hOther _ hi₁, hOther _ hi₂⟩
      have hpos : 0 < (selectedProperK4ColorRecords a b c x S).card :=
        Finset.card_pos.mpr ⟨i, hSelected⟩
      have hLoss : min 2 (4 - S.card) = 1 := by omega
      rw [hLoss]
      norm_num
      exact Finset.card_pos.mp hpos
    · have hle : S.card ≤ 4 := Finset.card_le_univ S
      have hsmall : S.card ≤ 2 := by omega
      have hLoss : min 2 (4 - S.card) = 2 := by omega
      simp [hLoss]

theorem colorSlotRecords_disjoint {ι : Type*} [Fintype ι]
    [DecidableEq ι] (label : ι → CliqueColor) {c d : CliqueColor}
    (hcd : c ≠ d) : Disjoint (colorSlotRecords label c)
      (colorSlotRecords label d) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hcd ((Finset.mem_filter.mp hi).2.symm.trans
    (Finset.mem_filter.mp hj).2)

/-- A rainbow triangle has one edge of each of the three colors. -/
theorem rainbow_triangle_three_colors {a b c : CliqueColor}
    (h : monoOrRainbow a b c) (hn : ¬ a = b) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rcases h with hmono | hrainbow
  · exact False.elim (hn hmono.1)
  · exact hrainbow

/-- If every triangle in a colored K4 is monochromatic or rainbow, then
either the whole K4 is monochromatic or the coloring is the proper
three-coloring: opposite edges agree and adjacent edges differ. -/
theorem k4_mono_or_proper_three_color
    (a b c d e f : CliqueColor)
    (habc : monoOrRainbow a b c)
    (habd : monoOrRainbow a d e)
    (hacd : monoOrRainbow b d f)
    (hbcd : monoOrRainbow c e f) :
    (a = b ∧ a = c ∧ a = d ∧ a = e ∧ a = f) ∨
      (a = f ∧ b = e ∧ c = d ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    norm_num [monoOrRainbow] at *

/-- In the rainbow-triangle case, each color occupies exactly one of its
three edge records. -/
theorem rainbow_triangle_color_occurs_once
    (a b c : CliqueColor)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∀ x : CliqueColor, ((if a = x then 1 else 0 : ℕ) +
      (if b = x then 1 else 0) + (if c = x then 1 else 0)) = 1 := by
  intro x
  fin_cases x <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num at *

/-- In the proper K4 case, every color occupies exactly two opposite
edges; its two edge records are disjoint from those of the other colors. -/
theorem proper_k4_color_occurs_twice
    (a b c d e f : CliqueColor)
    (hOpp : a = f ∧ b = e ∧ c = d)
    (hAdj : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∀ x : CliqueColor,
      ((if a = x then 1 else 0 : ℕ) + (if b = x then 1 else 0) +
       (if c = x then 1 else 0) + (if d = x then 1 else 0) +
       (if e = x then 1 else 0) + (if f = x then 1 else 0)) = 2 := by
  rcases hOpp with ⟨rfl, rfl, rfl⟩
  intro x
  fin_cases x <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num at *

/-- Every color has exactly one edge record in a rainbow triangle. -/
theorem rainbowTriangleRecordImage_card_eq_one {ρ : Type*}
    [DecidableEq ρ] (a b c x : CliqueColor) (record : Fin 3 → ρ)
    (hinj : Function.Injective record)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (coloredSlotRecordImage (rainbowTriangleColorRecords a b c x) record).card = 1 := by
  rw [coloredSlotRecordImage_card _ _ hinj,
    rainbowTriangleColorRecords_card a b c h x]

theorem properK4RecordImage_card_eq_two {ρ : Type*}
    [DecidableEq ρ] (a b c x : CliqueColor) (record : Fin 6 → ρ)
    (hinj : Function.Injective record)
    (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (coloredSlotRecordImage (properK4ColorRecords a b c x) record).card = 2 := by
  rw [coloredSlotRecordImage_card _ _ hinj,
    properK4ColorRecords_card a b c h x]

end JSP523.Rank4
