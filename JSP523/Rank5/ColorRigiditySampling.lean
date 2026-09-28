import JSP523.Rank5.ColorRigidityQuantitative
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite sampling bounds for the quantitative coloring lemma

This module isolates two finite counting steps used in IV.6.2.  The first is
the union bound for bad samples.  The second says that a regular incidence
relation transfers a bad-sample fraction to the corresponding pair fraction.
The manuscript's h-subsets and ordered edge-pairs are an instance of the
second statement once their constant incidence degrees are counted.
-/

namespace JSP523.Rank5

/-- The three edges of a triangle, represented as two-element vertex sets. -/
def triangleEdgeSupports {α : Type*} [DecidableEq α]
    (T : Finset α) : Finset (Finset α) :=
  T.powersetCard 2

/-- The three edges of `T` use exactly the two colors `c` and `d`. -/
def IsBicoloredTriangleSupport
    {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (edgeColor : Finset α → Option κ) (T : Finset α) : Prop :=
  ∃ c d : κ, c ≠ d ∧
    (∃ e ∈ triangleEdgeSupports T, edgeColor e = some c) ∧
    (∃ e ∈ triangleEdgeSupports T, edgeColor e = some d) ∧
    ∀ e ∈ triangleEdgeSupports T,
      edgeColor e = some c ∨ edgeColor e = some d

/-- Uncolored edge supports in the induced partial coloring on `V`. -/
def uncoloredEdgeSupports
    {α κ : Type*} [DecidableEq α]
    (V : Finset α) (edgeColor : Finset α → Option κ) : Finset (Finset α) :=
  (V.powersetCard 2).filter fun e => edgeColor e = none

/-- Fully colored bicolored triangle supports in the induced partial coloring. -/
noncomputable def bicoloredTriangleSupports
    {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (V : Finset α) (edgeColor : Finset α → Option κ) : Finset (Finset α) := by
  classical
  exact (V.powersetCard 3).filter (IsBicoloredTriangleSupport edgeColor)

/-- A union of support events contains at most the sum of their sizes. -/
theorem bad_samples_card_le_support_sum
    {S σ : Type*} [DecidableEq S] [DecidableEq σ]
    (samples : Finset S) (supports : Finset σ)
    (contains : σ → S → Prop) [DecidableRel contains]
    (B : ℕ)
    (hEvent : ∀ s ∈ supports,
      (samples.filter fun x => contains s x).card ≤ B) :
    (samples.filter fun x => ∃ s ∈ supports, contains s x).card ≤
      supports.card * B := by
  classical
  let events : σ → Finset S := fun s => samples.filter fun x => contains s x
  have hSub : (samples.filter fun x => ∃ s ∈ supports, contains s x) ⊆
      supports.biUnion events := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    obtain ⟨s, hs, hxs⟩ := hx.2
    exact Finset.mem_biUnion.mpr ⟨s, hs,
      Finset.mem_filter.mpr ⟨hx.1, hxs⟩⟩
  calc
    _ ≤ (supports.biUnion events).card := Finset.card_le_card hSub
    _ ≤ ∑ s ∈ supports, (events s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ supports, B := by
      apply Finset.sum_le_sum
      intro s hs
      exact hEvent s hs
    _ = supports.card * B := by simp

/-- The actual bad-sample count in IV.6.2.  For an `h`-set to be bad it must
contain either an uncolored two-set or the support of a fully colored
bicolored triangle.  Each fixed two-set is contained in
`choose(m-2,h-2)` samples and each fixed three-set in
`choose(m-3,h-3)` samples, giving the stated finite union bound. -/
theorem bad_coloring_samples_card_le
    {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (V : Finset α) (h : ℕ) (edgeColor : Finset α → Option κ)
    (h2 : 2 ≤ h) (h3 : 3 ≤ h) :
    ((V.powersetCard h).filter fun A =>
      (∃ e ∈ uncoloredEdgeSupports V edgeColor, e ⊆ A) ∨
      (∃ T ∈ bicoloredTriangleSupports V edgeColor, T ⊆ A)).card ≤
      (uncoloredEdgeSupports V edgeColor).card *
          (V.card - 2).choose (h - 2) +
        (bicoloredTriangleSupports V edgeColor).card *
          (V.card - 3).choose (h - 3) := by
  classical
  let samples := V.powersetCard h
  let U := uncoloredEdgeSupports V edgeColor
  let T := bicoloredTriangleSupports V edgeColor
  let badU := samples.filter fun A => ∃ e ∈ U, e ⊆ A
  let badT := samples.filter fun A => ∃ t ∈ T, t ⊆ A
  have hUsize : ∀ e ∈ U, e.card = 2 := by
    intro e he
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp he).1).2
  have hTsize : ∀ t ∈ T, t.card = 3 := by
    intro t ht
    change t ∈ (V.powersetCard 3).filter _ at ht
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp ht).1).2
  have hUbound : badU.card ≤ U.card * (V.card - 2).choose (h - 2) := by
    apply bad_samples_card_le_support_sum samples U (fun e A => e ⊆ A)
      ((V.card - 2).choose (h - 2))
    intro e he
    rw [Finset.card_filter_powersetCard_subset e V h
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).1)
      (by rw [hUsize e he]; omega)]
    rw [hUsize e he]
  have hTbound : badT.card ≤ T.card * (V.card - 3).choose (h - 3) := by
    apply bad_samples_card_le_support_sum samples T (fun t A => t ⊆ A)
      ((V.card - 3).choose (h - 3))
    intro t ht
    change t ∈ (V.powersetCard 3).filter _ at ht
    rw [Finset.card_filter_powersetCard_subset t V h
      ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht).1).1)
      (by rw [hTsize t ht]; omega)]
    rw [hTsize t ht]
  have hUnion :
      (samples.filter fun A =>
        (∃ e ∈ U, e ⊆ A) ∨ (∃ t ∈ T, t ⊆ A)) = badU ∪ badT := by
    ext A
    constructor
    · intro hA
      rcases Finset.mem_filter.mp hA with ⟨hA, hbad⟩
      rcases hbad with hU | hT
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hA, hU⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hA, hT⟩))
    · intro hA
      rcases Finset.mem_union.mp hA with hU | hT
      · rcases Finset.mem_filter.mp hU with ⟨hA, hU⟩
        exact Finset.mem_filter.mpr ⟨hA, Or.inl hU⟩
      · rcases Finset.mem_filter.mp hT with ⟨hA, hT⟩
        exact Finset.mem_filter.mpr ⟨hA, Or.inr hT⟩
  rw [hUnion]
  calc
    (badU ∪ badT).card ≤ badU.card + badT.card := Finset.card_union_le _ _
    _ ≤ U.card * (V.card - 2).choose (h - 2) +
        T.card * (V.card - 3).choose (h - 3) := Nat.add_le_add hUbound hTbound

end JSP523.Rank5
