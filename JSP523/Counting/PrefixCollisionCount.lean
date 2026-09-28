import JSP523.Rank5.PrefixTrade
import JSP523.Counting.PrefixCollisionActual
import Mathlib.Tactic

/-!
# The complete finite prefix double count

Ordered pairs remove the factors of two from the bookkeeping.  The number
of available ordered disjoint p-prefix pairs is exactly
`choose(|V|,p) * choose(|V|-p,p)`, twice the manuscript's `T_p`.
The only geometric input is the common-tail bound (IV.B.2); neither the
Cauchy estimate nor the intersecting-pair estimate is assumed.
-/

namespace JSP523.Counting

open Finset
open scoped BigOperators

variable {α τ : Type*} [DecidableEq α]

/-- Ordered disjoint pairs in a finite prefix family. -/
def orderedDisjointPrefixes (F : Family α) : Finset (Edge α × Edge α) :=
  (F ×ˢ F).filter (fun YZ => Disjoint YZ.1 YZ.2)

theorem orderedDisjointPrefixes_card_eq_sum (F : Family α) :
    (orderedDisjointPrefixes F).card =
      ∑ Y ∈ F, (F.filter (fun Z => Disjoint Y Z)).card := by
  classical
  simp only [orderedDisjointPrefixes, Finset.card_filter]
  exact Finset.sum_product' F F
    (fun Y Z => if Disjoint Y Z then (1 : ℕ) else 0)

/-- The exact finite number of ordered disjoint p-prefix pairs. -/
theorem orderedDisjointPrefixes_powersetCard_card (V : Edge α) (p : ℕ) :
    (orderedDisjointPrefixes (V.powersetCard p)).card =
      V.card.choose p * (V.card - p).choose p := by
  classical
  rw [orderedDisjointPrefixes_card_eq_sum]
  have hTerm : ∀ Y ∈ V.powersetCard p,
      ((V.powersetCard p).filter (fun Z => Disjoint Y Z)).card =
        (V.card - p).choose p := by
    intro Y hY
    obtain ⟨hYV, hYcard⟩ := Finset.mem_powersetCard.mp hY
    have hEq : (V.powersetCard p).filter (fun Z => Disjoint Y Z) =
        (V \ Y).powersetCard p := by
      ext Z
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hZV, hZcard⟩, hYZ⟩
        refine ⟨?_, hZcard⟩
        intro x hxZ
        exact Finset.mem_sdiff.mpr ⟨hZV hxZ,
          fun hxY => (Finset.disjoint_left.mp hYZ) hxY hxZ⟩
      · rintro ⟨hZ, hZcard⟩
        refine ⟨⟨hZ.trans Finset.sdiff_subset, hZcard⟩, ?_⟩
        exact Finset.disjoint_left.mpr
          (fun x hxY hxZ => (Finset.mem_sdiff.mp (hZ hxZ)).2 hxY)
    have hDiff : (V \ Y).card = V.card - p := by
      have := Finset.card_sdiff_add_card_eq_card hYV
      omega
    rw [hEq, Finset.card_powersetCard, hDiff]
  calc
    (∑ Y ∈ V.powersetCard p,
      ((V.powersetCard p).filter (fun Z => Disjoint Y Z)).card)
        = ∑ _Y ∈ V.powersetCard p, (V.card - p).choose p :=
      Finset.sum_congr rfl hTerm
    _ = V.card.choose p * (V.card - p).choose p := by
      simp [Finset.card_powersetCard]

/-- A whole second moment is paid by the diagonal, intersecting prefixes,
and ordered disjoint pairs. -/
theorem prefix_card_square_le
    (F : Family α) (p D : ℕ) (hUniform : Uniform p F) (hD : 1 ≤ D)
    (hDegree : ∀ x : α, (F.filter (fun Y => x ∈ Y)).card ≤ D) :
    F.card ^ 2 ≤ (1 + p * (D - 1)) * F.card +
      (orderedDisjointPrefixes F).card := by
  classical
  have hRow : ∀ Y ∈ F,
      F.card ≤ 1 + p * (D - 1) + (F.filter (fun Z => Disjoint Y Z)).card := by
    intro Y hY
    have hInter := Rank5.fixed_prefix_intersections_le F hY p D
      (hUniform hY) hD hDegree
    have hPartition := Finset.card_filter_add_card_filter_not
      (s := F.erase Y) (fun Z => Disjoint Y Z)
    have hErase := Finset.card_erase_add_one hY
    have hSub : (F.erase Y).filter (fun Z => Disjoint Y Z) ⊆
        F.filter (fun Z => Disjoint Y Z) := by
      intro Z hZ
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_of_mem_erase (Finset.mem_filter.mp hZ).1,
          (Finset.mem_filter.mp hZ).2⟩
    have hLe := Finset.card_le_card hSub
    omega
  calc
    F.card ^ 2 = ∑ _Y ∈ F, F.card := by
      simp [pow_two]
    _ ≤ ∑ Y ∈ F, (1 + p * (D - 1) +
        (F.filter (fun Z => Disjoint Y Z)).card) := Finset.sum_le_sum hRow
    _ = (1 + p * (D - 1)) * F.card +
        (orderedDisjointPrefixes F).card := by
      rw [Finset.sum_add_distrib, ← orderedDisjointPrefixes_card_eq_sum]
      simp [Nat.mul_comm]

/-- Exact reindexing of assigned disjoint pairs by prefix pair instead of
by tail. No occurrence multiplicity is discarded. -/
theorem assigned_disjoint_pairs_double_count
    (T : Finset τ) (F : Family α) (assigned : τ → Family α)
    (hAssigned : ∀ P ∈ T, assigned P ⊆ F) :
    (∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card) =
      ∑ YZ ∈ orderedDisjointPrefixes F,
        (T.filter (fun P => YZ.1 ∈ assigned P ∧ YZ.2 ∈ assigned P)).card := by
  classical
  have hRow : ∀ P ∈ T,
      orderedDisjointPrefixes (assigned P) =
        (orderedDisjointPrefixes F).filter
          (fun YZ => YZ.1 ∈ assigned P ∧ YZ.2 ∈ assigned P) := by
    intro P hP
    ext ⟨Y, Z⟩
    simp only [orderedDisjointPrefixes, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hY, hZ⟩, hYZ⟩
      exact ⟨⟨⟨hAssigned P hP hY, hAssigned P hP hZ⟩, hYZ⟩, hY, hZ⟩
    · rintro ⟨⟨_, hYZ⟩, hY, hZ⟩
      exact ⟨⟨hY, hZ⟩, hYZ⟩
  calc
    (∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card) =
        ∑ P ∈ T, ((orderedDisjointPrefixes F).filter
          (fun YZ => YZ.1 ∈ assigned P ∧ YZ.2 ∈ assigned P)).card := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [hRow P hP]
    _ = ∑ YZ ∈ orderedDisjointPrefixes F,
        (T.filter (fun P => YZ.1 ∈ assigned P ∧ YZ.2 ∈ assigned P)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]

/-- Sum the geometric common-tail cap over exactly the available ordered
prefix pairs. -/
theorem assigned_disjoint_pairs_le
    (T : Finset τ) (F : Family α) (assigned : τ → Family α) (B : ℕ)
    (hAssigned : ∀ P ∈ T, assigned P ⊆ F)
    (hCommon : ∀ Y ∈ F, ∀ Z ∈ F, Disjoint Y Z →
      (T.filter (fun P => Y ∈ assigned P ∧ Z ∈ assigned P)).card ≤ B) :
    (∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card) ≤
      (orderedDisjointPrefixes F).card * B := by
  classical
  rw [assigned_disjoint_pairs_double_count T F assigned hAssigned]
  calc
    (∑ YZ ∈ orderedDisjointPrefixes F,
      (T.filter (fun P => YZ.1 ∈ assigned P ∧ YZ.2 ∈ assigned P)).card)
        ≤ ∑ _YZ ∈ orderedDisjointPrefixes F, B := by
      apply Finset.sum_le_sum
      intro YZ hYZ
      obtain ⟨hPair, hDisj⟩ := Finset.mem_filter.mp hYZ
      obtain ⟨hY, hZ⟩ := Finset.mem_product.mp hPair
      exact hCommon YZ.1 hY YZ.2 hZ hDisj
    _ = (orderedDisjointPrefixes F).card * B := by
      simp

/-- The second moment before applying a geometric common-tail cap. -/
theorem assigned_prefix_second_moment_le
    (V : Edge α) (T : Finset τ) (p D : ℕ) (assigned : τ → Family α)
    (hD : 1 ≤ D)
    (hAssigned : ∀ P ∈ T, assigned P ⊆ V.powersetCard p)
    (hDegree : ∀ P ∈ T, ∀ x : α,
      ((assigned P).filter (fun Y => x ∈ Y)).card ≤ D) :
    (∑ P ∈ T, (assigned P).card ^ 2) ≤
      (1 + p * (D - 1)) * (∑ P ∈ T, (assigned P).card) +
        ∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card := by
  classical
  calc
    (∑ P ∈ T, (assigned P).card ^ 2) ≤
        ∑ P ∈ T, ((1 + p * (D - 1)) * (assigned P).card +
          (orderedDisjointPrefixes (assigned P)).card) := by
      apply Finset.sum_le_sum
      intro P hP
      apply prefix_card_square_le (assigned P) p D ?_ hD (hDegree P hP)
      intro Y hY
      exact (Finset.mem_powersetCard.mp (hAssigned P hP hY)).2
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Complete finite prefix inequality, in natural-number form. The input
`hCommon` is precisely the geometric common-tail bound, not the desired
collision inequality. -/
theorem prefix_collision_quadratic_bound
    (V : Edge α) (T : Finset τ)
    (p D B : ℕ) (assigned : τ → Family α)
    (hD : 1 ≤ D)
    (hAssigned : ∀ P ∈ T, assigned P ⊆ V.powersetCard p)
    (hDegree : ∀ P ∈ T, ∀ x : α,
      ((assigned P).filter (fun Y => x ∈ Y)).card ≤ D)
    (hCommon : ∀ Y ∈ V.powersetCard p, ∀ Z ∈ V.powersetCard p,
      Disjoint Y Z →
      (T.filter (fun P => Y ∈ assigned P ∧ Z ∈ assigned P)).card ≤ B) :
    (∑ P ∈ T, (assigned P).card) ^ 2 ≤
      T.card * ((1 + p * (D - 1)) * (∑ P ∈ T, (assigned P).card) +
        V.card.choose p * (V.card - p).choose p * B) := by
  classical
  have hUpper := assigned_prefix_second_moment_le V T p D assigned
    hD hAssigned hDegree
  have hDisjoint : (∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card) ≤
      V.card.choose p * (V.card - p).choose p * B := by
    have h := assigned_disjoint_pairs_le T (V.powersetCard p)
      assigned B hAssigned hCommon
    simpa only [orderedDisjointPrefixes_powersetCard_card] using h
  have hCauchy := _root_.sq_sum_le_card_mul_sum_sq
    (s := T) (f := fun P => (assigned P).card)
  exact hCauchy.trans (Nat.mul_le_mul_left _
    (hUpper.trans (Nat.add_le_add_left hDisjoint _)))

/-- Real-valued common-tail budgets require no ceiling, and hence incur no
extra additive term in the exact finite quadratic inequality. -/
theorem prefix_collision_quadratic_bound_real
    (V : Edge α) (T : Finset τ)
    (p D : ℕ) (B : ℝ) (assigned : τ → Family α)
    (hD : 1 ≤ D)
    (hAssigned : ∀ P ∈ T, assigned P ⊆ V.powersetCard p)
    (hDegree : ∀ P ∈ T, ∀ x : α,
      ((assigned P).filter (fun Y => x ∈ Y)).card ≤ D)
    (hCommon : ∀ Y ∈ V.powersetCard p, ∀ Z ∈ V.powersetCard p,
      Disjoint Y Z →
      (((T.filter (fun P => Y ∈ assigned P ∧ Z ∈ assigned P)).card : ℕ) : ℝ) ≤ B) :
    ((∑ P ∈ T, (assigned P).card : ℕ) : ℝ) ^ 2 ≤
      (T.card : ℝ) * (((1 + p * (D - 1) : ℕ) : ℝ) *
        ((∑ P ∈ T, (assigned P).card : ℕ) : ℝ) +
        ((V.card.choose p * (V.card - p).choose p : ℕ) : ℝ) * B) := by
  classical
  let F := V.powersetCard p
  have hCommonSum :
      ((∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card : ℕ) : ℝ) ≤
        ((V.card.choose p * (V.card - p).choose p : ℕ) : ℝ) * B := by
    rw [assigned_disjoint_pairs_double_count T F assigned hAssigned, Nat.cast_sum]
    calc
      (∑ YZ ∈ orderedDisjointPrefixes F,
        ((T.filter (fun P => YZ.1 ∈ assigned P ∧ YZ.2 ∈ assigned P)).card : ℝ))
          ≤ ∑ _YZ ∈ orderedDisjointPrefixes F, B := by
        apply Finset.sum_le_sum
        intro YZ hYZ
        obtain ⟨hPair, hDisj⟩ := Finset.mem_filter.mp hYZ
        obtain ⟨hY, hZ⟩ := Finset.mem_product.mp hPair
        exact hCommon YZ.1 hY YZ.2 hZ hDisj
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, F,
          orderedDisjointPrefixes_powersetCard_card]
  have hUpperNat := assigned_prefix_second_moment_le V T p D assigned
    hD hAssigned hDegree
  have hUpper :
      ((∑ P ∈ T, (assigned P).card ^ 2 : ℕ) : ℝ) ≤
        ((1 + p * (D - 1) : ℕ) : ℝ) *
          ((∑ P ∈ T, (assigned P).card : ℕ) : ℝ) +
        ((∑ P ∈ T, (orderedDisjointPrefixes (assigned P)).card : ℕ) : ℝ) := by
    exact_mod_cast hUpperNat
  have hCauchyNat := _root_.sq_sum_le_card_mul_sum_sq
    (s := T) (f := fun P => (assigned P).card)
  have hCauchy : ((∑ P ∈ T, (assigned P).card : ℕ) : ℝ) ^ 2 ≤
      (T.card : ℝ) * ((∑ P ∈ T, (assigned P).card ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hCauchyNat
  have hCombined :
      ((∑ P ∈ T, (assigned P).card ^ 2 : ℕ) : ℝ) ≤
        ((1 + p * (D - 1) : ℕ) : ℝ) *
          ((∑ P ∈ T, (assigned P).card : ℕ) : ℝ) +
        ((V.card.choose p * (V.card - p).choose p : ℕ) : ℝ) * B := by
    linarith [hUpper, hCommonSum]
  exact hCauchy.trans (mul_le_mul_of_nonneg_left
    hCombined (Nat.cast_nonneg _))

end JSP523.Counting
