import JSP523.Counting.ExceptionalEqualityConstruction
import JSP523.LowerConstruction
import JSP523.Counting.LinearNearStar

/-!
# Rank-r admissibility of the local equality constructions

This is the converse construction from §IV.2.3: a complete star plus a
matching, or with one star facet removed and two exceptional outside edges
meeting in one vertex.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- The rank-r equality-construction criterion, shared with the rank-four
case through the shared all-rank admissibility lemma. -/
theorem star_plus_linear_outside_admissible
    {S B : Family α} {v : α} {r : ℕ}
    (hr : 3 ≤ r)
    (hSUniform : Uniform r S) (hBUniform : Uniform r B)
    (hLinear : LinearFamily B) (hCenter : ∀ T ∈ S, v ∈ T)
    (hAvoid : ∀ T ∈ B, v ∉ T)
    (hMissing : ∀ E ∈ B, ∀ F ∈ B, E ≠ F →
      ¬ Disjoint E F →
        insert v (E \ F) ∉ S ∨ insert v (F \ E) ∉ S) :
    Admissible (S ∪ B) :=
  JSP523.star_plus_linear_outside_admissible hr hSUniform hBUniform
    hLinear hCenter hAvoid hMissing

/-- The second §IV.2.3 equality construction, by the common
exceptional-pair admissibility theorem. -/
theorem one_missing_star_exceptional_pair_admissible
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 5 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform r M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    Admissible (((starFamily v r).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M) ) :=
  JSP523.one_missing_star_exceptional_pair_admissible
    (by omega : 3 ≤ r) hPcard hQcard hPQ hxP hxQ hvx hvP hvQ
    hMU hMatch hMAvoid hMDisj

/-- Complete star plus a maximum matching is admissible for every positive
rank (the Rank 5 instance of the first §IV.2.3 equality construction). -/
theorem complete_star_plus_matching_admissible
    [Fintype α] {r : ℕ} {v : α} {M : Family α}
    (hr : 0 < r) (hMU : Uniform r M) (hMatch : IsMatching M)
    (hAvoid : ∀ E ∈ M, v ∉ E) :
    Admissible (starFamily v r ∪ M) := by
  simpa only [starPlusMatching] using
    star_plus_matching_admissible hr hMU hMatch hAvoid


/-- The complete rank-r star is parametrized without repetition by its
`(r-1)`-subsets of the vertices away from the center. -/
theorem rank_r_star_card [Fintype α] (v : α) (r : ℕ) (hr : 0 < r) :
    (starFamily v r).card =
      ((Finset.univ.erase v : Edge α).card).choose (r - 1) := by
  exact JSP523.rank_r_star_card v r hr

/-- First equality construction: the complete star plus an outside maximum
matching has its exact binomial-plus-matching size, is uniform/admissible,
and has no missing star facets. -/
theorem complete_star_plus_matching_extremal
    [Fintype α] {r : ℕ} {v : α} {M : Family α}
    (hr : 0 < r) (hMU : Uniform r M) (hMatch : IsMatching M)
    (hAvoid : ∀ E ∈ M, v ∉ E)
    (hMsize : M.card =
      (Finset.univ.erase v : Edge α).card / r) :
    let W : Edge α := Finset.univ.erase v
    let H : Family α := starFamily v r ∪ M
    Admissible H ∧ Uniform r H ∧
      (∀ E ∈ H, E ⊆ insert v W) ∧
      missingStarFacets H W v r = ∅ ∧
      H.card = W.card.choose (r - 1) + W.card / r := by
  classical
  let W : Edge α := Finset.univ.erase v
  let H : Family α := starFamily v r ∪ M
  have hvW : v ∉ W := Finset.notMem_erase v Finset.univ
  have hUniform : Uniform r H := by
    intro E hE
    simp only [H, Finset.mem_union] at hE
    rcases hE with hE | hE
    · exact (mem_star_family.mp hE).1
    · exact hMU hE
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E hE
    simp only [H, Finset.mem_union] at hE
    rcases hE with hStar | hM
    · intro x hx
      by_cases hxv : x = v
      · subst x
        exact Finset.mem_insert_self v W
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩)
    · intro x hx
      by_cases hxv : x = v
      · subst x
        exact False.elim (hAvoid E hM hx)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩)
  have hMissing : missingStarFacets H W v r = ∅ := by
    ext T
    constructor
    · intro hT
      simp only [missingStarFacets, Finset.mem_filter] at hT
      obtain ⟨hT, hMiss⟩ := hT
      have hTp := Finset.mem_powersetCard.mp hT
      have hvT : v ∉ T := fun hv => hvW (hTp.1 hv)
      have hStar : insert v T ∈ starFamily v r := by
        apply mem_star_family.mpr
        constructor
        · rw [Finset.card_insert_of_notMem hvT, hTp.2]
          omega
        · exact Finset.mem_insert_self v T
      exact False.elim (hMiss (Finset.mem_union_left M hStar))
    · simp
  have hAdmissible : Admissible H := by
    change Admissible (starFamily v r ∪ M)
    exact star_plus_matching_admissible hr hMU hMatch hAvoid
  have hDisj : Disjoint (starFamily v r) M := by
    apply Finset.disjoint_left.mpr
    intro E hStar hM
    exact hAvoid E hM (mem_star_family.mp hStar).2
  have hCard : H.card = W.card.choose (r - 1) + W.card / r := by
    change (starFamily v r ∪ M).card = W.card.choose (r - 1) + W.card / r
    rw [Finset.card_union_of_disjoint hDisj,
      rank_r_star_card v r hr, hMsize]
  exact ⟨hAdmissible, hUniform, hSupport, hMissing, hCard⟩

/-- Exceptional construction data, including the unique missing facet P. -/
theorem one_missing_star_exceptional_pair_equality_data
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 5 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform r M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q)))
    (hMsize : M.card + 1 =
      (Finset.univ.erase v : Edge α).card / r) :
    let W : Edge α := Finset.univ.erase v
    let S : Family α := (starFamily v r).erase (insert v P)
    let B : Family α := insert (insert x P) (insert (insert x Q) M)
    let H : Family α := S ∪ B
    Admissible H ∧ Uniform r H ∧
      (∀ E ∈ H, E ⊆ insert v W) ∧
      missingStarFacets H W v r = {P} ∧
      Uniform (r - 1) (missingStarFacets H W v r) ∧
      (missingStarFacets H W v r).card = 1 ∧
      H.card = W.card.choose (r - 1) + W.card / r := by
  classical
  let W : Edge α := Finset.univ.erase v
  let S : Family α := (starFamily v r).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  let H : Family α := S ∪ B
  have hSpecialAvoid : ∀ E ∈ B, v ∉ E := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · simp [hvx, hvP]
    · simp [hvx, hvQ]
    · exact hMAvoid E hEM
  have hUniform : Uniform r H := by
    intro E hE
    simp only [H, Finset.mem_union] at hE
    rcases hE with hE | hE
    · exact (mem_star_family.mp (Finset.mem_erase.mp hE).2).1
    · change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
      simp only [Finset.mem_insert] at hE
      rcases hE with rfl | rfl | hEM
      · rw [Finset.card_insert_of_notMem hxP, hPcard]
        omega
      · rw [Finset.card_insert_of_notMem hxQ, hQcard]
        omega
      · exact hMU hEM
  have hSupport : ∀ E ∈ H, E ⊆ insert v W := by
    intro E hE y hy
    simp only [H, Finset.mem_union] at hE
    rcases hE with hES | hEB
    · have hStar := (Finset.mem_erase.mp hES).2
      by_cases hyv : y = v
      · subst y
        exact Finset.mem_insert_self v W
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ _⟩)
    · by_cases hyv : y = v
      · subst y
        exact False.elim (hSpecialAvoid E hEB hy)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ _⟩)
  have hMissing : missingStarFacets H W v r = {P} := by
    simpa [H, S, B, W] using
      JSP523.one_missing_star_exceptional_pair_missing_facets
        (by omega : 0 < r) hPcard hvx hvP hvQ hMAvoid
  have hMissingUniform : Uniform (r - 1) (missingStarFacets H W v r) := by
    intro T hT
    rw [hMissing] at hT
    have : T = P := Finset.mem_singleton.mp hT
    subst T
    exact hPcard
  have hMissingCard : (missingStarFacets H W v r).card = 1 := by
    rw [hMissing]
    simp
  have hAdmissible : Admissible H :=
    one_missing_star_exceptional_pair_admissible hr hPcard hQcard hPQ
      hxP hxQ hvx hvP hvQ hMU hMatch hMAvoid hMDisj
  have hCard : H.card = W.card.choose (r - 1) + W.card / r := by
    have hCount := JSP523.one_missing_star_exceptional_pair_card
      (by omega : 3 ≤ r) hPcard hQcard hPQ hxQ hvx hvP hvQ
      hMAvoid hMDisj
    have hMsize' : M.card + 1 = W.card / r := by
      simpa [W] using hMsize
    change H.card = W.card.choose (r - 1) + M.card + 1 at hCount
    omega
  exact ⟨hAdmissible, hUniform, hSupport, hMissing, hMissingUniform,
    hMissingCard, hCard⟩

/-- The second equality family of §IV.2.3 can be completed by a matching
on the remaining vertices when the outside order is `r-1` modulo `r`. -/
theorem exists_one_missing_star_exceptional_pair_extremal
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α}
    (hr : 5 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hSize : 2 * r - 1 ≤ (Finset.univ.erase v : Edge α).card)
    (hMod : (Finset.univ.erase v : Edge α).card % r = r - 1) :
    ∃ M : Family α,
      Admissible (((starFamily v r).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)) ∧
      (((starFamily v r).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)).card =
          ((Finset.univ.erase v : Edge α).card).choose (r - 1) +
            (Finset.univ.erase v : Edge α).card / r ∧
      M.biUnion id = (Finset.univ.erase v : Edge α) \ insert x (P ∪ Q) :=
  JSP523.exists_one_missing_star_exceptional_pair_extremal
    (by omega : 3 ≤ r) hPcard hQcard hPQ hxP hxQ hvx hvP hvQ hSize hMod

/-- The second §IV.2.3 equality family exists when the outside order is at
least `2r-1` and is `r-1` modulo `r`. -/
theorem exists_high_rank_exceptional_equality_family
    [Fintype α] (v : α) (r : ℕ) (hr : 5 ≤ r)
    (hSize : 2 * r - 1 ≤ (Finset.univ.erase v : Edge α).card)
    (hMod : (Finset.univ.erase v : Edge α).card % r = r - 1) :
    ∃ H : Family α,
      Admissible H ∧
      H.card = ((Finset.univ.erase v : Edge α).card).choose (r - 1) +
        (Finset.univ.erase v : Edge α).card / r :=
  JSP523.exists_exceptional_equality_family v r
    (by omega : 3 ≤ r) hSize hMod

end JSP523.Rank5
