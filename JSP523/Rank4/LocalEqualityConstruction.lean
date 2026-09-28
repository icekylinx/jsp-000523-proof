import JSP523.Counting.ExceptionalEqualityConstruction
import JSP523.LowerConstruction
import JSP523.Rank4.LocalExactTrade

/-!
# Admissibility of the rank-four equality constructions

The converse direction of §III.C.5 needs a slightly more general fact than
the complete-star plus matching construction.  A linear outside family may
have intersecting pairs if the star edge opposite every such pair is
missing.  The following finite theorem states this exact condition.
-/

namespace JSP523.Rank4

variable {α : Type*}

variable [DecidableEq α]

/-- The rank-four equality-construction criterion from the shared all-rank
admissibility lemma, used for both forms in §III.C.5. -/
theorem star_plus_linear_outside_admissible
    {S B : Family α} {v : α}
    (hSUniform : Uniform 4 S) (hBUniform : Uniform 4 B)
    (hLinear : LinearFamily B)
    (hCenter : ∀ T ∈ S, v ∈ T)
    (hAvoid : ∀ T ∈ B, v ∉ T)
    (hMissing : ∀ E ∈ B, ∀ F ∈ B, E ≠ F →
      ¬ Disjoint E F →
        insert v (E \ F) ∉ S ∨ insert v (F \ E) ∉ S) :
    Admissible (S ∪ B) :=
  JSP523.star_plus_linear_outside_admissible (by omega : 3 ≤ 4)
    hSUniform hBUniform hLinear hCenter hAvoid hMissing

/-- The two exceptional outside edges meet only in their shared vertex. -/
theorem exceptional_pair_intersection
    {P Q : Edge α} {x : α} (hPQ : Disjoint P Q) :
    insert x P ∩ insert x Q = {x} :=
  JSP523.exceptional_pair_intersection hPQ

/-- The opposite facet of the first exceptional edge is exactly P. -/
theorem exceptional_pair_difference
    {P Q : Edge α} {x : α}
    (hPQ : Disjoint P Q) (hxP : x ∉ P) :
    insert x P \ insert x Q = P :=
  JSP523.exceptional_pair_difference hPQ hxP

/-- The second equality family of §III.C.5 is admissible by the
shared exceptional-pair construction. -/
theorem one_missing_star_exceptional_pair_admissible
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform 4 M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    Admissible
      (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)) :=
  JSP523.one_missing_star_exceptional_pair_admissible
    (by omega : 3 ≤ 4) (by simpa using hPcard) (by simpa using hQcard)
    hPQ hxP hxQ hvx hvP hvQ hMU hMatch hMAvoid hMDisj

/-- The rank-four exceptional family has exactly the deleted triple as a
missing star facet. -/
theorem one_missing_star_exceptional_pair_missing_triples
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMAvoid : ∀ E ∈ M, v ∉ E) :
    missingStarTriples
      (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M))
      (Finset.univ.erase v) v = {P} := by
  simpa [missingStarTriples, missingStarFacets] using
    JSP523.one_missing_star_exceptional_pair_missing_facets
      (r := 4) (by omega : 0 < 4) (by simpa using hPcard)
      hvx hvP hvQ hMAvoid

/-- The number of four-edges in a complete star is the number of outside
triples. -/
theorem rank_four_star_card
    [Fintype α] (v : α) :
    (starFamily v 4).card =
      ((Finset.univ.erase v : Edge α).card).choose 3 := by
  simpa using JSP523.rank_r_star_card v 4 (by omega)

/-- The complete-star plus maximum outside matching equality family. -/
theorem complete_star_max_matching_extremal
    [Fintype α] {v : α} {M : Family α}
    (hMU : Uniform 4 M) (hMatch : IsMatching M)
    (hAvoid : ∀ E ∈ M, v ∉ E)
    (hMsize : M.card = (Finset.univ.erase v : Edge α).card / 4) :
    Admissible (starFamily v 4 ∪ M) ∧
      (starFamily v 4 ∪ M).card =
        ((Finset.univ.erase v : Edge α).card).choose 3 +
          (Finset.univ.erase v : Edge α).card / 4 := by
  have hAdmissible : Admissible (starFamily v 4 ∪ M) := by
    simpa only [starPlusMatching] using
      star_plus_matching_admissible (by omega : 0 < 4)
        hMU hMatch hAvoid
  have hDisj : Disjoint (starFamily v 4) M := by
    apply Finset.disjoint_left.mpr
    intro E hStar hM
    exact hAvoid E hM (mem_starFamily.mp hStar).2
  constructor
  · exact hAdmissible
  · rw [Finset.card_union_of_disjoint hDisj,
      rank_four_star_card, hMsize]

/-- The cardinality of the one-missing-star construction, expressed in
terms of its auxiliary matching. -/
theorem one_missing_star_exceptional_pair_card
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (_hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    (((starFamily v 4).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M)).card =
      ((Finset.univ.erase v : Edge α).card).choose 3 + M.card + 1 :=
  JSP523.one_missing_star_exceptional_pair_card
    (by omega : 3 ≤ 4) hPcard (by simpa using hQcard)
    hPQ hxQ hvx hvP hvQ hMAvoid hMDisj

/-- The second equality construction attains the rank-four count when its
auxiliary matching has one fewer block than a maximum outside matching. -/
theorem one_missing_star_exceptional_pair_extremal
    [Fintype α]
    {v x : α} {P Q : Edge α} {M : Family α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform 4 M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q)))
    (hMsize : M.card + 1 =
      (Finset.univ.erase v : Edge α).card / 4) :
    Admissible
      (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)) ∧
    (((starFamily v 4).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M)).card =
      ((Finset.univ.erase v : Edge α).card).choose 3 +
        (Finset.univ.erase v : Edge α).card / 4 := by
  constructor
  · exact one_missing_star_exceptional_pair_admissible hPcard hQcard
      hPQ hxP hxQ hvx hvP hvQ hMU hMatch hMAvoid hMDisj
  · rw [one_missing_star_exceptional_pair_card hPcard hQcard
      hPQ hxP hxQ hvx hvP hvQ hMAvoid hMDisj]
    omega

/-- The second equality form in §III.C.5 exists for specified special
vertices and triples whenever the outside order has the required residue. -/
theorem exists_one_missing_star_exceptional_pair_extremal
    [Fintype α]
    {v x : α} {P Q : Edge α}
    (hPcard : P.card = 3) (hQcard : Q.card = 3)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hSize : 7 ≤ (Finset.univ.erase v : Edge α).card)
    (hMod : (Finset.univ.erase v : Edge α).card % 4 = 3) :
    ∃ M : Family α,
      Admissible (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)) ∧
      (((starFamily v 4).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)).card =
        ((Finset.univ.erase v : Edge α).card).choose 3 +
          (Finset.univ.erase v : Edge α).card / 4 ∧
      M.biUnion id = (Finset.univ.erase v : Edge α) \ insert x (P ∪ Q) := by
  simpa using JSP523.exists_one_missing_star_exceptional_pair_extremal
    (r := 4) (by omega : 3 ≤ 4) (by simpa using hPcard)
    (by simpa using hQcard) hPQ hxP hxQ hvx hvP hvQ hSize hMod

/-- The second §III.C.5 equality family exists when at least seven outside
vertices are available and their number is three modulo four. -/
theorem exists_rank_four_exceptional_equality_family
    [Fintype α] (v : α)
    (hSize : 7 ≤ (Finset.univ.erase v : Edge α).card)
    (hMod : (Finset.univ.erase v : Edge α).card % 4 = 3) :
    ∃ H : Family α,
      Admissible H ∧
      H.card = ((Finset.univ.erase v : Edge α).card).choose 3 +
        (Finset.univ.erase v : Edge α).card / 4 := by
  simpa using JSP523.exists_exceptional_equality_family v 4
    (by omega : 3 ≤ 4) hSize hMod

end JSP523.Rank4
