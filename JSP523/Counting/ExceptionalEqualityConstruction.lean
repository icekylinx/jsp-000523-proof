import JSP523.Counting.LinearAdmissible
import JSP523.Counting.LinearNearStar
import JSP523.LowerConstruction

/-!
# Shared exceptional-pair equality construction

This is the admissibility argument for the second equality form in
§III.C.5 and §IV.2.3 of `paper/proof.pdf`. It works uniformly for `r ≥ 3`.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

private theorem exceptional_remainder_arithmetic (w r : ℕ)
    (hr : 0 < r) (hw : 2 * r - 1 ≤ w) (hmod : w % r = r - 1) :
    (w - (2 * r - 1)) % r = 0 ∧
      (w - (2 * r - 1)) / r + 1 = w / r := by
  have hDivision := Nat.mod_add_div w r
  have hW : w = r * (w / r) + (r - 1) := by omega
  have hR : r ≤ w := by omega
  have hQpos : 0 < w / r := Nat.div_pos hR hr
  obtain ⟨t, ht⟩ : ∃ t, w / r = t + 1 :=
    ⟨w / r - 1, by omega⟩
  have hW' : w = r * t + (2 * r - 1) := by
    calc
      w = r * (t + 1) + (r - 1) := by simpa [ht] using hW
      _ = r * t + (2 * r - 1) := by
        have hTwo : 2 * r - 1 = r + (r - 1) := by omega
        rw [hTwo]
        simp only [Nat.mul_add, mul_one]
        omega
  have hRcard : w - (2 * r - 1) = r * t := by omega
  constructor
  · simp [hRcard]
  · rw [hRcard, ht]
    rw [Nat.mul_div_cancel_left t hr]

/-- The two special outside edges avoid the star center. -/
theorem exceptional_special_subset_off_center
    [Fintype α] {v x : α} {P Q : Edge α}
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q) :
    insert x (P ∪ Q) ⊆ (Finset.univ.erase v : Edge α) := by
  intro y hy
  apply Finset.mem_erase.mpr
  constructor
  · intro hyv
    subst y
    rcases Finset.mem_insert.mp hy with hvx' | hy
    · exact hvx hvx'
    · rcases Finset.mem_union.mp hy with hyP | hyQ
      · exact hvP hyP
      · exact hvQ hyQ
  · exact Finset.mem_univ y

/-- The remaining vertices of an exceptional-pair equality construction
have a perfectly covering matching. The congruence `|W| ≡ r-1 (mod r)`
is exactly the equality condition in §§III.C.5 and IV.2.3. -/
theorem exists_exceptional_remainder_matching
    (W P Q : Edge α) (x : α) (r : ℕ)
    (hr : 0 < r) (hPcard : P.card = r - 1)
    (hQcard : Q.card = r - 1) (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hSpecialSub : insert x (P ∪ Q) ⊆ W)
    (hSize : 2 * r - 1 ≤ W.card)
    (hMod : W.card % r = r - 1) :
    ∃ M : Family α,
      IsMatching M ∧ Uniform r M ∧
      (∀ E ∈ M, E ⊆ W \ insert x (P ∪ Q)) ∧
      M.biUnion id = W \ insert x (P ∪ Q) ∧
      M.card + 1 = W.card / r := by
  classical
  let S : Edge α := insert x (P ∪ Q)
  let R : Edge α := W \ S
  have hxUnion : x ∉ P ∪ Q := by simp [hxP, hxQ]
  have hScard : S.card = 2 * r - 1 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem hxUnion,
      Finset.card_union_of_disjoint hPQ, hPcard, hQcard]
    omega
  have hRcard : R.card = W.card - (2 * r - 1) := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hSpecialSub, hScard]
  have hArith := exceptional_remainder_arithmetic W.card r hr hSize hMod
  have hRmod : R.card % r = 0 := by rw [hRcard]; exact hArith.1
  have hDiv : r ∣ R.card := Nat.dvd_of_mod_eq_zero hRmod
  obtain ⟨M, hMatch, hUniform, hSupport, hCover, hCard⟩ :=
    exists_perfect_uniform_matching R r hr hDiv
  refine ⟨M, hMatch, hUniform, ?_, ?_, ?_⟩
  · simpa [R, S] using hSupport
  · simpa [R, S] using hCover
  · rw [hCard, hRcard]
    exact hArith.2

/-- Every sufficiently large outside ground set contains the shared vertex
and two disjoint `(r-1)`-blocks of the second equality construction. -/
theorem exists_exceptional_pair_blocks
    (W : Edge α) (r : ℕ) (hr : 0 < r)
    (hSize : 2 * r - 1 ≤ W.card) :
    ∃ x : α, ∃ P Q : Edge α,
      x ∈ W ∧ P ⊆ W ∧ Q ⊆ W ∧
      P.card = r - 1 ∧ Q.card = r - 1 ∧
      Disjoint P Q ∧ x ∉ P ∧ x ∉ Q := by
  have hWpos : 0 < W.card := by omega
  obtain ⟨x, hxW⟩ := Finset.card_pos.mp hWpos
  let W₀ : Edge α := W.erase x
  have hW₀card : W₀.card + 1 = W.card := by
    simpa [W₀] using Finset.card_erase_add_one hxW
  obtain ⟨P, hPsub, hPcard⟩ :=
    Finset.exists_subset_card_eq (show r - 1 ≤ W₀.card by omega)
  let R : Edge α := W₀ \ P
  have hRcard : R.card = W₀.card - P.card := by
    simpa [R] using Finset.card_sdiff_of_subset hPsub
  obtain ⟨Q, hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq (show r - 1 ≤ R.card by omega)
  have hPsubW : P ⊆ W := hPsub.trans (Finset.erase_subset x W)
  have hQsubW : Q ⊆ W :=
    hQsub.trans (Finset.sdiff_subset.trans (Finset.erase_subset x W))
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro y hyP hyQ
    exact (Finset.mem_sdiff.mp (hQsub hyQ)).2 hyP
  have hxP : x ∉ P := by
    intro hx
    exact (Finset.notMem_erase x W) (hPsub hx)
  have hxQ : x ∉ Q := by
    intro hx
    exact (Finset.notMem_erase x W)
      ((hQsub.trans Finset.sdiff_subset) hx)
  exact ⟨x, P, Q, hxW, hPsubW, hQsubW,
    hPcard, hQcard, hPQ, hxP, hxQ⟩

/-- The two exceptional outside edges meet only in their shared vertex. -/
theorem exceptional_pair_intersection
    {P Q : Edge α} {x : α} (hPQ : Disjoint P Q) :
    insert x P ∩ insert x Q = {x} := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyP, hyQ⟩ := Finset.mem_inter.mp hy
    rcases Finset.mem_insert.mp hyP with rfl | hyP'
    · simp
    rcases Finset.mem_insert.mp hyQ with rfl | hyQ'
    · simp
    exact False.elim ((Finset.disjoint_left.mp hPQ) hyP' hyQ')
  · intro hy
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst y
    simp

/-- The opposite facet of the first exceptional edge is exactly P. -/
theorem exceptional_pair_difference
    {P Q : Edge α} {x : α}
    (hPQ : Disjoint P Q) (hxP : x ∉ P) :
    insert x P \ insert x Q = P := by
  ext y
  constructor
  · intro hy
    have h := Finset.mem_sdiff.mp hy
    rcases Finset.mem_insert.mp h.1 with hyx | hyP
    · exact False.elim (h.2 (hyx ▸ Finset.mem_insert_self x Q))
    · exact hyP
  · intro hyP
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_insert_of_mem hyP, ?_⟩
    intro hyQ
    rcases Finset.mem_insert.mp hyQ with hyx | hyQ'
    · exact hxP (hyx ▸ hyP)
    · exact (Finset.disjoint_left.mp hPQ) hyP hyQ'

/-- Removing one star edge and adding two exceptional outside edges changes
the star-plus-matching count by one, in every rank at least three. -/
theorem one_missing_star_exceptional_pair_card
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 3 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    (((starFamily v r).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M)).card =
      ((Finset.univ.erase v : Edge α).card).choose (r - 1) + M.card + 1 := by
  classical
  let S : Family α := (starFamily v r).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  have hStarMem : insert v P ∈ starFamily v r := by
    apply mem_starFamily.mpr
    constructor
    · rw [Finset.card_insert_of_notMem hvP, hPcard]
      omega
    · exact Finset.mem_insert_self v P
  have hSCard : S.card + 1 =
      ((Finset.univ.erase v : Edge α).card).choose (r - 1) := by
    have hErase := Finset.card_erase_add_one hStarMem
    rw [rank_r_star_card v r (by omega)] at hErase
    exact hErase
  have hQcard' : (insert x Q).card = r := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
    omega
  have hSpecialNe : insert x P ≠ insert x Q := by
    intro hEq
    have hInter := exceptional_pair_intersection (x := x) hPQ
    rw [hEq, Finset.inter_self] at hInter
    have hCard := congrArg Finset.card hInter
    simp [hQcard'] at hCard
    omega
  have hPnotM : insert x P ∉ M := by
    intro hPM
    have hD := hMDisj (insert x P) hPM
    exact (Finset.disjoint_left.mp hD)
      (Finset.mem_insert_self x P)
      (Finset.mem_insert_self x (P ∪ Q))
  have hQnotM : insert x Q ∉ M := by
    intro hQM
    have hD := hMDisj (insert x Q) hQM
    exact (Finset.disjoint_left.mp hD)
      (Finset.mem_insert_self x Q)
      (Finset.mem_insert_self x (P ∪ Q))
  have hPnotTail : insert x P ∉ insert (insert x Q) M := by
    simp only [Finset.mem_insert]
    exact not_or.mpr ⟨hSpecialNe, hPnotM⟩
  have hBCard : B.card = M.card + 2 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hPnotTail,
      Finset.card_insert_of_notMem hQnotM]
  have hSBDisj : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro E hES hEB
    have hvE : v ∈ E :=
      (mem_starFamily.mp (Finset.mem_erase.mp hES).2).2
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hEB
    simp only [Finset.mem_insert] at hEB
    rcases hEB with rfl | rfl | hEM
    · simp [hvx, hvP] at hvE
    · simp [hvx, hvQ] at hvE
    · exact hMAvoid E hEM hvE
  have hUnionCard := Finset.card_union_of_disjoint hSBDisj
  change (S ∪ B).card = S.card + B.card at hUnionCard
  change (S ∪ B).card =
    ((Finset.univ.erase v : Edge α).card).choose (r - 1) + M.card + 1
  omega

/-- The exceptional-pair construction is admissible at every rank `r ≥ 3`.
The assumptions encode disjoint `(r-1)`-blocks P,Q, their common external
vertex x, and a matching disjoint from their union. -/
theorem one_missing_star_exceptional_pair_admissible
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 3 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMU : Uniform r M) (hMatch : IsMatching M)
    (hMAvoid : ∀ E ∈ M, v ∉ E)
    (hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q))) :
    Admissible (((starFamily v r).erase (insert v P)) ∪
      insert (insert x P) (insert (insert x Q) M) ) := by
  let S : Family α := (starFamily v r).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  have hPcard' : (insert x P).card = r := by
    rw [Finset.card_insert_of_notMem hxP, hPcard]
    omega
  have hQcard' : (insert x Q).card = r := by
    rw [Finset.card_insert_of_notMem hxQ, hQcard]
    omega
  have hSU : Uniform r S := by
    intro E hE
    exact (mem_starFamily.mp (Finset.mem_erase.mp hE).2).1
  have hBU : Uniform r B := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · exact hPcard'
    · exact hQcard'
    · exact hMU hEM
  have hCenter : ∀ E ∈ S, v ∈ E := by
    intro E hE
    exact (mem_starFamily.mp (Finset.mem_erase.mp hE).2).2
  have hAvoid : ∀ E ∈ B, v ∉ E := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · simp [hvx, hvP]
    · simp [hvx, hvQ]
    · exact hMAvoid E hEM
  have hSpecPDisj : ∀ E ∈ M, Disjoint (insert x P) E := by
    intro E hEM
    apply Finset.disjoint_left.mpr
    intro y hySpec hyE
    have hyBig : y ∈ insert x (P ∪ Q) := by
      rcases Finset.mem_insert.mp hySpec with rfl | hyP
      · simp
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left Q hyP)
    exact (Finset.disjoint_left.mp (hMDisj E hEM)) hyE hyBig
  have hSpecQDisj : ∀ E ∈ M, Disjoint (insert x Q) E := by
    intro E hEM
    apply Finset.disjoint_left.mpr
    intro y hySpec hyE
    have hyBig : y ∈ insert x (P ∪ Q) := by
      rcases Finset.mem_insert.mp hySpec with rfl | hyQ
      · simp
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right P hyQ)
    exact (Finset.disjoint_left.mp (hMDisj E hEM)) hyE hyBig
  have hSpecialOne : (insert x P ∩ insert x Q).card ≤ 1 := by
    rw [exceptional_pair_intersection hPQ]
    simp
  have hSpecialOneSym : (insert x Q ∩ insert x P).card ≤ 1 := by
    simpa only [Finset.inter_comm] using hSpecialOne
  have hBLin : LinearFamily B := by
    intro E F hE hF hne
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    change F ∈ insert (insert x P) (insert (insert x Q) M) at hF
    simp only [Finset.mem_insert] at hE hF
    rcases hE with rfl | rfl | hEM <;>
      rcases hF with rfl | rfl | hFM
    · exact False.elim (hne rfl)
    · exact hSpecialOne
    · have hD := hSpecPDisj F hFM
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · exact hSpecialOneSym
    · exact False.elim (hne rfl)
    · have hD := hSpecQDisj F hFM
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · have hD := (hSpecPDisj E hEM).symm
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · have hD := (hSpecQDisj E hEM).symm
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
    · have hD := hMatch hEM hFM hne
      rw [Finset.disjoint_iff_inter_eq_empty] at hD
      simp [hD]
  have hMissingStar : insert v P ∉ S := Finset.notMem_erase _ _
  have hMissing : ∀ E ∈ B, ∀ F ∈ B, E ≠ F →
      ¬ Disjoint E F →
        insert v (E \ F) ∉ S ∨ insert v (F \ E) ∉ S := by
    intro E hE F hF hne hNonDisj
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    change F ∈ insert (insert x P) (insert (insert x Q) M) at hF
    simp only [Finset.mem_insert] at hE hF
    rcases hE with rfl | rfl | hEM <;>
      rcases hF with rfl | rfl | hFM
    · exact False.elim (hne rfl)
    · left
      rw [exceptional_pair_difference hPQ hxP]
      exact hMissingStar
    · exact False.elim (hNonDisj (hSpecPDisj F hFM))
    · right
      rw [exceptional_pair_difference hPQ hxP]
      exact hMissingStar
    · exact False.elim (hne rfl)
    · exact False.elim (hNonDisj (hSpecQDisj F hFM))
    · exact False.elim (hNonDisj (hSpecPDisj E hEM).symm)
    · exact False.elim (hNonDisj (hSpecQDisj E hEM).symm)
    · exact False.elim (hNonDisj (hMatch hEM hFM hne))
  change Admissible (S ∪ B)
  exact star_plus_linear_outside_admissible hr
    hSU hBU hBLin hCenter hAvoid hMissing

/-- The exceptional-pair construction has exactly the prescribed missing
star facet. This is the common converse interface for §§III.C.5 and IV.2.3. -/
theorem one_missing_star_exceptional_pair_missing_facets
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α} {M : Family α}
    (hr : 0 < r) (hPcard : P.card = r - 1)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hMAvoid : ∀ E ∈ M, v ∉ E) :
    missingStarFacets
      (((starFamily v r).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M))
      (Finset.univ.erase v) v r = {P} := by
  classical
  let W : Edge α := Finset.univ.erase v
  let S : Family α := (starFamily v r).erase (insert v P)
  let B : Family α := insert (insert x P) (insert (insert x Q) M)
  have hvW : v ∉ W := Finset.notMem_erase v Finset.univ
  have hPsub : P ⊆ W := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨by
      intro h
      exact hvP (h ▸ hy), Finset.mem_univ _⟩
  have hPfacet : P ∈ W.powersetCard (r - 1) :=
    Finset.mem_powersetCard.mpr ⟨hPsub, hPcard⟩
  have hSpecialAvoid : ∀ E ∈ B, v ∉ E := by
    intro E hE
    change E ∈ insert (insert x P) (insert (insert x Q) M) at hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | rfl | hEM
    · simp [hvx, hvP]
    · simp [hvx, hvQ]
    · exact hMAvoid E hEM
  have hNotP : insert v P ∉ B := by
    intro h
    exact (hSpecialAvoid (insert v P) h) (Finset.mem_insert_self v P)
  change missingStarFacets (S ∪ B) W v r = {P}
  ext T
  simp only [missingStarFacets, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hT, hMiss⟩
    by_cases hTP : T = P
    · exact hTP
    · have hTsub := (Finset.mem_powersetCard.mp hT).1
      have hvT : v ∉ T := fun hv => hvW (hTsub hv)
      have hStar : insert v T ∈ starFamily v r := by
        apply mem_starFamily.mpr
        constructor
        · rw [Finset.card_insert_of_notMem hvT,
            (Finset.mem_powersetCard.mp hT).2]
          omega
        · exact Finset.mem_insert_self v T
      have hNotErase : insert v T ≠ insert v P := by
        intro hEq
        have hErase := congrArg (fun E : Edge α => E.erase v) hEq
        have hTP' : T = P := by
          simpa [Finset.erase_insert hvT, Finset.erase_insert hvP] using hErase
        exact hTP hTP'
      have hInS : insert v T ∈ S :=
        Finset.mem_erase.mpr ⟨hNotErase, hStar⟩
      exact False.elim (hMiss (Finset.mem_union_left B hInS))
  · intro hTP
    subst T
    refine ⟨hPfacet, ?_⟩
    intro hH
    simp only [Finset.mem_union] at hH
    rcases hH with hS | hB
    · exact (Finset.mem_erase.mp hS).1 rfl
    · exact hNotP hB

/-- For every rank at least three, the exceptional-pair family exists at
the equality residue and covers every ordinary outside vertex. -/
theorem exists_one_missing_star_exceptional_pair_extremal
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α}
    (hr : 3 ≤ r)
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
      M.biUnion id = (Finset.univ.erase v : Edge α) \ insert x (P ∪ Q) := by
  classical
  let W : Edge α := Finset.univ.erase v
  have hSpecialSub : insert x (P ∪ Q) ⊆ W :=
    exceptional_special_subset_off_center hvx hvP hvQ
  obtain ⟨M, hMatch, hMU, hSupport, hCover, hMsize⟩ :=
    exists_exceptional_remainder_matching W P Q x r
      (by omega) hPcard hQcard hPQ hxP hxQ hSpecialSub
      (by simpa [W] using hSize) (by simpa [W] using hMod)
  have hMAvoid : ∀ E ∈ M, v ∉ E := by
    intro E hE hvE
    have hInW : v ∈ W :=
      ((hSupport E hE).trans Finset.sdiff_subset) hvE
    exact (Finset.notMem_erase v Finset.univ) hInW
  have hMDisj : ∀ E ∈ M, Disjoint E (insert x (P ∪ Q)) := by
    intro E hE
    apply Finset.disjoint_left.mpr
    intro y hyE hySpecial
    exact (Finset.mem_sdiff.mp (hSupport E hE hyE)).2 hySpecial
  have hAdm := one_missing_star_exceptional_pair_admissible
    hr hPcard hQcard hPQ hxP hxQ hvx hvP hvQ
    hMU hMatch hMAvoid hMDisj
  have hCount := one_missing_star_exceptional_pair_card
    hr hPcard hQcard hPQ hxQ hvx hvP hvQ hMAvoid hMDisj
  have hMsize' : M.card + 1 =
      (Finset.univ.erase v : Edge α).card / r := by
    simpa [W] using hMsize
  have hCard :
      (((starFamily v r).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)).card =
          ((Finset.univ.erase v : Edge α).card).choose (r - 1) +
            (Finset.univ.erase v : Edge α).card / r := by
    omega
  exact ⟨M, hAdm, hCard, by simpa [W] using hCover⟩

/-- The chosen exceptional family also has exactly its prescribed missing
star facet, completing the converse data for the equality classification. -/
theorem exists_exceptional_pair_equality_data
    [Fintype α]
    {r : ℕ} {v x : α} {P Q : Edge α}
    (hr : 3 ≤ r)
    (hPcard : P.card = r - 1) (hQcard : Q.card = r - 1)
    (hPQ : Disjoint P Q)
    (hxP : x ∉ P) (hxQ : x ∉ Q)
    (hvx : v ≠ x) (hvP : v ∉ P) (hvQ : v ∉ Q)
    (hSize : 2 * r - 1 ≤ (Finset.univ.erase v : Edge α).card)
    (hMod : (Finset.univ.erase v : Edge α).card % r = r - 1) :
    ∃ M : Family α,
      let H : Family α := ((starFamily v r).erase (insert v P)) ∪
        insert (insert x P) (insert (insert x Q) M)
      Admissible H ∧
      H.card = ((Finset.univ.erase v : Edge α).card).choose (r - 1) +
        (Finset.univ.erase v : Edge α).card / r ∧
      M.biUnion id = (Finset.univ.erase v : Edge α) \ insert x (P ∪ Q) ∧
      missingStarFacets H (Finset.univ.erase v) v r = {P} := by
  obtain ⟨M, hAdm, hCard, hCover⟩ :=
    exists_one_missing_star_exceptional_pair_extremal
      hr hPcard hQcard hPQ hxP hxQ hvx hvP hvQ hSize hMod
  have hMAvoid : ∀ E ∈ M, v ∉ E := by
    intro E hE hvE
    have hvUnion : v ∈ M.biUnion id :=
      Finset.mem_biUnion.mpr ⟨E, hE, hvE⟩
    rw [hCover] at hvUnion
    exact (Finset.notMem_erase v Finset.univ)
      (Finset.sdiff_subset hvUnion)
  refine ⟨M, hAdm, hCard, hCover, ?_⟩
  exact one_missing_star_exceptional_pair_missing_facets
    (by omega : 0 < r) hPcard hvx hvP hvQ hMAvoid

/-- The second equality family exists on every sufficiently large ground
set in the residue class `|W| ≡ r-1 (mod r)`. -/
theorem exists_exceptional_equality_family
    [Fintype α] (v : α) (r : ℕ) (hr : 3 ≤ r)
    (hSize : 2 * r - 1 ≤ (Finset.univ.erase v : Edge α).card)
    (hMod : (Finset.univ.erase v : Edge α).card % r = r - 1) :
    ∃ H : Family α,
      Admissible H ∧
      H.card = ((Finset.univ.erase v : Edge α).card).choose (r - 1) +
        (Finset.univ.erase v : Edge α).card / r := by
  let W : Edge α := Finset.univ.erase v
  obtain ⟨x, P, Q, hxW, hPsubW, hQsubW, hPcard, hQcard, hPQ, hxP, hxQ⟩ :=
    exists_exceptional_pair_blocks W r (by omega) (by simpa [W] using hSize)
  have hvx : v ≠ x := (Finset.mem_erase.mp hxW).1.symm
  have hvP : v ∉ P := by
    intro hv
    exact (Finset.notMem_erase v Finset.univ) (hPsubW hv)
  have hvQ : v ∉ Q := by
    intro hv
    exact (Finset.notMem_erase v Finset.univ) (hQsubW hv)
  obtain ⟨M, hAdm, hCard, _⟩ :=
    exists_one_missing_star_exceptional_pair_extremal
      hr hPcard hQcard hPQ hxP hxQ hvx hvP hvQ hSize hMod
  exact ⟨((starFamily v r).erase (insert v P)) ∪
    insert (insert x P) (insert (insert x Q) M), hAdm, hCard⟩

/-- The exceptional equality family in the manuscript's `n`-vertex
notation, at every rank at least three. -/
theorem exists_exceptional_equality_fin
    (n r : ℕ) (hn : 0 < n) (hr : 3 ≤ r)
    (hSize : 2 * r - 1 ≤ n - 1)
    (hMod : (n - 1) % r = r - 1) :
    ∃ H : Family (Fin n),
      Admissible H ∧
      H.card = (n - 1).choose (r - 1) + (n - 1) / r := by
  let v : Fin n := ⟨0, hn⟩
  simpa [v] using
    exists_exceptional_equality_family v r hr
      (by simpa [v] using hSize) (by simpa [v] using hMod)

end JSP523
