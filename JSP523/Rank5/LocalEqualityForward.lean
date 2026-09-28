import JSP523.Counting.LinearNearStar
import JSP523.Counting.PrefixCommonSystem
import JSP523.Matching
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Forward equality consequences for one missing star facet

This is the all-rank degree part of the `q = 1` equality argument in
§IV.2.3. It derives the exceptional vertex and its missing-facet edge from
actual outside edges, rather than adding a geometric hypothesis.
-/

namespace JSP523.Rank5

open JSP523

variable {α : Type*} [DecidableEq α]

def equalityOutsideEdgesAt (B : Family α) (a : α) : Family α :=
  B.filter fun E => a ∈ E

def equalityPresentOutsideAt (H B : Family α) (v a : α) : Family α :=
  (equalityOutsideEdgesAt B a).filter fun E => insert v (E.erase a) ∈ H

def equalityMissingOutsideAt (H B : Family α) (v a : α) : Family α :=
  (equalityOutsideEdgesAt B a).filter fun E => insert v (E.erase a) ∉ H

def equalityMissingVertices (H B : Family α) (W : Edge α) (v : α) : Edge α :=
  W.filter fun a => (equalityMissingOutsideAt H B v a).Nonempty

private theorem equality_present_edges_same
    {H B : Family α} {W E F : Edge α} {v a : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ G ∈ B, G ⊆ W) (hvW : v ∉ W)
    (hE : E ∈ B) (hF : F ∈ B) (haE : a ∈ E) (haF : a ∈ F)
    (hStarE : insert v (E.erase a) ∈ H)
    (hStarF : insert v (F.erase a) ∈ H) : E = F := by
  by_contra hEF
  have haW : a ∈ W := hW E hE haE
  have hav : a ≠ v := fun h => hvW (h ▸ haW)
  have hTnon : (E.erase a).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_erase_add_one haE
    rw [hU hE] at hc
    omega
  have hSnon : (F.erase a).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_erase_add_one haF
    rw [hU hF] at hc
    omega
  have hTS : Disjoint (E.erase a) (F.erase a) := by
    apply Finset.disjoint_left.mpr
    intro x hxE hxF
    have hxa : x ≠ a := Finset.ne_of_mem_erase hxE
    have hTwo : ({a, x} : Edge α) ⊆ E ∩ F := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact Finset.mem_inter.mpr ⟨haE, haF⟩
      · have hxy : y = x := Finset.mem_singleton.mp hys
        exact Finset.mem_inter.mpr
          ⟨hxy ▸ Finset.mem_of_mem_erase hxE,
           hxy ▸ Finset.mem_of_mem_erase hxF⟩
    have hCard := Finset.card_le_card hTwo
    have hPair : ({a, x} : Edge α).card = 2 := Finset.card_pair hxa.symm
    have hOne := hLin hE hF hEF
    omega
  have hQuad := prefix_switch_forbidden (by simp) (by simp) hTnon hSnon
    (Finset.disjoint_singleton.mpr hav)
    (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase a E))
    (Finset.disjoint_singleton_right.mpr (by
      intro hvT
      exact hvW (hW E hE (Finset.mem_of_mem_erase hvT))))
    (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase a F))
    (Finset.disjoint_singleton_right.mpr (by
      intro hvS
      exact hvW (hW F hF (Finset.mem_of_mem_erase hvS)))) hTS
  have hEeq : ({a} : Edge α) ∪ E.erase a = E := by
    simpa [Finset.singleton_union] using (Finset.insert_erase haE)
  have hFeq : ({a} : Edge α) ∪ F.erase a = F := by
    simpa [Finset.singleton_union] using (Finset.insert_erase haF)
  have hQuad' : ForbiddenQuad E (insert v (F.erase a)) F (insert v (E.erase a)) := by
    simpa only [hEeq, hFeq, Finset.singleton_union] using hQuad
  exact hH (hBH hE) hStarF (hBH hF) hStarE hQuad'

private theorem equality_present_card_le_one
    {H B : Family α} {W : Edge α} {v a : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W) :
    (equalityPresentOutsideAt H B v a).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro E hE F hF
  have hE' := Finset.mem_filter.mp hE
  have hF' := Finset.mem_filter.mp hF
  have hEa := Finset.mem_filter.mp hE'.1
  have hFa := Finset.mem_filter.mp hF'.1
  exact equality_present_edges_same hH hBH hU hLin hr hW hvW
    hEa.1 hFa.1 hEa.2 hFa.2 hE'.2 hF'.2

private theorem equality_missing_opposite_unique
    {H B : Family α} {W P : Edge α} {v a : α} {r : ℕ}
    (hU : Uniform r B) (hW : ∀ E ∈ B, E ⊆ W)
    (hMissing : missingStarFacets H W v r = {P})
    {E : Edge α} (hE : E ∈ equalityMissingOutsideAt H B v a) :
    E.erase a = P ∧ E = insert a P := by
  have hE' := Finset.mem_filter.mp hE
  have hEa := Finset.mem_filter.mp hE'.1
  have hCard : (E.erase a).card = r - 1 := by
    have hc := Finset.card_erase_add_one hEa.2
    rw [hU hEa.1] at hc
    omega
  have hSub : E.erase a ⊆ W :=
    (Finset.erase_subset a E).trans (hW E hEa.1)
  have hFacet : E.erase a ∈ missingStarFacets H W v r := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hSub, hCard⟩, hE'.2⟩
  rw [hMissing] at hFacet
  have hEq : E.erase a = P := by simpa using hFacet
  exact ⟨hEq, by rw [← Finset.insert_erase hEa.2, hEq]⟩

private theorem equality_missing_vertices_card_le_one
    {H B : Family α} {W P : Edge α} {v : α} {r : ℕ}
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hMissing : missingStarFacets H W v r = {P})
    (hPcard : P.card = r - 1) :
    (equalityMissingVertices H B W v).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hab
  obtain ⟨E, hE⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨F, hF⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨hEP, hEeq⟩ := equality_missing_opposite_unique hU hW hMissing hE
  obtain ⟨hFP, hFeq⟩ := equality_missing_opposite_unique hU hW hMissing hF
  have hEF : E ≠ F := by
    intro h
    have haP : a ∉ P := by rw [← hEP]; exact Finset.notMem_erase a E
    have hbP : b ∉ P := by rw [← hFP]; exact Finset.notMem_erase b F
    have haF : a ∈ F := h ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    rw [hFeq] at haF
    simp only [Finset.mem_insert] at haF
    rcases haF with h | h
    · exact hab h
    · exact haP h
  have hSub : P ⊆ E ∩ F := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨hEeq ▸ Finset.mem_insert_of_mem hx,
       hFeq ▸ Finset.mem_insert_of_mem hx⟩
  have hPle := Finset.card_le_card hSub
  have hOne := hLin (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
    (Finset.mem_filter.mp (Finset.mem_filter.mp hF).1).1 hEF
  have hContr : r - 1 ≤ 1 := by
    rw [← hPcard]
    exact hPle.trans hOne
  omega

/-- The one-hole equality count forces a unique exceptional vertex, the edge
completing the missing facet, degree two there, and degree one everywhere
else. This is stated for actual finite outside edges at arbitrary rank. -/
theorem one_missing_equality_vertex_degrees
    {H B : Family α} {W P : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarFacets H W v r = {P})
    (hPcard : P.card = r - 1)
    (hCount : r * B.card = W.card + 1) :
    ∃ x ∈ W, x ∉ P ∧ insert x P ∈ B ∧
      (equalityOutsideEdgesAt B x).card = 2 ∧
      ∀ y ∈ W, y ≠ x → (equalityOutsideEdgesAt B y).card = 1 := by
  classical
  let X := equalityMissingVertices H B W v
  have hXle : X.card ≤ 1 :=
    equality_missing_vertices_card_le_one hU hLin hr hW hMissing hPcard
  have hMunique {a : α} (ha : a ∈ X) {E F : Edge α}
      (hE : E ∈ equalityMissingOutsideAt H B v a)
      (hF : F ∈ equalityMissingOutsideAt H B v a) : E = F := by
    have hEeq := equality_missing_opposite_unique hU hW hMissing hE
    have hFeq := equality_missing_opposite_unique hU hW hMissing hF
    exact hEeq.2.trans hFeq.2.symm
  have hMissingLe : ∀ a ∈ W,
      (equalityMissingOutsideAt H B v a).card ≤
        if a ∈ X then 1 else 0 := by
    intro a ha
    by_cases hax : a ∈ X
    · simp [hax]
      apply Finset.card_le_one.mpr
      intro E hE F hF
      exact hMunique (a := a) hax hE hF
    · have hEmpty : equalityMissingOutsideAt H B v a = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hn
        exact hax (Finset.mem_filter.mpr ⟨ha, hn⟩)
      simp [hax, hEmpty]
  have hDegreeBound : ∀ a ∈ W,
      (equalityOutsideEdgesAt B a).card ≤ 1 + if a ∈ X then 1 else 0 := by
    intro a ha
    have hUnion : equalityOutsideEdgesAt B a =
        equalityPresentOutsideAt H B v a ∪ equalityMissingOutsideAt H B v a := by
      ext E
      simp only [equalityOutsideEdgesAt, equalityPresentOutsideAt,
        equalityMissingOutsideAt, Finset.mem_filter, Finset.mem_union]
      tauto
    rw [hUnion]
    have hp := equality_present_card_le_one (a := a) hH hBH hU hLin hr hW hvW
    have hm := hMissingLe a ha
    have hc := Finset.card_union_le
      (equalityPresentOutsideAt H B v a) (equalityMissingOutsideAt H B v a)
    omega
  have hInc : (∑ a ∈ W, (equalityOutsideEdgesAt B a).card) = r * B.card := by
    classical
    calc
      _ = ∑ E ∈ B, E.card := by
        simp_rw [equalityOutsideEdgesAt, Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro E hE
        have hFilter : W.filter (fun a => a ∈ E) = E := by
          ext a
          simp [hW E hE]
        rw [← Finset.card_filter, hFilter]
      _ = ∑ _E ∈ B, r := by
        apply Finset.sum_congr rfl
        intro E hE
        exact hU hE
      _ = r * B.card := by simp [Finset.sum_const, mul_comm]
  have hIndicator : (∑ a ∈ W, (if a ∈ X then 1 else 0)) = X.card := by
    rw [← Finset.card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun ha => Finset.mem_filter.mp ha |>.1)
  have hUpper : (∑ a ∈ W, (1 + if a ∈ X then 1 else 0)) = W.card + X.card := by
    rw [Finset.sum_add_distrib, hIndicator]
    simp
  have hSumLe := Finset.sum_le_sum hDegreeBound
  rw [hInc, hCount, hUpper] at hSumLe
  have hXeq : X.card = 1 := by omega
  obtain ⟨x, hxX⟩ := Finset.card_eq_one.mp hXeq
  have hx : x ∈ X := by simp [hxX]
  have hxW : x ∈ W := (Finset.mem_filter.mp hx).1
  obtain ⟨E, hE⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hEP, hEeq⟩ := equality_missing_opposite_unique hU hW hMissing hE
  have hxP : x ∉ P := by rw [← hEP]; exact Finset.notMem_erase x E
  have hPx : insert x P ∈ B := by
    rw [← hEeq]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
  have hEqTerms : ∀ a ∈ W,
      (equalityOutsideEdgesAt B a).card = 1 + if a ∈ X then 1 else 0 := by
    apply Finset.sum_eq_sum_iff_of_le hDegreeBound |>.mp
    rw [hInc, hCount, hUpper, hXeq]
  refine ⟨x, hxW, hxP, hPx, ?_, ?_⟩
  · have h := hEqTerms x hxW
    simpa [hx] using h
  · intro y hy hyx
    have h := hEqTerms y hy
    have hyX : y ∉ X := by
      intro hmem
      have : y = x := by
        simpa [hxX] using hmem
      exact hyx this
    simpa [hyX] using h

/-- The second edge through the exceptional vertex has an opposite
`(r-1)`-set disjoint from the unique missing facet. -/
theorem one_missing_equality_two_core_edges
    {H B : Family α} {W P : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarFacets H W v r = {P})
    (hPcard : P.card = r - 1)
    (hCount : r * B.card = W.card + 1) :
    ∃ x Q, x ∈ W ∧ x ∉ P ∧ Q.card = r - 1 ∧
      Disjoint P Q ∧ x ∉ Q ∧ insert x P ∈ B ∧ insert x Q ∈ B ∧
      insert x P ≠ insert x Q ∧
      equalityOutsideEdgesAt B x = {insert x P, insert x Q} ∧
      (∀ y ∈ W, y ≠ x →
        (equalityOutsideEdgesAt B y).card = 1) := by
  classical
  obtain ⟨x, hxW, hxP, hPx, hDegX, hDegElse⟩ :=
    one_missing_equality_vertex_degrees hH hBH hU hLin hr hW hvW
      hMissing hPcard hCount
  have hPxAt : insert x P ∈ equalityOutsideEdgesAt B x := by
    exact Finset.mem_filter.mpr ⟨hPx, Finset.mem_insert_self ..⟩
  obtain ⟨F, hFAt, hFne⟩ := Finset.exists_mem_ne
    (by omega : 1 < (equalityOutsideEdgesAt B x).card) (insert x P)
  have hF : F ∈ B := (Finset.mem_filter.mp hFAt).1
  have hxF : x ∈ F := (Finset.mem_filter.mp hFAt).2
  let Q := F.erase x
  have hQcard : Q.card = r - 1 := by
    have hc := Finset.card_erase_add_one hxF
    rw [hU hF] at hc
    dsimp [Q]
    omega
  have hxQ : x ∉ Q := Finset.notMem_erase x F
  have hF_eq : F = insert x Q := (Finset.insert_erase hxF).symm
  have hDisj : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro y hyP hyQ
    have hyx : y ≠ x := by
      intro h
      exact hxP (h ▸ hyP)
    have hSub : ({x, y} : Edge α) ⊆ (insert x P) ∩ F := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_insert_self .., hxF⟩
      · have hzy : z = y := Finset.mem_singleton.mp hz
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_insert_of_mem (hzy ▸ hyP),
           Finset.mem_of_mem_erase (hzy ▸ hyQ)⟩
    have hCard := Finset.card_le_card hSub
    have hPair : ({x, y} : Edge α).card = 2 := Finset.card_pair hyx.symm
    have hOne := hLin hPx hF hFne.symm
    omega
  have hAtEq : equalityOutsideEdgesAt B x = {insert x P, F} := by
    have hSub : ({insert x P, F} : Family α) ⊆ equalityOutsideEdgesAt B x := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact hPxAt
      · exact hFAt
    have hPairCard : ({insert x P, F} : Family α).card = 2 :=
      Finset.card_pair hFne.symm
    exact Finset.eq_of_subset_of_card_le hSub (by omega) |>.symm
  refine ⟨x, Q, hxW, hxP, hQcard, hDisj, hxQ, hPx, ?_, ?_, ?_⟩
  · rw [← hF_eq]
    exact hF
  · rw [← hF_eq]
    exact hFne.symm
  · rw [← hF_eq]
    constructor
    · simpa [hF_eq] using hAtEq
    · exact hDegElse

/-- Complete all-rank normal form: after deleting the two core edges, the
remaining actual outside edges form a matching and cover exactly the
remaining ordinary vertices. -/
theorem one_missing_equality_outside_normal_form
    {H B : Family α} {W P : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hLin : LinearFamily B) (hr : 3 ≤ r)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarFacets H W v r = {P})
    (hPcard : P.card = r - 1)
    (hCount : r * B.card = W.card + 1) :
    ∃ x Q M, x ∈ W ∧ x ∉ P ∧ Q.card = r - 1 ∧
      Disjoint P Q ∧ x ∉ Q ∧
      B = insert (insert x P) (insert (insert x Q) M) ∧
      IsMatching M ∧
      (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
      M.biUnion (fun E => E) = W \ (insert x P ∪ insert x Q) := by
  classical
  obtain ⟨x, Q, hxW, hxP, hQcard, hPQ, hxQ, hPx, hQx, hCoreNe,
    hAtEq, hDegElse⟩ := one_missing_equality_two_core_edges
      hH hBH hU hLin hr hW hvW hMissing hPcard hCount
  let Ex := insert x P
  let Fx := insert x Q
  let M := (B.erase Ex).erase Fx
  have hMmem {E : Edge α} (hE : E ∈ M) :
      E ∈ B ∧ E ≠ Ex ∧ E ≠ Fx := by
    have hE' : E ≠ Fx ∧ E ∈ B.erase Ex := by
      simpa [M, Finset.mem_erase] using hE
    have hE'' := Finset.mem_erase.mp hE'.2
    exact ⟨hE''.2, hE''.1, hE'.1⟩
  have hNoX {E : Edge α} (hE : E ∈ M) : x ∉ E := by
    intro hxE
    obtain ⟨hEB, hENe, hFNe⟩ := hMmem hE
    have hEAt : E ∈ equalityOutsideEdgesAt B x :=
      Finset.mem_filter.mpr ⟨hEB, hxE⟩
    rw [hAtEq] at hEAt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEAt
    rcases hEAt with h | h
    · exact hENe h
    · exact hFNe h
  have hSameAt (y : α) (hyW : y ∈ W) (hyx : y ≠ x)
      {E F : Edge α} (hE : E ∈ B) (hF : F ∈ B)
      (hyE : y ∈ E) (hyF : y ∈ F) : E = F := by
    have hCard : (equalityOutsideEdgesAt B y).card ≤ 1 := by
      rw [hDegElse y hyW hyx]
    exact Finset.card_le_one.mp hCard E
      (Finset.mem_filter.mpr ⟨hE, hyE⟩) F
      (Finset.mem_filter.mpr ⟨hF, hyF⟩)
  have hMdisj : ∀ E ∈ M, Disjoint E (Ex ∪ Fx) := by
    intro E hE
    apply Finset.disjoint_left.mpr
    intro y hyE hyCore
    obtain ⟨hEB, hENe, hFNe⟩ := hMmem hE
    have hyW : y ∈ W := hW E hEB hyE
    have hyx : y ≠ x := by
      intro h
      exact hNoX hE (h ▸ hyE)
    rcases Finset.mem_union.mp hyCore with hyEx | hyFx
    · exact hENe (hSameAt y hyW hyx hEB hPx hyE hyEx)
    · exact hFNe (hSameAt y hyW hyx hEB hQx hyE hyFx)
  have hMatch : IsMatching M := by
    intro E F hE hF hEF
    apply Finset.disjoint_left.mpr
    intro y hyE hyF
    have hEB := (hMmem hE).1
    have hFB := (hMmem hF).1
    have hyW := hW E hEB hyE
    have hyx : y ≠ x := by
      intro h
      exact hNoX hE (h ▸ hyE)
    exact hEF (hSameAt y hyW hyx hEB hFB hyE hyF)
  have hBform : B = insert Ex (insert Fx M) := by
    have hFx : Fx ∈ B := hQx
    have hFxErase : Fx ∈ B.erase Ex := Finset.mem_erase.mpr ⟨hCoreNe.symm, hFx⟩
    have h1 : insert Fx M = B.erase Ex := Finset.insert_erase hFxErase
    have h2 : insert Ex (B.erase Ex) = B := Finset.insert_erase hPx
    rw [h1, h2]
  have hCover : M.biUnion (fun E => E) = W \ (Ex ∪ Fx) := by
    ext y
    constructor
    · intro hy
      obtain ⟨E, hE, hyE⟩ := Finset.mem_biUnion.mp hy
      have hEB := (hMmem hE).1
      apply Finset.mem_sdiff.mpr
      refine ⟨hW E hEB hyE, ?_⟩
      intro hyCore
      exact (Finset.disjoint_left.mp (hMdisj E hE)) hyE hyCore
    · intro hy
      have hyW : y ∈ W := (Finset.mem_sdiff.mp hy).1
      have hyCore : y ∉ Ex ∪ Fx := (Finset.mem_sdiff.mp hy).2
      have hyx : y ≠ x := by
        intro h
        exact hyCore (Finset.mem_union.mpr (Or.inl (h ▸ Finset.mem_insert_self ..)))
      have hDeg := hDegElse y hyW hyx
      obtain ⟨E, hEAt⟩ := Finset.card_pos.mp (by omega : 0 <
        (equalityOutsideEdgesAt B y).card)
      have hEB := (Finset.mem_filter.mp hEAt).1
      have hyE := (Finset.mem_filter.mp hEAt).2
      have hENe : E ≠ Ex := by
        intro h
        exact hyCore (Finset.mem_union.mpr (Or.inl (h ▸ hyE)))
      have hFNe : E ≠ Fx := by
        intro h
        exact hyCore (Finset.mem_union.mpr (Or.inr (h ▸ hyE)))
      have hEM : E ∈ M := by
        simp [M, Finset.mem_erase, hENe, hFNe, hEB]
      exact Finset.mem_biUnion.mpr ⟨E, hEM, hyE⟩
  refine ⟨x, Q, M, hxW, hxP, hQcard, hPQ, hxQ, ?_, hMatch, hMdisj, ?_⟩
  · simpa [Ex, Fx] using hBform
  · simpa [Ex, Fx] using hCover

end JSP523.Rank5
