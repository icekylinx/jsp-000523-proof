import JSP523.Rank4.LocalExactLinear
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The forward one-missing-facet equality branch

The incidence map behind (III.C.3) is sharp when exactly one star triple is
missing. This file extracts the vertex-degree consequences used in III.C.5
directly from actual outside edges.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Two outside edges through a cannot both have their opposite star
facets present. Their opposite triples would be disjoint members of the
common cell of v,a. -/
theorem linear_outside_present_opposite_unique
    {H B : Family α} {W : Edge α} {v a : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    {E F : Edge α} (hE : E ∈ B) (hF : F ∈ B)
    (haE : a ∈ E) (haF : a ∈ F)
    (hStarE : insert v (E.erase a) ∈ H)
    (hStarF : insert v (F.erase a) ∈ H) : E = F := by
  by_contra hEF
  have haW : a ∈ W := hW E hE haE
  have hva : v ≠ a := by
    intro h
    exact hvW (h.symm ▸ haW)
  have hTcard : (E.erase a).card = 3 := by
    have h := Finset.card_erase_add_one haE
    rw [hU hE] at h
    omega
  have hScard : (F.erase a).card = 3 := by
    have h := Finset.card_erase_add_one haF
    rw [hU hF] at h
    omega
  have hTcell : E.erase a ∈ commonTripleCell H (insert v W) v a := by
    apply mem_common_triple_cell.mpr
    refine ⟨?_, hTcard, ?_, hStarE, ?_⟩
    · intro x hx
      exact Finset.mem_insert_of_mem
        (hW E hE (Finset.mem_of_mem_erase hx))
    · apply Finset.disjoint_left.mpr
      intro x hx hxVA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxVA
      rcases hxVA with hxv | hxa
      · exact hvW (hW E hE (Finset.mem_of_mem_erase (hxv ▸ hx)))
      · exact (Finset.notMem_erase a E) (hxa ▸ hx)
    · simpa only [Finset.insert_erase haE] using hBH hE
  have hScell : F.erase a ∈ commonTripleCell H (insert v W) v a := by
    apply mem_common_triple_cell.mpr
    refine ⟨?_, hScard, ?_, hStarF, ?_⟩
    · intro x hx
      exact Finset.mem_insert_of_mem
        (hW F hF (Finset.mem_of_mem_erase hx))
    · apply Finset.disjoint_left.mpr
      intro x hx hxVA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxVA
      rcases hxVA with hxv | hxa
      · exact hvW (hW F hF (Finset.mem_of_mem_erase (hxv ▸ hx)))
      · exact (Finset.notMem_erase a F) (hxa ▸ hx)
    · simpa only [Finset.insert_erase haF] using hBH hF
  have hDisj : Disjoint (E.erase a) (F.erase a) := by
    apply Finset.disjoint_left.mpr
    intro x hxE hxF
    have hxa : x ≠ a := Finset.ne_of_mem_erase hxE
    have hTwo : ({a, x} : Edge α) ⊆ E ∩ F := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_inter.mpr ⟨haE, haF⟩
      · have hyx : y = x := Finset.mem_singleton.mp hy
        exact Finset.mem_inter.mpr
          ⟨hyx ▸ Finset.mem_of_mem_erase hxE,
           hyx ▸ Finset.mem_of_mem_erase hxF⟩
    have hCard := Finset.card_le_card hTwo
    have hPair : ({a, x} : Edge α).card = 2 :=
      Finset.card_pair hxa.symm
    have hOne := hLin hE hF hEF
    omega
  have hEraseNe : E.erase a ≠ F.erase a := by
    intro hEq
    have hEeq : insert a (E.erase a) = E := Finset.insert_erase haE
    have hFeq : insert a (F.erase a) = F := Finset.insert_erase haF
    exact hEF (by rw [← hEeq, ← hFeq, hEq])
  have hMeet :=
    common_triple_cell_intersecting hH hva hTcell hScell hEraseNe
  exact Finset.not_nonempty_iff_eq_empty.mpr
    (Finset.disjoint_iff_inter_eq_empty.mp hDisj) hMeet

/-- Actual outside edges incident with a vertex. -/
def outsideEdgesAt (B : Family α) (a : α) : Family α :=
  B.filter fun E => a ∈ E

/-- Incident outside edges whose opposite star facet is present. -/
def presentOutsideEdgesAt (H B : Family α) (v a : α) : Family α :=
  (outsideEdgesAt B a).filter fun E => insert v (E.erase a) ∈ H

/-- Incident outside edges whose opposite star facet is missing. -/
def missingOutsideEdgesAt (H B : Family α) (v a : α) : Family α :=
  (outsideEdgesAt B a).filter fun E => insert v (E.erase a) ∉ H

/-- A missing opposite facet in the one-hole star is precisely the hole. -/
theorem missing_outside_opposite_eq_unique
    {H B : Family α} {W P : Edge α} {v a : α}
    (hU : Uniform 4 B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hMissing : missingStarTriples H W v = {P})
    {E : Edge α} (hE : E ∈ missingOutsideEdgesAt H B v a) :
    E.erase a = P ∧ E = insert a P := by
  have hE' := Finset.mem_filter.mp hE
  have hEa := Finset.mem_filter.mp hE'.1
  have hCard : (E.erase a).card = 3 := by
    have h := Finset.card_erase_add_one hEa.2
    rw [hU hEa.1] at h
    omega
  have hSub : E.erase a ⊆ W :=
    (Finset.erase_subset a E).trans (hW E hEa.1)
  have hFacet : E.erase a ∈ missingStarTriples H W v := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powersetCard.mpr ⟨hSub, hCard⟩, hE'.2⟩
  rw [hMissing] at hFacet
  have hEq : E.erase a = P := by simpa using hFacet
  exact ⟨hEq, by rw [← Finset.insert_erase hEa.2, hEq]⟩

theorem present_outside_edges_at_card_le_one
    {H B : Family α} {W : Edge α} {v a : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W) :
    (presentOutsideEdgesAt H B v a).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro E hE F hF
  have hE' := Finset.mem_filter.mp hE
  have hF' := Finset.mem_filter.mp hF
  have hEa := Finset.mem_filter.mp hE'.1
  have hFa := Finset.mem_filter.mp hF'.1
  exact linear_outside_present_opposite_unique hH hBH hU hLin
    hW hvW hEa.1 hFa.1 hEa.2 hFa.2 hE'.2 hF'.2

theorem missing_outside_edges_at_card_le_one
    {H B : Family α} {W P : Edge α} {v a : α}
    (hU : Uniform 4 B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hMissing : missingStarTriples H W v = {P}) :
    (missingOutsideEdgesAt H B v a).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro E hE F hF
  calc
    E = insert a P := (missing_outside_opposite_eq_unique hU hW hMissing hE).2
    _ = F := (missing_outside_opposite_eq_unique hU hW hMissing hF).2.symm

/-- The two kinds of incidences partition the actual outside degree. -/
theorem outside_edges_at_eq_present_union_missing
    (H B : Family α) (v a : α) :
    outsideEdgesAt B a =
      presentOutsideEdgesAt H B v a ∪ missingOutsideEdgesAt H B v a := by
  ext E
  simp only [outsideEdgesAt, presentOutsideEdgesAt, missingOutsideEdgesAt,
    Finset.mem_filter, Finset.mem_union]
  tauto

theorem outside_edges_at_card_le_two
    {H B : Family α} {W P : Edge α} {v a : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarTriples H W v = {P}) :
    (outsideEdgesAt B a).card ≤ 2 := by
  rw [outside_edges_at_eq_present_union_missing H B v a]
  have hP := present_outside_edges_at_card_le_one
    (a := a) hH hBH hU hLin hW hvW
  have hM := missing_outside_edges_at_card_le_one
    (a := a) hU hW hMissing
  have hUcard := Finset.card_union_le
    (presentOutsideEdgesAt H B v a)
    (missingOutsideEdgesAt H B v a)
  omega

/-- A pair of outside edges sharing the three-vertex hole violates
linearity. Hence at most one vertex can carry a missing opposite facet. -/
theorem unique_missing_opposite_vertex
    {H B : Family α} {W P : Edge α} {v a b : α}
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hMissing : missingStarTriples H W v = {P})
    (hPcard : P.card = 3)
    (ha : (missingOutsideEdgesAt H B v a).Nonempty)
    (hb : (missingOutsideEdgesAt H B v b).Nonempty) : a = b := by
  obtain ⟨E, hE⟩ := ha
  obtain ⟨F, hF⟩ := hb
  have hEa := Finset.mem_filter.mp (Finset.mem_filter.mp hE).1
  have hFb := Finset.mem_filter.mp (Finset.mem_filter.mp hF).1
  obtain ⟨hEP, hEeq⟩ :=
    missing_outside_opposite_eq_unique hU hW hMissing hE
  obtain ⟨hFP, hFeq⟩ :=
    missing_outside_opposite_eq_unique hU hW hMissing hF
  by_contra hab
  have hEF : E ≠ F := by
    intro hEq
    have haNot : a ∉ P := hEP ▸ Finset.notMem_erase a E
    have hbNot : b ∉ P := hFP ▸ Finset.notMem_erase b F
    have haF : a ∈ F := hEq ▸ hEa.2
    rw [hFeq] at haF
    simp only [Finset.mem_insert] at haF
    rcases haF with h | h
    · exact hab h
    · exact haNot h
  have hSub : P ⊆ E ∩ F := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨hEeq ▸ Finset.mem_insert_of_mem hx,
       hFeq ▸ Finset.mem_insert_of_mem hx⟩
  have hCard := Finset.card_le_card hSub
  have hOne := hLin hEa.1 hFb.1 hEF
  omega

/-- Double-count actual outside edge-vertex incidences. -/
theorem sum_outside_edges_at_card
    (B : Family α) (W : Edge α)
    (hU : Uniform 4 B) (hW : ∀ E ∈ B, E ⊆ W) :
    (∑ a ∈ W, (outsideEdgesAt B a).card) = 4 * B.card := by
  classical
  calc
    (∑ a ∈ W, (outsideEdgesAt B a).card) =
        ∑ a ∈ W, ∑ E ∈ B, if a ∈ E then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [outsideEdgesAt, Finset.card_filter]
    _ = ∑ E ∈ B, ∑ a ∈ W, if a ∈ E then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ E ∈ B, E.card := by
      apply Finset.sum_congr rfl
      intro E hE
      have hFilter : W.filter (fun a => a ∈ E) = E := by
        ext a
        simp [hW E hE]
      rw [← Finset.card_filter, hFilter]
    _ = 4 * B.card := by
      calc
        (∑ E ∈ B, E.card) = ∑ _E ∈ B, 4 := by
          apply Finset.sum_congr rfl
          intro E hE
          exact hU hE
        _ = 4 * B.card := by simp [Finset.sum_const, mul_comm]

/-- Ordinary vertices carrying a missing opposite star facet. -/
def missingOppositeVertices
    (H B : Family α) (W : Edge α) (v : α) : Edge α :=
  W.filter fun a => (missingOutsideEdgesAt H B v a).Nonempty

theorem missing_opposite_vertices_card_le_one
    {H B : Family α} {W P : Edge α} {v : α}
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W)
    (hMissing : missingStarTriples H W v = {P})
    (hPcard : P.card = 3) :
    (missingOppositeVertices H B W v).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact unique_missing_opposite_vertex hU hLin hW hMissing hPcard
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

/-- Every outside vertex has at most one present incidence, and only the
unique missing opposite facet can allow a second incidence. -/
theorem outside_edges_at_card_le_one_add_special
    {H B : Family α} {W P : Edge α} {v a : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarTriples H W v = {P})
    (haW : a ∈ W) :
    (outsideEdgesAt B a).card ≤
      1 + if a ∈ missingOppositeVertices H B W v then 1 else 0 := by
  classical
  by_cases hSpecial : a ∈ missingOppositeVertices H B W v
  · simp only [hSpecial, ↓reduceIte]
    simpa using outside_edges_at_card_le_two hH hBH hU hLin hW hvW hMissing
  · have hEmpty : missingOutsideEdgesAt H B v a = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hNon
      exact hSpecial (Finset.mem_filter.mpr ⟨haW, hNon⟩)
    rw [outside_edges_at_eq_present_union_missing H B v a, hEmpty]
    simpa [hSpecial] using
      (present_outside_edges_at_card_le_one
        (a := a) hH hBH hU hLin hW hvW)

/-- At the one-hole equality count, exactly one ordinary vertex carries
the missing-facet incidence. -/
theorem one_missing_equality_unique_special_vertex
    {H B : Family α} {W P : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarTriples H W v = {P})
    (hPcard : P.card = 3)
    (hCount : 4 * B.card = W.card + 1) :
    ∃! x : α, x ∈ missingOppositeVertices H B W v := by
  classical
  let X := missingOppositeVertices H B W v
  have hXle : X.card ≤ 1 :=
    missing_opposite_vertices_card_le_one hU hLin hW hMissing hPcard
  have hTerm : ∀ a ∈ W,
      (outsideEdgesAt B a).card ≤
        1 + if a ∈ X then 1 else 0 := by
    intro a ha
    exact outside_edges_at_card_le_one_add_special
      hH hBH hU hLin hW hvW hMissing ha
  have hSum := Finset.sum_le_sum hTerm
  have hXsub : X ⊆ W := Finset.filter_subset _ _
  have hIndicator :
      (∑ a ∈ W, (if a ∈ X then 1 else 0)) = X.card := by
    rw [← Finset.card_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun ha => hXsub ha)
  have hUpper :
      (∑ a ∈ W, (1 + if a ∈ X then 1 else 0)) =
        W.card + X.card := by
    rw [Finset.sum_add_distrib, hIndicator]
    simp
  rw [sum_outside_edges_at_card B W hU hW, hUpper, hCount] at hSum
  have hXeq : X.card = 1 := by omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hXeq
  refine ⟨x, ?_, ?_⟩
  · change x ∈ X
    simp [hx]
  · intro y hy
    change y ∈ X at hy
    simpa [hx] using hy

/-- Sharpness of the one-hole incidence count forces one degree-two
vertex, all other ordinary vertices having degree one. The degree-two
vertex lies outside the missing triple and supports its outside edge. -/
theorem one_missing_equality_vertex_degrees
    {H B : Family α} {W P : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarTriples H W v = {P})
    (hPcard : P.card = 3)
    (hCount : 4 * B.card = W.card + 1) :
    ∃ x ∈ W, x ∉ P ∧ insert x P ∈ B ∧
      (outsideEdgesAt B x).card = 2 ∧
      ∀ y ∈ W, y ≠ x → (outsideEdgesAt B y).card = 1 := by
  classical
  let X := missingOppositeVertices H B W v
  obtain ⟨x, hx, hUnique⟩ :=
    one_missing_equality_unique_special_vertex hH hBH hU hLin
      hW hvW hMissing hPcard hCount
  have hxX : x ∈ X := hx
  have hXeq : X = {x} := by
    ext y
    constructor
    · intro hy
      have hyx : y = x := hUnique y hy
      simp [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      exact hyx ▸ hxX
  have hxW : x ∈ W := (Finset.mem_filter.mp hx).1
  obtain ⟨E, hE⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hEP, hEeq⟩ :=
    missing_outside_opposite_eq_unique hU hW hMissing hE
  have hxP : x ∉ P := by
    rw [← hEP]
    exact Finset.notMem_erase x E
  have hPx : insert x P ∈ B := by
    rw [← hEeq]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
  have hTerm : ∀ y ∈ W,
      (outsideEdgesAt B y).card ≤
        1 + if y ∈ X then 1 else 0 := by
    intro y hy
    exact outside_edges_at_card_le_one_add_special
      hH hBH hU hLin hW hvW hMissing hy
  have hXsub : X ⊆ W := Finset.filter_subset _ _
  have hIndicator :
      (∑ y ∈ W, (if y ∈ X then 1 else 0)) = X.card := by
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hy => hXsub hy)
  have hUpper :
      (∑ y ∈ W, (1 + if y ∈ X then 1 else 0)) =
        W.card + X.card := by
    rw [Finset.sum_add_distrib, hIndicator]
    simp
  have hSumEq :
      (∑ y ∈ W, (outsideEdgesAt B y).card) =
        ∑ y ∈ W, (1 + if y ∈ X then 1 else 0) := by
    rw [sum_outside_edges_at_card B W hU hW, hUpper, hXeq]
    simpa using hCount
  have hPoint := (Finset.sum_eq_sum_iff_of_le hTerm).mp hSumEq
  refine ⟨x, hxW, hxP, hPx, ?_, ?_⟩
  · have h := hPoint x hxW
    simpa [hXeq] using h
  · intro y hy hyx
    have h := hPoint y hy
    simpa [hXeq, hyx] using h

/-- The two outside edges through the degree-two vertex have disjoint
opposite triples. All remaining outside edges avoid that vertex. -/
theorem one_missing_equality_two_core_edges
    {H B : Family α} {W P : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarTriples H W v = {P})
    (hPcard : P.card = 3)
    (hCount : 4 * B.card = W.card + 1) :
    ∃ x : α, ∃ Q : Edge α,
      x ∈ W ∧ x ∉ P ∧ Q.card = 3 ∧
      Disjoint P Q ∧ x ∉ Q ∧
      insert x P ∈ B ∧ insert x Q ∈ B ∧
      insert x P ≠ insert x Q ∧
      outsideEdgesAt B x = {insert x P, insert x Q} ∧
      (∀ y ∈ W, y ≠ x → (outsideEdgesAt B y).card = 1) := by
  classical
  obtain ⟨x, hxW, hxP, hPx, hDegX, hDegElse⟩ :=
    one_missing_equality_vertex_degrees
      hH hBH hU hLin hW hvW hMissing hPcard hCount
  have hPxAt : insert x P ∈ outsideEdgesAt B x := by
    apply Finset.mem_filter.mpr
    exact ⟨hPx, Finset.mem_insert_self ..⟩
  obtain ⟨F, hFAt, hFne⟩ :=
    Finset.exists_mem_ne (by omega : 1 < (outsideEdgesAt B x).card)
      (insert x P)
  have hF : F ∈ B := (Finset.mem_filter.mp hFAt).1
  have hxF : x ∈ F := (Finset.mem_filter.mp hFAt).2
  let Q := F.erase x
  have hQcard : Q.card = 3 := by
    have h := Finset.card_erase_add_one hxF
    rw [hU hF] at h
    change (F.erase x).card = 3
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
    have hPair : ({x, y} : Edge α).card = 2 :=
      Finset.card_pair hyx.symm
    have hOne := hLin hPx hF hFne.symm
    omega
  have hAtEq : outsideEdgesAt B x = {insert x P, F} := by
    have hSub : ({insert x P, F} : Family α) ⊆ outsideEdgesAt B x := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact hPxAt
      · exact hFAt
    have hPair : ({insert x P, F} : Family α).card = 2 :=
      Finset.card_pair hFne.symm
    exact (Finset.eq_of_subset_of_card_le hSub (by omega)).symm
  refine ⟨x, Q, hxW, hxP, hQcard, hDisj, hxQ, hPx, ?_, ?_, ?_, hDegElse⟩
  · rw [← hF_eq]
    exact hF
  · rw [← hF_eq]
    exact hFne.symm
  · rw [← hF_eq]
    exact hAtEq

/-- The forward equality classification for one missing star triple.
The two exceptional outside edges meet only at x; the remaining outside
edges form a matching and partition the remaining ordinary vertices. -/
theorem one_missing_equality_outside_normal_form
    {H B : Family α} {W P : Edge α} {v : α}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform 4 B) (hLin : LinearFamily B)
    (hW : ∀ E ∈ B, E ⊆ W) (hvW : v ∉ W)
    (hMissing : missingStarTriples H W v = {P})
    (hPcard : P.card = 3)
    (hCount : 4 * B.card = W.card + 1) :
    ∃ (x : α) (Q : Edge α) (M : Family α),
      x ∈ W ∧ x ∉ P ∧ Q.card = 3 ∧
      Disjoint P Q ∧ x ∉ Q ∧
      B = insert (insert x P) (insert (insert x Q) M) ∧
      IsMatching M ∧
      (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
      M.biUnion (fun E => E) =
        W \ (insert x P ∪ insert x Q) := by
  classical
  obtain ⟨x, Q, hxW, hxP, hQcard, hPQ, hxQ, hPx, hQx,
    hNe, hAtEq, hDegElse⟩ :=
      one_missing_equality_two_core_edges
        hH hBH hU hLin hW hvW hMissing hPcard hCount
  let Ex : Edge α := insert x P
  let Fx : Edge α := insert x Q
  let M : Family α := (B.erase Ex).erase Fx
  have hMmem {E : Edge α} (hE : E ∈ M) :
      E ∈ B ∧ E ≠ Ex ∧ E ≠ Fx := by
    have hE' : E ≠ Fx ∧ E ∈ B.erase Ex := by
      simpa only [M, Finset.mem_erase] using hE
    have hE'' := Finset.mem_erase.mp hE'.2
    exact ⟨hE''.2, hE''.1, hE'.1⟩
  have hNoX {E : Edge α} (hE : E ∈ M) : x ∉ E := by
    intro hxE
    obtain ⟨hEB, hENe, hFNe⟩ := hMmem hE
    have hEAt : E ∈ outsideEdgesAt B x :=
      Finset.mem_filter.mpr ⟨hEB, hxE⟩
    rw [hAtEq] at hEAt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEAt
    rcases hEAt with h | h
    · exact hENe h
    · exact hFNe h
  have hSameAt (y : α) (hyW : y ∈ W) (hyx : y ≠ x)
      {E F : Edge α} (hE : E ∈ B) (hF : F ∈ B)
      (hyE : y ∈ E) (hyF : y ∈ F) : E = F := by
    have hCard : (outsideEdgesAt B y).card ≤ 1 := by
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
    have hyW : y ∈ W := hW E hEB hyE
    have hyx : y ≠ x := by
      intro h
      exact hNoX hE (h ▸ hyE)
    exact hEF (hSameAt y hyW hyx hEB hFB hyE hyF)
  have hCover :
      M.biUnion (fun E => E) = W \ (Ex ∪ Fx) := by
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
        exact hyCore (Finset.mem_union.mpr
          (Or.inl (h ▸ Finset.mem_insert_self ..)))
      have hDeg : (outsideEdgesAt B y).card = 1 :=
        hDegElse y hyW hyx
      have hNon : (outsideEdgesAt B y).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨E, hEAt⟩ := hNon
      have hEB : E ∈ B := (Finset.mem_filter.mp hEAt).1
      have hyE : y ∈ E := (Finset.mem_filter.mp hEAt).2
      have hENe : E ≠ Ex := by
        intro h
        exact hyCore (Finset.mem_union.mpr (Or.inl (h ▸ hyE)))
      have hFNe : E ≠ Fx := by
        intro h
        exact hyCore (Finset.mem_union.mpr (Or.inr (h ▸ hyE)))
      apply Finset.mem_biUnion.mpr
      refine ⟨E, ?_, hyE⟩
      simp only [M, Finset.mem_erase]
      exact ⟨hFNe, hENe, hEB⟩
  have hFxErase : Fx ∈ B.erase Ex :=
    Finset.mem_erase.mpr ⟨hNe.symm, hQx⟩
  have hBform : B = insert Ex (insert Fx M) := by
    dsimp [M]
    rw [Finset.insert_erase hFxErase, Finset.insert_erase hPx]
  refine ⟨x, Q, M, hxW, hxP, hQcard, hPQ, hxQ, ?_, hMatch,
    hMdisj, ?_⟩
  · simpa only [Ex, Fx] using hBform
  · simpa only [Ex, Fx] using hCover

/-- The one-missing-triple branch of equality in the rank-four near-star
bound has exactly the exceptional-pair-plus-matching outside structure. -/
theorem rank_four_one_missing_equality_classification
    {H : Family α} {W : Edge α} {v : α}
    (hH : Admissible H) (hU : Uniform 4 H)
    (hSupport : ∀ E ∈ H, E ⊆ insert v W)
    (hvW : v ∉ W)
    (hLin : LinearFamily (outsideEdges H W))
    (hEquality : H.card = W.card.choose 3 + W.card / 4)
    (hMissingCard : (missingStarTriples H W v).card = 1) :
    ∃ (P : Edge α) (x : α) (Q : Edge α) (M : Family α),
      missingStarTriples H W v = {P} ∧ P.card = 3 ∧
      W.card % 4 = 3 ∧
      x ∈ W ∧ x ∉ P ∧ Q.card = 3 ∧
      Disjoint P Q ∧ x ∉ Q ∧
      outsideEdges H W =
        insert (insert x P) (insert (insert x Q) M) ∧
      IsMatching M ∧
      (∀ E ∈ M, Disjoint E (insert x P ∪ insert x Q)) ∧
      M.biUnion (fun E => E) =
        W \ (insert x P ∪ insert x Q) := by
  classical
  let B := outsideEdges H W
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hMissingCard
  have hMissing : missingStarTriples H W v = {P} := hP
  have hPmem : P ∈ missingStarTriples H W v := by simp [hMissing]
  have hPcard : P.card = 3 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hPmem).1).2
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform 4 B := by
    intro E hE
    exact hU (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ W := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  have hMod : W.card % 4 = 3 :=
    (linear_outside_equality_missing_restriction
      hH hU hSupport hvW hLin hEquality).2 hMissingCard
  have hStar := rank_four_star_outside_card hU hSupport hvW
  have hPartition := present_add_missing_star H W v
  have hDiv : W.card = 4 * (W.card / 4) + W.card % 4 := by
    simpa [add_comm, mul_comm] using (Nat.mod_add_div W.card 4).symm
  have hCount : 4 * B.card = W.card + 1 := by
    change H.card = (presentStarTriples H W v).card + B.card at hStar
    omega
  obtain ⟨x, Q, M, hxW, hxP, hQcard, hPQ, hxQ,
    hBform, hMatch, hMdisj, hCover⟩ :=
      one_missing_equality_outside_normal_form
        hH hBH hBU hLin hBW hvW hMissing hPcard hCount
  exact ⟨P, x, Q, M, hMissing, hPcard, hMod, hxW, hxP,
    hQcard, hPQ, hxQ, hBform, hMatch, hMdisj, hCover⟩

end JSP523.Rank4
