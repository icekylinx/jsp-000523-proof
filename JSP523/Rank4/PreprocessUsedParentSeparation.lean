import JSP523.Rank4.PreprocessUsedParentLabel

/-!
# Reciprocal rainbow attachments under used parent-label separation

Only the labels of actual used completion pairs enter the rainbow
attachment argument. This replaces the older all-pairs separation
condition by the bounded-label system from §III.A.5.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- A rainbow attachment to a reciprocal triangle would put its
attachment vertex in the corrected parent-label completion sets of two
distinct pair roots of the reciprocal edge. -/
theorem used_parent_reciprocal_rainbow_attachment_forbidden
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (h_ab : (completionPairLinkGraph D P).Adj a b)
    (h_aw : (completionPairLinkGraph D P).Adj a w)
    (h_bw : (completionPairLinkGraph D P).Adj b w)
    (h_separated : ReciprocalUsedParentPairSeparation D) :
    ∀ t : α,
      t ≠ b → t ≠ w →
      (completionPairLinkGraph D P).Adj a t →
      D.label b t ∈ P → D.label w t ∈ P →
      D.label b t ≠ D.label w t → False := by
  classical
  intro t hNotB hNotW hAT hBTinP hWTinP hDiff
  have hAB' := h_ab
  have hAW' := h_aw
  have hBW' := h_bw
  have hAT' := hAT
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
  change a ∉ P ∧ w ∉ P ∧ a ∈ D.ground ∧ w ∈ D.ground ∧
    a ≠ w ∧ insert a (insert w P) ∈ D.K at hAW'
  change b ∉ P ∧ w ∉ P ∧ b ∈ D.ground ∧ w ∈ D.ground ∧
    b ≠ w ∧ insert b (insert w P) ∈ D.K at hBW'
  change a ∉ P ∧ t ∉ P ∧ a ∈ D.ground ∧ t ∈ D.ground ∧
    a ≠ t ∧ insert a (insert t P) ∈ D.K at hAT'
  let x := D.label b t
  let y := D.label w t
  let R : Edge α := {b, x}
  let S : Edge α := {w, y}
  let E : Edge α := insert b (insert w P)
  have htNotP : t ∉ P := hAT'.2.1
  have htGround : t ∈ D.ground := hAT'.2.2.2.1
  have hxGround : x ∈ D.ground := h_p_ground hBTinP
  have hyGround : y ∈ D.ground := h_p_ground hWTinP
  have hbx : b ≠ x := by
    intro h
    exact hBW'.1 (h ▸ hBTinP)
  have hwy : w ≠ y := by
    intro h
    exact hBW'.2.1 (h ▸ hWTinP)
  have hRcard : R.card = 2 := Finset.card_pair hbx
  have hScard : S.card = 2 := Finset.card_pair hwy
  have hRsub : R ⊆ E := by
    intro z hz
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzb | hzx
    · subst z
      simp [E]
    · have hzP : z ∈ P := hzx ▸ hBTinP
      simp [E, hzP]
  have hSsub : S ⊆ E := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzw | hzy
    · subst z
      simp [E]
    · have hzP : z ∈ P := hzy ▸ hWTinP
      simp [E, hzP]
  have hRmem : R ∈ E.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hRsub, hRcard⟩
  have hSmem : S ∈ E.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hSsub, hScard⟩
  have hDisj : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro z hzR hzS
    simp only [R, S, Finset.mem_insert, Finset.mem_singleton] at hzR hzS
    rcases hzR with hzb | hzx
    · rcases hzS with hzw | hzy
      · exact hBW'.2.2.2.2.1 (hzb.symm.trans hzw)
      · have hby : b = y := hzb.symm.trans hzy
        exact hBW'.1 (hby ▸ hWTinP)
    · rcases hzS with hzw | hzy
      · have hxw : x = w := hzx.symm.trans hzw
        exact hBW'.2.1 (hxw ▸ hBTinP)
      · exact hDiff (hzx.symm.trans hzy)
  have hE : E ∈ D.K := hBW'.2.2.2.2.2
  have hTripleX : insert x ({b, t} : Edge α) ∈
      reciprocalUsedParentLabelTriples D := by
    dsimp [x]
    exact mem_used_parent_label_of_shared_pair_root D P a b t
      h_p_card h_p_ground hAB'.2.2.1 hAB'.1
      hAB'.2.2.2.1 htGround hNotB.symm
      (by simpa [Finset.insert_comm] using hAB'.2.2.2.2.2)
      (by simpa [Finset.insert_comm] using hAT'.2.2.2.2.2)
  have hTripleY : insert y ({w, t} : Edge α) ∈
      reciprocalUsedParentLabelTriples D := by
    dsimp [y]
    exact mem_used_parent_label_of_shared_pair_root D P a w t
      h_p_card h_p_ground hAW'.2.2.1 hAW'.1
      hAW'.2.2.2.1 htGround hNotW.symm
      (by simpa [Finset.insert_comm] using hAW'.2.2.2.2.2)
      (by simpa [Finset.insert_comm] using hAT'.2.2.2.2.2)
  have hRset : R ∪ {t} = insert x ({b, t} : Edge α) := by
    ext z
    simp only [R, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hSset : S ∪ {t} = insert y ({w, t} : Edge α) := by
    ext z
    simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hRcompletion : t ∈ JSP523.Rank3.completionVertices
      (reciprocalUsedParentLabelTriples D) D.ground R := by
    simp only [JSP523.Rank3.completionVertices, Finset.mem_filter]
    refine ⟨htGround, ?_, ?_⟩
    · intro htR
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at htR
      rcases htR with hEqB | hEqX
      · exact hNotB hEqB
      · exact htNotP (hEqX.symm ▸ hBTinP)
    · rw [hRset]
      exact hTripleX
  have hScompletion : t ∈ JSP523.Rank3.completionVertices
      (reciprocalUsedParentLabelTriples D) D.ground S := by
    simp only [JSP523.Rank3.completionVertices, Finset.mem_filter]
    refine ⟨htGround, ?_, ?_⟩
    · intro htS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at htS
      rcases htS with hEqW | hEqY
      · exact hNotW hEqW
      · exact htNotP (hEqY.symm ▸ hWTinP)
    · rw [hSset]
      exact hTripleY
  have hSeparatedRS := h_separated E hE R hRmem S hSmem (by
    intro hEq
    have hbR : b ∈ R := by simp [R]
    have hbS : b ∈ S := hEq ▸ hbR
    exact (Finset.disjoint_left.mp hDisj) hbR hbS)
  exact (Finset.disjoint_left.mp hSeparatedRS) hRcompletion hScompletion

/-- The full reciprocal cleanup isolates each surviving triangle using
only the corrected used-pair parent label system. -/
theorem reciprocal_triangle_isolated_after_used_parent_cleanup
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel (completionPairLinkGraph (clearReciprocalFully D) P).Adj]
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (h_ab : (completionPairLinkGraph (clearReciprocalFully D) P).Adj a b)
    (h_aw : (completionPairLinkGraph (clearReciprocalFully D) P).Adj a w)
    (h_bw : (completionPairLinkGraph (clearReciprocalFully D) P).Adj b w)
    (h_aw_label : (clearReciprocalFully D).label a w = b)
    (h_bw_label : (clearReciprocalFully D).label b w = a)
    (h_separated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D)) :
    ∀ x ∈ ({a, b, w} : Edge α), ∀ t : α,
      t ∉ ({a, b, w} : Edge α) →
      ¬ (completionPairLinkGraph (clearReciprocalFully D) P).Adj x t := by
  let D₂ := clearReciprocalFully D
  have h_ab_label := clear_reciprocal_fully_common_witness_eq_label
    D P h_p_card h_p_ground a b w h_ab h_aw h_bw
    h_aw_label h_bw_label
  have h_no_a := used_parent_reciprocal_rainbow_attachment_forbidden
    D₂ P a b w h_p_card h_p_ground h_ab h_aw h_bw h_separated
  have h_no_b := used_parent_reciprocal_rainbow_attachment_forbidden
    D₂ P b a w h_p_card h_p_ground h_ab.symm h_bw h_aw h_separated
  have h_no_w := used_parent_reciprocal_rainbow_attachment_forbidden
    D₂ P w a b h_p_card h_p_ground h_aw.symm h_bw.symm h_ab h_separated
  exact reciprocal_triangle_has_no_external_neighbors
    D₂ P a b w h_p_card h_p_ground hab haw hbw
    h_ab h_aw h_bw h_ab_label h_aw_label h_bw_label
    (clear_reciprocal_fully_no_second D P h_p_card h_p_ground)
    h_no_a h_no_b h_no_w

end JSP523.Rank4
