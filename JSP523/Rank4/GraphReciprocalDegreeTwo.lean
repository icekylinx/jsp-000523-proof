import JSP523.Rank4.PreprocessUsedParentSeparation

/-!
# Degree-two facets of isolated reciprocal triangles

An isolated triangle in the actual pair link at a pair root has exactly
two completions at each of its three incident triple facets. This file
connects the full reciprocal preprocessing to the finite `R ≤ b` count.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- If the actual pair-link triangle `a,b,w` has no outside attachment,
the facet `P+a` has exactly the completions `b,w`. -/
theorem isolated_reciprocal_triangle_facet_degree_two
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    (h_p_card : P.card = 2) (_h_p_ground : P ⊆ D.ground)
    (h_ab : (completionPairLinkGraph D P).Adj a b)
    (h_aw : (completionPairLinkGraph D P).Adj a w)
    (hbw : b ≠ w)
    (h_isolated : ∀ x ∈ ({a, b, w} : Edge α), ∀ t : α,
      t ∉ ({a, b, w} : Edge α) →
        ¬ (completionPairLinkGraph D P).Adj x t) :
    (graphFacetCompletions D.K D.ground (insert a P)).card = 2 := by
  classical
  have h_ab' := h_ab
  have h_aw' := h_aw
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at h_ab'
  change a ∉ P ∧ w ∉ P ∧ a ∈ D.ground ∧ w ∈ D.ground ∧
    a ≠ w ∧ insert a (insert w P) ∈ D.K at h_aw'
  let T := insert a P
  have h_t_card : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem h_ab'.1, h_p_card]
  have h_b : b ∈ graphFacetCompletions D.K D.ground T := by
    exact Finset.mem_filter.mpr
      ⟨h_ab'.2.2.2.1, by
        simpa [T, Finset.insert_comm] using h_ab'.2.2.2.2.2⟩
  have h_w : w ∈ graphFacetCompletions D.K D.ground T := by
    exact Finset.mem_filter.mpr
      ⟨h_aw'.2.2.2.1, by
        simpa [T, Finset.insert_comm] using h_aw'.2.2.2.2.2⟩
  have h_set : graphFacetCompletions D.K D.ground T =
      ({b, w} : Finset α) := by
    ext t
    constructor
    · intro ht
      have ht' := Finset.mem_filter.mp ht
      have ht_not_t : t ∉ T :=
        four_facet_completion_not_in_facet
          D.K D.uniform_four T h_t_card t ht'.2
      have ht_not_p : t ∉ P := by
        intro htP
        exact ht_not_t (Finset.mem_insert_of_mem htP)
      have hat : a ≠ t := by
        intro h
        exact ht_not_t (h ▸ Finset.mem_insert_self a P)
      have h_at : (completionPairLinkGraph D P).Adj a t := by
        change a ∉ P ∧ t ∉ P ∧ a ∈ D.ground ∧ t ∈ D.ground ∧
          a ≠ t ∧ insert a (insert t P) ∈ D.K
        exact ⟨h_ab'.1, ht_not_p, h_ab'.2.2.1, ht'.1, hat,
          by simpa [T, Finset.insert_comm] using ht'.2⟩
      by_cases h_tri : t ∈ ({a, b, w} : Edge α)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h_tri
        rcases h_tri with hta | htb | htw
        · exact False.elim (hat hta.symm)
        · simp [htb]
        · simp [htw]
      · exact False.elim
          ((h_isolated a (by simp) t h_tri) h_at)
    · intro ht
      rcases Finset.mem_insert.mp ht with htb | htw
      · exact htb ▸ h_b
      · exact (Finset.mem_singleton.mp htw) ▸ h_w
  rw [h_set, Finset.card_pair hbw]

/-- The full two-round cleanup and parent separation give both degree-two
opposite facets of every surviving reciprocal triangle at its actual root. -/
theorem reciprocal_full_cleanup_opposite_facets_degree_two
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
    (graphFacetCompletions (clearReciprocalFully D).K D.ground
      (insert a P)).card = 2 ∧
    (graphFacetCompletions (clearReciprocalFully D).K D.ground
      (insert b P)).card = 2 := by
  let D₂ := clearReciprocalFully D
  have h_isolated := reciprocal_triangle_isolated_after_used_parent_cleanup
    D P a b w h_p_card h_p_ground hab haw hbw
    h_ab h_aw h_bw h_aw_label h_bw_label h_separated
  constructor
  · exact isolated_reciprocal_triangle_facet_degree_two
      D₂ P a b w h_p_card h_p_ground h_ab h_aw hbw h_isolated
  · have h_isolated' : ∀ x ∈ ({b, a, w} : Edge α), ∀ t : α,
        t ∉ ({b, a, w} : Edge α) →
          ¬ (completionPairLinkGraph D₂ P).Adj x t := by
      simpa only [Finset.insert_comm] using h_isolated
    exact isolated_reciprocal_triangle_facet_degree_two
      D₂ P b a w h_p_card h_p_ground h_ab.symm h_bw haw
      h_isolated'

omit [Fintype α] in
/-- The pair root opposite two vertices of an actual four-edge recovers
both opposite facets and the full edge. -/
theorem reciprocal_edge_pair_root_decomposition
    (D : FiniteCompletionCliqueData α)
    (E : Edge α) (a b : α)
    (h_edge : E ∈ D.K) (h_ground : E ⊆ D.ground)
    (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    let P := (E.erase a).erase b
    P.card = 2 ∧ P ⊆ D.ground ∧
      E.erase a = insert b P ∧
      E.erase b = insert a P ∧
      E = insert a (insert b P) := by
  classical
  intro P
  have hb_erase : b ∈ E.erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have ha_erase : a ∈ E.erase b :=
    Finset.mem_erase.mpr ⟨hab, ha⟩
  have h_four := D.uniform_four h_edge
  have h_card : P.card = 2 := by
    dsimp [P]
    rw [Finset.card_erase_of_mem hb_erase,
      Finset.card_erase_of_mem ha, h_four]
  have h_sub : P ⊆ D.ground :=
    (Finset.erase_subset _ _).trans
      ((Finset.erase_subset _ _).trans h_ground)
  have h_a : E.erase a = insert b P :=
    (Finset.insert_erase hb_erase).symm
  have h_b : E.erase b = insert a P := by
    have h_comm : (E.erase b).erase a = P := by
      exact (Finset.erase_right_comm).symm
    calc
      E.erase b = insert a ((E.erase b).erase a) :=
        (Finset.insert_erase ha_erase).symm
      _ = insert a P := by rw [h_comm]
  have h_edge_eq : E = insert a (insert b P) := by
    calc
      E = insert a (E.erase a) := (Finset.insert_erase ha).symm
      _ = insert a (insert b P) := by rw [h_a]
  exact ⟨h_card, h_sub, h_a, h_b, h_edge_eq⟩

omit [Fintype α] in
/-- An actual arrow out of `a` through the facet opposite `a` supplies
an ordinary pair-link neighbor of `b` at the opposite pair root. -/
theorem reciprocal_arrow_witness_pair_link
    (D : FiniteCompletionCliqueData α)
    (E P : Edge α) (a b : α)
    (h_p_card : P.card = 2) (h_p_ground : P ⊆ D.ground)
    (h_b_ground : b ∈ D.ground) (h_b_not_p : b ∉ P)
    (h_facet : E.erase a = insert b P)
    (h_arrow : actualReciprocalArrow D E a b) :
    ∃ w : α,
      (completionPairLinkGraph D P).Adj b w ∧
      w ≠ a ∧ D.label a w = b := by
  classical
  obtain ⟨_, _, _, w, hw, hwa, hlabel⟩ := h_arrow
  have h_p : P ∈ D.ground.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨h_p_ground, h_p_card⟩
  have hw' : w ∈ graphFacetCompletions D.K D.ground (insert b P) :=
    h_facet ▸ hw
  have h_adj := (raw_pair_link_slot_adj_iff_facet_completion
    D P h_p b w h_b_ground h_b_not_p).2 hw'
  exact ⟨w, h_adj, hwa, hlabel⟩

/-- Every actual reciprocal arrow pair in the fully cleaned family has a
degree-two facet opposite its first endpoint. The only global cleanup
premise is parent pair-label separation. -/
theorem reciprocal_full_cleanup_directed_opposite_degree_two
    (D : FiniteCompletionCliqueData α)
    (E : Edge α) (a b : α)
    (h_ground : ∀ F ∈ (clearReciprocalFully D).K,
      F ⊆ D.ground)
    (h_separated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D))
    (h_edge : E ∈ (clearReciprocalFully D).K)
    (h_ab : actualReciprocalArrow (clearReciprocalFully D) E a b)
    (h_ba : actualReciprocalArrow (clearReciprocalFully D) E b a) :
    (graphFacetCompletions (clearReciprocalFully D).K D.ground
      (E.erase a)).card = 2 := by
  classical
  let D₂ := clearReciprocalFully D
  let P := (E.erase a).erase b
  have h_a : a ∈ E := h_ab.1
  have h_b : b ∈ E := h_ab.2.1
  have hab : a ≠ b := h_ab.2.2.1
  have h_decomp := reciprocal_edge_pair_root_decomposition
    D₂ E a b h_edge (h_ground E h_edge) h_a h_b hab
  have h_p_card : P.card = 2 := h_decomp.1
  have h_p_ground : P ⊆ D.ground := h_decomp.2.1
  have h_facet_a : E.erase a = insert b P := h_decomp.2.2.1
  have h_facet_b : E.erase b = insert a P := h_decomp.2.2.2.1
  have h_edge_eq : E = insert a (insert b P) := h_decomp.2.2.2.2
  have h_a_not_p : a ∉ P := by
    intro haP
    have haErase : a ∈ E.erase a :=
      (Finset.erase_subset _ _) haP
    exact (Finset.mem_erase.mp haErase).1 rfl
  have h_b_not_p : b ∉ P := by
    intro hbP
    exact (Finset.mem_erase.mp hbP).1 rfl
  have h_a_ground : a ∈ D.ground := h_ground E h_edge h_a
  have h_b_ground : b ∈ D.ground := h_ground E h_edge h_b
  have h_pair : (completionPairLinkGraph D₂ P).Adj a b := by
    change a ∉ P ∧ b ∉ P ∧ a ∈ D₂.ground ∧ b ∈ D₂.ground ∧
      a ≠ b ∧ insert a (insert b P) ∈ D₂.K
    exact ⟨h_a_not_p, h_b_not_p, h_a_ground, h_b_ground,
      hab, h_edge_eq ▸ h_edge⟩
  obtain ⟨r, h_br, h_ra, h_label_ar⟩ :=
    reciprocal_arrow_witness_pair_link D₂ E P a b
      h_p_card h_p_ground h_b_ground h_b_not_p h_facet_a h_ab
  obtain ⟨s, h_as, h_sb, h_label_bs⟩ :=
    reciprocal_arrow_witness_pair_link D₂ E P b a
      h_p_card h_p_ground h_a_ground h_a_not_p h_facet_b h_ba
  have h_rs : r = s := by
    by_contra hrs
    have h_no_second := clear_reciprocal_fully_no_second
      D P h_p_card h_p_ground
    have h_ar : a ≠ r := Ne.symm h_ra
    have h_bs : b ≠ s := Ne.symm h_sb
    have h_as_ne : a ≠ s := by
      have h := h_as
      change a ∉ P ∧ s ∉ P ∧ a ∈ D₂.ground ∧ s ∈ D₂.ground ∧
        a ≠ s ∧ insert a (insert s P) ∈ D₂.K at h
      exact h.2.2.2.2.1
    have h_br_ne : b ≠ r := by
      have h := h_br
      change b ∉ P ∧ r ∉ P ∧ b ∈ D₂.ground ∧ r ∈ D₂.ground ∧
        b ≠ r ∧ insert b (insert r P) ∈ D₂.K at h
      exact h.2.2.2.2.1
    exact hrs (h_no_second a b r s h_pair h_br h_as
      hab h_ar h_as_ne h_br_ne h_bs hrs
      h_label_ar h_label_bs)
  subst s
  have h_ar : a ≠ r := Ne.symm h_ra
  have h_b_r_ne : b ≠ r := by
    have h := h_br
    change b ∉ P ∧ r ∉ P ∧ b ∈ D₂.ground ∧ r ∈ D₂.ground ∧
      b ≠ r ∧ insert b (insert r P) ∈ D₂.K at h
    exact h.2.2.2.2.1
  have h_degree := reciprocal_full_cleanup_opposite_facets_degree_two
    D P a b r h_p_card h_p_ground hab h_ar h_b_r_ne
    h_pair h_as h_br h_label_ar h_label_bs h_separated
  rw [h_facet_a]
  exact h_degree.2

/-- The fully cleaned actual completion data satisfies the degree-two
premise consumed by the reciprocal double count. -/
theorem clear_reciprocal_fully_degree_two_premise
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_separated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D)) :
    ∀ p ∈ actualReciprocalDirectedOccurrences
      (clearReciprocalFully D),
      (graphFacetCompletions (clearReciprocalFully D).K D.ground
        (p.1.erase p.2.1)).card = 2 := by
  classical
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have h_ground_2 : ∀ E ∈ D₂.K, E ⊆ D.ground := by
    intro E hE
    exact h_ground E
      (clear_reciprocal_different_witnesses_sub D
        (clear_reciprocal_wrong_common_witnesses_sub D₁ hE))
  intro p hp
  have h_parts := Finset.mem_filter.mp hp
  have h_edge : p.1 ∈ D₂.K :=
    (Finset.mem_product.mp h_parts.1).1
  exact reciprocal_full_cleanup_directed_opposite_degree_two
    D p.1 p.2.1 p.2.2 h_ground_2 h_separated h_edge
    h_parts.2.1 h_parts.2.2

/-- Actual finite `R ≤ b` after both reciprocal deletion rounds and
parent pair-label separation. All reciprocal occurrences and nonprivate
facets are computed from the final cleaned family. -/
theorem clear_reciprocal_fully_unordered_card_le_nonprivate
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_separated : ReciprocalUsedParentPairSeparation
      (clearReciprocalFully D)) :
    (actualReciprocalUnorderedOccurrences
      (clearReciprocalFully D)).card ≤
      (rankFourNonprivateFacets
        (clearReciprocalFully D).K D.ground).card := by
  let D₁ := clearReciprocalDifferentWitnesses D
  let D₂ := clearReciprocalFully D
  have h_ground_2 : ∀ E ∈ D₂.K, E ⊆ D.ground := by
    intro E hE
    exact h_ground E
      (clear_reciprocal_different_witnesses_sub D
        (clear_reciprocal_wrong_common_witnesses_sub D₁ hE))
  exact actual_reciprocal_unordered_card_le_nonprivate
    D₂ h_ground_2
    (clear_reciprocal_fully_degree_two_premise D h_ground h_separated)

end JSP523.Rank4
