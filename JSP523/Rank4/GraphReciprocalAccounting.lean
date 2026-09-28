import JSP523.Rank4.GraphActualDeficit

/-!
# Actual reciprocal arrows at a four-edge

The degree-two facet opposite a vertex of a reciprocal pair determines
that vertex's arrow target. This is the local uniqueness used when charging
reciprocal incidences to nonprivate facets in (III.B.9).
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The manuscript's arrow `a → b` at the actual edge `E`: a second
completion of the facet opposite `a` has pair label `b`. -/
def actualReciprocalArrow (D : FiniteCompletionCliqueData α)
    (E : Edge α) (a b : α) : Prop :=
  a ∈ E ∧ b ∈ E ∧ a ≠ b ∧
    ∃ x ∈ graphFacetCompletions D.K D.ground (E.erase a),
      x ≠ a ∧ D.label a x = b

/-- At a degree-two opposite facet, an actual arrow out of `a` has a
unique target. This uses the actual completion set and actual label. -/
theorem actual_reciprocal_arrow_target_unique
    (D : FiniteCompletionCliqueData α)
    (E : Edge α) (a b c : α)
    (h_edge : E ∈ D.K)
    (h_ground : E ⊆ D.ground)
    (h_degree :
      (graphFacetCompletions D.K D.ground (E.erase a)).card = 2)
    (h_ab : actualReciprocalArrow D E a b)
    (h_ac : actualReciprocalArrow D E a c) : b = c := by
  classical
  obtain ⟨h_a, _, _, x, h_x, h_xa, h_label_b⟩ := h_ab
  obtain ⟨_, _, _, y, h_y, h_ya, h_label_c⟩ := h_ac
  let C := graphFacetCompletions D.K D.ground (E.erase a)
  have h_a_completion : a ∈ C := by
    exact Finset.mem_filter.mpr
      ⟨h_ground h_a, by
        simpa [C, Finset.insert_erase h_a] using h_edge⟩
  have h_erase_card : (C.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem h_a_completion, h_degree]
  have h_x_erase : x ∈ C.erase a :=
    Finset.mem_erase.mpr ⟨h_xa, h_x⟩
  have h_y_erase : y ∈ C.erase a :=
    Finset.mem_erase.mpr ⟨h_ya, h_y⟩
  have h_xy : x = y :=
    Finset.card_le_one.mp (by omega : (C.erase a).card ≤ 1)
      x h_x_erase y h_y_erase
  calc
    b = D.label a x := h_label_b.symm
    _ = D.label a y := by rw [h_xy]
    _ = c := h_label_c

/-- Oriented reciprocal occurrences `(E,a,b)` in the actual cleaned
family. The two orientations of a reciprocal pair are both retained. -/
noncomputable def actualReciprocalDirectedOccurrences
    (D : FiniteCompletionCliqueData α) :
    Finset (Edge α × (α × α)) := by
  classical
  exact (D.K.product (D.ground.product D.ground)).filter fun p =>
    actualReciprocalArrow D p.1 p.2.1 p.2.2 ∧
      actualReciprocalArrow D p.1 p.2.2 p.2.1

/-- Forget the orientation of the reciprocal pair while retaining its
containing four-edge. -/
def actualReciprocalUnorderedKey
    (p : Edge α × (α × α)) : Edge α × Edge α :=
  (p.1, {p.2.1, p.2.2})

noncomputable def actualReciprocalUnorderedOccurrences
    (D : FiniteCompletionCliqueData α) :
    Finset (Edge α × Edge α) :=
  (actualReciprocalDirectedOccurrences D).image
    actualReciprocalUnorderedKey

def actualReciprocalSwap (p : Edge α × (α × α)) :
    Edge α × (α × α) :=
  (p.1, (p.2.2, p.2.1))

theorem actual_reciprocal_swap_mem
    (D : FiniteCompletionCliqueData α)
    (p : Edge α × (α × α))
    (hp : p ∈ actualReciprocalDirectedOccurrences D) :
    actualReciprocalSwap p ∈ actualReciprocalDirectedOccurrences D := by
  classical
  obtain ⟨h_product, h_arrow, h_reverse⟩ :=
    Finset.mem_filter.mp hp
  have h_ground := Finset.mem_product.mp h_product
  have h_points := Finset.mem_product.mp h_ground.2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr
      ⟨h_ground.1, Finset.mem_product.mpr ⟨h_points.2, h_points.1⟩⟩,
      h_reverse, h_arrow⟩

theorem actual_reciprocal_swap_ne
    (D : FiniteCompletionCliqueData α)
    (p : Edge α × (α × α))
    (hp : p ∈ actualReciprocalDirectedOccurrences D) :
    p ≠ actualReciprocalSwap p := by
  classical
  have h_arrow := (Finset.mem_filter.mp hp).2.1
  intro h
  have h_eq : p.2.1 = p.2.2 :=
    congrArg (fun q : Edge α × (α × α) => q.2.1) h
  exact h_arrow.2.2.1 h_eq

/-- Every unordered actual reciprocal occurrence has precisely the two
orientations `(a,b)` and `(b,a)`. -/
theorem actual_reciprocal_unordered_fiber_card
    (D : FiniteCompletionCliqueData α)
    (q : Edge α × Edge α)
    (hq : q ∈ actualReciprocalUnorderedOccurrences D) :
    ((actualReciprocalDirectedOccurrences D).filter fun p =>
      actualReciprocalUnorderedKey p = q).card = 2 := by
  classical
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  let R := actualReciprocalDirectedOccurrences D
  let s := actualReciprocalSwap p
  have hs : s ∈ R := actual_reciprocal_swap_mem D p hp
  have h_ne : p ≠ s := actual_reciprocal_swap_ne D p hp
  have h_key_swap : actualReciprocalUnorderedKey s =
      actualReciprocalUnorderedKey p := by
    simp [s, actualReciprocalUnorderedKey, actualReciprocalSwap,
      Finset.pair_comm]
  have h_fiber : (R.filter fun r =>
      actualReciprocalUnorderedKey r = q) = {p, s} := by
    ext r
    constructor
    · intro hr
      have h_key : actualReciprocalUnorderedKey r =
          actualReciprocalUnorderedKey p :=
        (Finset.mem_filter.mp hr).2.trans hpq.symm
      have h_edge : r.1 = p.1 :=
        congrArg (fun z : Edge α × Edge α => z.1) h_key
      have h_pair : ({r.2.1, r.2.2} : Edge α) =
          {p.2.1, p.2.2} :=
        congrArg (fun z : Edge α × Edge α => z.2) h_key
      have h_offdiag : p.2.1 ≠ p.2.2 :=
        (Finset.mem_filter.mp hp).2.1.2.2.1
      rcases pair_finset_eq_oriented_eq h_offdiag h_pair with
        h_same | h_swap
      · have h_eq : r = p :=
          Prod.ext h_edge (Prod.ext h_same.1.symm h_same.2.symm)
        simp [h_eq]
      · have h_eq : r = s :=
          Prod.ext h_edge (Prod.ext h_swap.2.symm h_swap.1.symm)
        simp [h_eq]
    · intro hr
      rcases Finset.mem_insert.mp hr with h_eq | hr
      · subst r
        exact Finset.mem_filter.mpr ⟨hp, hpq⟩
      · have h_eq : r = s := Finset.mem_singleton.mp hr
        subst r
        exact Finset.mem_filter.mpr ⟨hs, h_key_swap.trans hpq⟩
  rw [h_fiber, Finset.card_pair h_ne]

/-- The directed occurrence count is exactly twice the unordered count. -/
theorem actual_reciprocal_directed_card_eq_twice_unordered
    (D : FiniteCompletionCliqueData α) :
    (actualReciprocalDirectedOccurrences D).card =
      2 * (actualReciprocalUnorderedOccurrences D).card := by
  classical
  let R := actualReciprocalDirectedOccurrences D
  let Q := actualReciprocalUnorderedOccurrences D
  have h_count : R.card =
      ∑ q ∈ Q, (R.filter fun p =>
        actualReciprocalUnorderedKey p = q).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  rw [h_count]
  calc
    (∑ q ∈ Q, (R.filter fun p =>
        actualReciprocalUnorderedKey p = q).card) =
        ∑ _q ∈ Q, (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact actual_reciprocal_unordered_fiber_card D q hq
    _ = 2 * Q.card := by simp [mul_comm]

/-- Actual facets with exactly two completions. -/
def rankFourDegreeTwoFacets (K : Family α) (U : Edge α) :
    Family α :=
  (U.powersetCard 3).filter fun T =>
    (facetCompletions K U T).card = 2

/-- Each directed reciprocal occurrence determines its opposite facet
and deleted vertex. The degree-two property makes this record injective:
the other completion determines the arrow target. -/
theorem actual_reciprocal_opposite_record_injective
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_degree : ∀ p ∈ actualReciprocalDirectedOccurrences D,
      (graphFacetCompletions D.K D.ground (p.1.erase p.2.1)).card = 2) :
    Set.InjOn (fun p : Edge α × (α × α) => (p.1.erase p.2.1, p.2.1))
      (↑(actualReciprocalDirectedOccurrences D) :
        Set (Edge α × (α × α))) := by
  classical
  intro p hp q hq h_record
  have hp_parts := Finset.mem_filter.mp hp
  have hq_parts := Finset.mem_filter.mp hq
  have hp_edge : p.1 ∈ D.K := (Finset.mem_product.mp hp_parts.1).1
  have hq_edge : q.1 ∈ D.K := (Finset.mem_product.mp hq_parts.1).1
  have hp_arrow := hp_parts.2.1
  have hq_arrow := hq_parts.2.1
  have h_a : p.2.1 = q.2.1 := congrArg Prod.snd h_record
  have h_t : p.1.erase p.2.1 = q.1.erase q.2.1 :=
    congrArg Prod.fst h_record
  have h_edge : p.1 = q.1 := by
    calc
      p.1 = insert p.2.1 (p.1.erase p.2.1) :=
        (Finset.insert_erase hp_arrow.1).symm
      _ = insert p.2.1 (q.1.erase q.2.1) :=
        congrArg (insert p.2.1) h_t
      _ = insert q.2.1 (q.1.erase q.2.1) :=
        congrArg (fun z => insert z (q.1.erase q.2.1)) h_a
      _ = q.1 := Finset.insert_erase hq_arrow.1
  have h_b : p.2.2 = q.2.2 := by
    have h_q_arrow : actualReciprocalArrow D p.1 p.2.1 q.2.2 := by
      rw [h_edge, h_a]
      exact hq_arrow
    exact actual_reciprocal_arrow_target_unique D p.1 p.2.1
      p.2.2 q.2.2 hp_edge (h_ground p.1 hp_edge)
      (h_degree p hp) hp_arrow h_q_arrow
  exact Prod.ext h_edge (Prod.ext h_a h_b)

/-- A degree-two facet together with one of its two completion vertices. -/
noncomputable def rankFourDegreeTwoCompletionRecords
    (K : Family α) (U : Edge α) : Finset (Edge α × α) :=
  (rankFourDegreeTwoFacets K U).biUnion fun T =>
    (facetCompletions K U T).image fun a => (T, a)

/-- There are exactly two completion records per degree-two facet. -/
theorem rank_four_degree_two_completion_records_card
    (K : Family α) (U : Edge α) :
    (rankFourDegreeTwoCompletionRecords K U).card =
      2 * (rankFourDegreeTwoFacets K U).card := by
  classical
  let F := rankFourDegreeTwoFacets K U
  let C := fun T : Edge α =>
    (facetCompletions K U T).image fun a => (T, a)
  have h_disjoint : Set.Pairwise (↑F : Set (Edge α))
      fun T S => Disjoint (C T) (C S) := by
    intro T _ S _ hTS
    apply Finset.disjoint_left.mpr
    intro r hrT hrS
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hrT
    obtain ⟨b, _, hEq⟩ := Finset.mem_image.mp hrS
    exact hTS (congrArg Prod.fst hEq.symm)
  have h_each : ∀ T ∈ F, (C T).card = 2 := by
    intro T hT
    have hInj : Function.Injective (fun a : α => (T, a)) := by
      intro a b hab
      exact congrArg Prod.snd hab
    rw [Finset.card_image_of_injective _ hInj]
    exact (Finset.mem_filter.mp hT).2
  calc
    (rankFourDegreeTwoCompletionRecords K U).card =
        ∑ T ∈ F, (C T).card := Finset.card_biUnion h_disjoint
    _ = ∑ _T ∈ F, (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact h_each T hT
    _ = 2 * F.card := by simp [mul_comm]

/-- The actual double count behind `R ≤ b`: each oriented reciprocal
occurrence occupies a distinct degree-two facet/completion record.
The local isolated-reciprocal property is expressed by `h_degree`. -/
theorem actual_reciprocal_directed_card_le_twice_nonprivate
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_degree : ∀ p ∈ actualReciprocalDirectedOccurrences D,
      (graphFacetCompletions D.K D.ground (p.1.erase p.2.1)).card = 2) :
    (actualReciprocalDirectedOccurrences D).card ≤
      2 * (rankFourNonprivateFacets D.K D.ground).card := by
  classical
  let R := actualReciprocalDirectedOccurrences D
  let f : Edge α × (α × α) → Edge α × α :=
    fun p => (p.1.erase p.2.1, p.2.1)
  have h_image_sub : R.image f ⊆
      rankFourDegreeTwoCompletionRecords D.K D.ground := by
    intro r hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
    have hp_parts := Finset.mem_filter.mp hp
    have h_edge : p.1 ∈ D.K := (Finset.mem_product.mp hp_parts.1).1
    have h_a : p.2.1 ∈ p.1 := hp_parts.2.1.1
    let T := p.1.erase p.2.1
    have h_t_ground : T ⊆ D.ground :=
      (Finset.erase_subset _ _).trans (h_ground p.1 h_edge)
    have h_t_card : T.card = 3 := by
      have h_four := D.uniform_four h_edge
      rw [Finset.card_erase_of_mem h_a]
      omega
    have h_t_degree : (facetCompletions D.K D.ground T).card = 2 :=
      h_degree p hp
    have h_t : T ∈ rankFourDegreeTwoFacets D.K D.ground :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨h_t_ground, h_t_card⟩,
          h_t_degree⟩
    have h_completion : p.2.1 ∈ facetCompletions D.K D.ground T := by
      exact Finset.mem_filter.mpr
        ⟨h_ground p.1 h_edge h_a, by
          simpa [T, Finset.insert_erase h_a] using h_edge⟩
    exact Finset.mem_biUnion.mpr
      ⟨T, h_t, Finset.mem_image.mpr ⟨p.2.1, h_completion, rfl⟩⟩
  have h_inj := actual_reciprocal_opposite_record_injective
    D h_ground h_degree
  have h_card_image : R.card = (R.image f).card :=
    (Finset.card_image_of_injOn h_inj).symm
  have h_target := rank_four_degree_two_completion_records_card
    D.K D.ground
  have h_degree_two_sub :
      rankFourDegreeTwoFacets D.K D.ground ⊆
        rankFourNonprivateFacets D.K D.ground := by
    intro T hT
    have h := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨h.1, by omega⟩
  have h_b := Finset.card_le_card h_degree_two_sub
  have h_image := Finset.card_le_card h_image_sub
  change R.card ≤ 2 * (rankFourNonprivateFacets D.K D.ground).card
  omega

/-- The manuscript's `R ≤ b` for the actual unordered reciprocal pairs.
The sole remaining local premise is that reciprocal triangles have been
isolated, so each opposite facet has degree two. -/
theorem actual_reciprocal_unordered_card_le_nonprivate
    (D : FiniteCompletionCliqueData α)
    (h_ground : ∀ E ∈ D.K, E ⊆ D.ground)
    (h_degree : ∀ p ∈ actualReciprocalDirectedOccurrences D,
      (graphFacetCompletions D.K D.ground (p.1.erase p.2.1)).card = 2) :
    (actualReciprocalUnorderedOccurrences D).card ≤
      (rankFourNonprivateFacets D.K D.ground).card := by
  have h_oriented := actual_reciprocal_directed_card_le_twice_nonprivate
    D h_ground h_degree
  have h_count := actual_reciprocal_directed_card_eq_twice_unordered D
  omega

end JSP523.Rank4
