import JSP523.Rank3.RootedSignedWeights

/-!
# Exclusion of large receiving common links

The rank-three charging argument sends a positive rooted weight from a
source pair to another completion pair.  This module proves the local
obstruction used to exclude a receiving cell with at least three base pairs:
each other base pair supplies a distinct weak alternative to the source.
-/

namespace JSP523.Rank3

section ReceiverExclusion

variable {α : Type*} [DecidableEq α]

private theorem pair_eq_of_two_members
    {p : Edge α} {a b : α}
    (hp : p.card = 2) (ha : a ∈ p) (hb : b ∈ p)
    (hab : a ≠ b) : p = {a, b} := by
  have hsub : ({a, b} : Edge α) ⊆ p := by
    intro t ht
    rcases Finset.mem_insert.mp ht with hta | htb
    · exact hta ▸ ha
    · exact (Finset.mem_singleton.mp htb) ▸ hb
  have hcard : p.card ≤ ({a, b} : Edge α).card := by
    rw [hp, Finset.card_pair hab]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- A pair other than `{x,y}` that meets `{x,y}` has exactly one of its
    endpoints, with the other endpoint uniquely determining the pair. -/
private theorem other_pair_decomposition
    {p : Edge α} {x y : α}
    (hp : p.card = 2) (hxy : x ≠ y)
    (hne : p ≠ ({x, y} : Edge α))
    (hmeets : ¬ Disjoint p ({x, y} : Edge α)) :
    (∃ u : α, x ≠ u ∧ y ≠ u ∧ p = {x, u}) ∨
      (∃ u : α, y ≠ u ∧ x ≠ u ∧ p = {y, u}) := by
  have hxyMem : x ∈ p ∨ y ∈ p := by
    by_contra h
    have hx : x ∉ p := fun hpx => h (Or.inl hpx)
    have hy : y ∉ p := fun hpy => h (Or.inr hpy)
    apply hmeets
    apply Finset.disjoint_left.mpr
    intro t ht hpSource
    rcases Finset.mem_insert.mp hpSource with htx | hty
    · exact hx (htx ▸ ht)
    · exact hy ((Finset.mem_singleton.mp hty) ▸ ht)
  rcases hxyMem with hx | hy
  · have hyNot : y ∉ p := by
      intro hyMem
      exact hne (pair_eq_of_two_members hp hx hyMem hxy)
    have hmore : (p.erase x).Nonempty := by
      apply Finset.card_pos.mp
      have hErase := Finset.card_erase_add_one hx
      omega
    obtain ⟨u, huErase⟩ := hmore
    have hux : u ≠ x := (Finset.mem_erase.mp huErase).1
    have hu : u ∈ p := (Finset.mem_erase.mp huErase).2
    have hyu : y ≠ u := by
      intro h
      exact hyNot (h ▸ hu)
    exact Or.inl ⟨u, Ne.symm hux, hyu,
      pair_eq_of_two_members hp hx hu (Ne.symm hux)⟩
  · have hxNot : x ∉ p := by
      intro hxMem
      exact hne (pair_eq_of_two_members hp hxMem hy hxy)
    have hmore : (p.erase y).Nonempty := by
      apply Finset.card_pos.mp
      have hErase := Finset.card_erase_add_one hy
      omega
    obtain ⟨u, huErase⟩ := hmore
    have huy : u ≠ y := (Finset.mem_erase.mp huErase).1
    have hu : u ∈ p := (Finset.mem_erase.mp huErase).2
    have hxu : x ≠ u := by
      intro h
      exact hxNot (h ▸ hu)
    exact Or.inr ⟨u, Ne.symm huy, hxu,
      pair_eq_of_two_members hp hy hu (Ne.symm huy)⟩

/-- Every other base pair at a receiving cell comes from one of the two
    weak-alternative sets of the source rooted edge. -/
theorem other_receiving_pairs_covered_by_weak_alternatives
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ orientedCommonLink H V z v) :
    ((orientedCommonLink H V z v).erase ({x, y} : Edge α)) ⊆
      ((weakRightAlternatives H V z x y).image
        (fun u => ({x, u} : Edge α))) ∪
      ((weakLeftAlternatives H V z x y).image
        (fun u => ({y, u} : Edge α))) := by
  intro p hp
  have hpLink : p ∈ orientedCommonLink H V z v :=
    (Finset.mem_erase.mp hp).2
  have hpNe : p ≠ ({x, y} : Edge α) :=
    (Finset.mem_erase.mp hp).1
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpLink).1).2
  have hmeet := oriented_common_link_intersecting hH hzv hpLink hsource
  rcases other_pair_decomposition hp2 hxy hpNe hmeet with
    ⟨u, hxu, hyu, hpair⟩ | ⟨u, hyu, hxu, hpair⟩
  · have hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V z v := by
      rw [← hpair]
      exact hpLink
    have huWeak := second_book_pair_mem_weak_right_alternatives
      hH hzV hvV hzv hxy hxu hyu hsource hxuLink
    apply Finset.mem_union.mpr
    left
    rw [hpair]
    exact Finset.mem_image_of_mem _ huWeak
  · have hyxSource : ({y, x} : Edge α) ∈ orientedCommonLink H V z v := by
      simpa only [Finset.pair_comm] using hsource
    have hyuLink : ({y, u} : Edge α) ∈ orientedCommonLink H V z v := by
      rw [← hpair]
      exact hpLink
    have huWeak : u ∈ weakRightAlternatives H V z y x :=
      second_book_pair_mem_weak_right_alternatives
        hH hzV hvV hzv (Ne.symm hxy) hyu hxu hyxSource hyuLink
    have huWeakLeft : u ∈ weakLeftAlternatives H V z x y := huWeak
    apply Finset.mem_union.mpr
    right
    rw [hpair]
    exact Finset.mem_image_of_mem _ huWeakLeft

/-- If a receiving common link has at least three base pairs, the source
    edge has at least two weak alternatives. -/
theorem two_weak_alternatives_of_large_receiving_link
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hlarge : 3 ≤ (orientedCommonLink H V z v).card) :
    2 ≤ (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card := by
  have hcover := other_receiving_pairs_covered_by_weak_alternatives
    hH hzV hvV hzv hxy hsource
  have hErase := Finset.card_erase_add_one hsource
  have hcard := Finset.card_le_card hcover
  have hUnion := Finset.card_union_le
    ((weakRightAlternatives H V z x y).image
      (fun u => ({x, u} : Edge α)))
    ((weakLeftAlternatives H V z x y).image
      (fun u => ({y, u} : Edge α)))
  have hright := Finset.card_image_le
    (s := weakRightAlternatives H V z x y)
    (f := fun u => ({x, u} : Edge α))
  have hleft := Finset.card_image_le
    (s := weakLeftAlternatives H V z x y)
    (f := fun u => ({y, u} : Edge α))
  omega

/-- A receiving cell with at least three base pairs cannot receive a
    positive signed weight from any of its source edges. -/
theorem rooted_signed_weight_nonpos_of_large_receiving_link
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hlarge : 3 ≤ (orientedCommonLink H V z v).card) :
    rootedSignedWeight H V z x y ≤ 0 := by
  have htwo := two_weak_alternatives_of_large_receiving_link
    hH hzV hvV hzv hxy hsource hlarge
  exact rooted_signed_weight_nonpos_of_two_weak_alternatives H V
    (oriented_common_link_pair_mem_root_link H V hsource) hxy htwo

/-- A two-base-pair receiving common link supplies one weak alternative,
    so each source weight aimed at that cell is strictly below one. -/
theorem rooted_signed_weight_lt_one_of_double_receiving_link
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y)
    (hsource : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hdouble : (orientedCommonLink H V z v).card = 2) :
    rootedSignedWeight H V z x y < 1 := by
  have hcover := other_receiving_pairs_covered_by_weak_alternatives
    hH hzV hvV hzv hxy hsource
  have hErase := Finset.card_erase_add_one hsource
  have hnonempty :
      ((orientedCommonLink H V z v).erase ({x, y} : Edge α)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnonempty
  have hcovered := hcover hp
  have hcount : 1 ≤ (weakLeftAlternatives H V z x y).card +
      (weakRightAlternatives H V z x y).card := by
    rcases Finset.mem_union.mp hcovered with hright | hleft
    · obtain ⟨u, hu, _⟩ := Finset.mem_image.mp hright
      have hpos := Finset.card_pos.mpr ⟨u, hu⟩
      omega
    · obtain ⟨u, hu, _⟩ := Finset.mem_image.mp hleft
      have hpos := Finset.card_pos.mpr ⟨u, hu⟩
      omega
  exact rooted_signed_weight_lt_one_of_weak_alternative H V
    (oriented_common_link_pair_mem_root_link H V hsource) hxy hcount

/-- A second completion vertex of a rooted source pair makes that pair a
    base pair in the common link of the two completion vertices. -/
theorem source_pair_mem_receiving_link
    (H : Family α) (V : Edge α) {z v x y : α}
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hv : v ∈ completionVertices H V ({x, y} : Edge α)) :
    ({x, y} : Edge α) ∈ orientedCommonLink H V z v := by
  obtain ⟨hxyV, hzOut, hxz⟩ := Finset.mem_filter.mp hsource
  obtain ⟨_, hvOut, hxv⟩ := Finset.mem_filter.mp hv
  have hdis : Disjoint ({x, y} : Edge α) ({z, v} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht htv
    rcases Finset.mem_insert.mp htv with htz | htv'
    · exact hzOut (htz ▸ ht)
    · exact hvOut ((Finset.mem_singleton.mp htv') ▸ ht)
  exact Finset.mem_filter.mpr ⟨hxyV, hdis, hxz, hxv⟩

/-- A positive source weight can be sent only to a receiving common link
    with at most two base pairs. -/
theorem positive_source_receiving_link_card_le_two
    {H : Family α} {V : Edge α} {z v x y : α}
    (hH : Admissible H)
    (hzV : z ∈ V)
    (hsource : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxy : x ≠ y)
    (hv : v ∈ completionVertices H V ({x, y} : Edge α))
    (hzv : z ≠ v)
    (hpositive : 0 < rootedSignedWeight H V z x y) :
    (commonLink H V ({z, v} : Edge α)).card ≤ 2 := by
  have hvV : v ∈ V := (Finset.mem_filter.mp hv).1
  have hsourceLink := source_pair_mem_receiving_link H V hsource hv
  have hcardEq :
      (commonLink H V ({z, v} : Edge α)).card =
      (orientedCommonLink H V z v).card := by
    congr 1
    ext p
    exact mem_common_link_pair_iff_oriented H V hzv p
  by_contra h
  have hlarge : 3 ≤ (orientedCommonLink H V z v).card := by omega
  have hnonpos := rooted_signed_weight_nonpos_of_large_receiving_link
    hH hzV hvV hzv hxy hsourceLink hlarge
  linarith

end ReceiverExclusion

end JSP523.Rank3
