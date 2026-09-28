import JSP523.Rank3.ReceiverExclusion
import JSP523.Rank3.RootCommonLinkFibers
import Mathlib.Tactic.FinCases

/-!
# Structural nonduplication of rank-three bridge demands

This module records the bridge-book structures and the finite counting
step used after their nine triples have been extracted. -/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem root_common_neighbors_comm
    (H : Family α) (V : Edge α) (z x y : α) :
    rootCommonNeighbors H V z x y = rootCommonNeighbors H V z y x := by
  ext t
  simp [rootCommonNeighbors, and_left_comm, and_comm]

/-- No five-vertex set spans exactly nine or ten triples. -/
def NoNineOrTenTripleBlock (H : JSP523.Family α) : Prop :=
  ∀ S : Edge α, S.card = 5 →
    let n := (Finset.filter (fun E : Edge α => E ⊆ S) H).card
    n ≠ 9 ∧ n ≠ 10

/-- The nine triples forced in the coincident-page case. -/
def bridgeOverlapTripleSet (a b c x u : α) : Family α :=
  {{a, b, c}, {a, b, u}, {a, c, x}, {a, x, u}, {b, c, x},
    {b, x, u}, {a, c, u}, {a, b, x}, {c, x, u}}

private def bridgeStd : Finset (Finset (Fin 5)) :=
  {{0, 1, 2}, {0, 1, 4}, {0, 2, 3}, {0, 3, 4}, {1, 2, 3},
    {1, 3, 4}, {0, 2, 4}, {0, 1, 3}, {2, 3, 4}}

private theorem bridge_std_card : bridgeStd.card = 9 := by
  decide

private def bridgeF (a b c x u : α) (i : Fin 5) : α :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c
    else if i = 3 then x else u

/-- The nine listed triples are distinct whenever their five vertices are
pairwise distinct. -/
theorem bridge_overlap_triple_set_card
    {a b c x u : α}
    (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x) (hau : a ≠ u)
    (hbc : b ≠ c) (hbx : b ≠ x) (hbu : b ≠ u)
    (hcx : c ≠ x) (hcu : c ≠ u) (hxu : x ≠ u) :
    (bridgeOverlapTripleSet a b c x u).card = 9 := by
  let f : Fin 5 → α := bridgeF a b c x u
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, bridgeF]
  have hset : bridgeOverlapTripleSet a b c x u =
      bridgeStd.image (fun e => e.image f) := by
    ext e
    simp [bridgeOverlapTripleSet, bridgeStd, f, bridgeF]
  rw [hset, Finset.card_image_of_injective _ (Finset.image_injective hf)]
  exact bridge_std_card


/-- The two books from Theorem II.C.1, represented by their actual common
links. -/
structure DoubleBridgeBook (H : JSP523.Family α) (V : Edge α)
    (a b c x u y v : α) : Prop where
  ab : orientedCommonLink H V b a = ({{x, c}, {x, u}} : Family α)
  cu : orientedCommonLink H V c u = ({{a, b}, {a, x}, {b, x}} : Family α)
  ac : orientedCommonLink H V c a = ({{y, b}, {y, v}} : Family α)
  bv : orientedCommonLink H V b v = ({{a, c}, {a, y}, {c, y}} : Family α)

private theorem oriented_link_left_extension
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hp : p ∈ orientedCommonLink H V z v) : p ∪ {z} ∈ H :=
  (Finset.mem_filter.mp hp).2.2.1

private theorem oriented_link_right_extension
    {H : Family α} {V : Edge α} {z v : α} {p : Edge α}
    (hp : p ∈ orientedCommonLink H V z v) : p ∪ {v} ∈ H :=
  (Finset.mem_filter.mp hp).2.2.2

/-- The two page pairs forced into `J_ax` cannot be disjoint, so their
outside vertices must agree.  This is the admissibility step used after
extracting the pairs `{b,u}` and `{c,v}` from the four books. -/
theorem pages_in_same_link_equal
    {H : Family α} {V : Edge α} {a b c x u v : α}
    (hH : Admissible H) (hax : a ≠ x)
    (hbc : b ≠ c) (hcu : c ≠ u)
    (hbv : b ≠ v)
    (hbuLink : ({b, u} : Edge α) ∈ orientedCommonLink H V a x)
    (hcvLink : ({c, v} : Edge α) ∈ orientedCommonLink H V a x) :
    u = v := by
  by_contra huv
  have hmeet := oriented_common_link_intersecting hH hax hbuLink hcvLink
  apply hmeet
  apply Finset.disjoint_left.mpr
  intro t htB htC
  have htB' : t = b ∨ t = u := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using htB
  have htC' : t = c ∨ t = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using htC
  rcases htB' with htb | htu <;> rcases htC' with htc | htv
  · exact hbc (htb.symm.trans htc)
  · exact hbv (htb.symm.trans htv)
  · exact hcu (htc.symm.trans htu)
  · exact huv (htu.symm.trans htv)

/-- Extract `{b,u}` and `{c,v}` into the actual common link `J_ax` from
the four book links.  Admissibility then identifies the page vertices. -/
theorem double_book_overlap_pages_equal
    {H : Family α} {V : Edge α} {a b c x u v : α}
    (hH : Admissible H)
    (hBook : DoubleBridgeBook H V a b c x u x v)
    (hvV : v ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x)
    (hbx : b ≠ x) (hcx : c ≠ x) (hbc : b ≠ c)
    (hbu : b ≠ u) (hau : a ≠ u) (hxu : x ≠ u)
    (hcv : c ≠ v) (hav : a ≠ v) (hxv : x ≠ v)
    (hcu : c ≠ u) (hbv : b ≠ v) :
    u = v := by
  have habCu : ({a, b} : Edge α) ∈ orientedCommonLink H V c u := by
    rw [hBook.cu]
    simp
  have hxuBa : ({x, u} : Edge α) ∈ orientedCommonLink H V b a := by
    rw [hBook.ab]
    simp
  have hacBv : ({a, c} : Edge α) ∈ orientedCommonLink H V b v := by
    rw [hBook.bv]
    simp
  have hcxBv : ({c, x} : Edge α) ∈ orientedCommonLink H V b v := by
    rw [hBook.bv]
    simp
  have habu : ({a, b} : Edge α) ∪ {u} ∈ H :=
    oriented_link_right_extension habCu
  have hbxu : ({x, u} : Edge α) ∪ {b} ∈ H :=
    oriented_link_left_extension hxuBa
  have hacv : ({a, c} : Edge α) ∪ {v} ∈ H :=
    oriented_link_right_extension hacBv
  have hcxv : ({c, x} : Edge α) ∪ {v} ∈ H :=
    oriented_link_right_extension hcxBv
  have hbV : b ∈ V := by
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp habCu).1).1 (by simp)
  have huV : u ∈ V := by
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hxuBa).1).1 (by simp)
  have hcV : c ∈ V := by
    exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hacBv).1).1 (by simp)
  have hbuV : ({b, u} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htb | htu
      · exact htb ▸ hbV
      · exact (Finset.mem_singleton.mp htu) ▸ huV
    · exact Finset.card_pair hbu
  have hcvV : ({c, v} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htc | htv
      · exact htc ▸ hcV
      · exact (Finset.mem_singleton.mp htv) ▸ hvV
    · exact Finset.card_pair hcv
  have hdisBu : Disjoint ({b, u} : Edge α) ({a, x} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht hp
    rcases ht with htb | htu <;> rcases hp with hta | htx
    · exact hab (hta.symm.trans htb)
    · exact hbx (htb.symm.trans htx)
    · exact hau (hta.symm.trans htu)
    · exact hxu (htx.symm.trans htu)
  have hdisCv : Disjoint ({c, v} : Edge α) ({a, x} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht hp
    rcases ht with htc | htv <;> rcases hp with hta | htx
    · exact hac (hta.symm.trans htc)
    · exact hcx (htc.symm.trans htx)
    · exact hav (hta.symm.trans htv)
    · exact hxv (htx.symm.trans htv)
  have hbuA : ({b, u} : Edge α) ∪ {a} = ({a, b} : Edge α) ∪ {u} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hbuX : ({b, u} : Edge α) ∪ {x} = ({x, u} : Edge α) ∪ {b} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hcvA : ({c, v} : Edge α) ∪ {a} = ({a, c} : Edge α) ∪ {v} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hcvX : ({c, v} : Edge α) ∪ {x} = ({c, x} : Edge α) ∪ {v} := by
    ext t
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hbuLink : ({b, u} : Edge α) ∈ orientedCommonLink H V a x :=
    Finset.mem_filter.mpr ⟨hbuV, hdisBu,
      hbuA.symm ▸ habu, hbuX.symm ▸ hbxu⟩
  have hcvLink : ({c, v} : Edge α) ∈ orientedCommonLink H V a x :=
    Finset.mem_filter.mpr ⟨hcvV, hdisCv,
      hcvA.symm ▸ hacv, hcvX.symm ▸ hcxv⟩
  exact pages_in_same_link_equal hH hax hbc hcu hbv hbuLink hcvLink

/-- A common-link center is forced to equal any root whose fiber already
contains at least two distinct pairs. -/
theorem common_link_center_eq_of_root_fiber_large
    {H : Family α} {V : Edge α} {z x y center : α}
    (hzV : z ∈ V) (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y)
    (hmu : 2 ≤ (rootCommonNeighbors H V z x y).card)
    (hcenter : ∀ p ∈ commonLink H V ({x, y} : Edge α), center ∈ p) :
    center = z := by
  have hfiber := root_common_neighbors_eq_common_link_fiber H V hzV hzx hzy hxy
  have hbig : 1 < (commonLinkFiber H V ({x, y} : Edge α) z).card := by
    rw [← hfiber]
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, htNe⟩ := Finset.one_lt_card.mp hbig
  have hpair₁ : ({z, t₁} : Edge α) ∈ commonLink H V ({x, y} : Edge α) :=
    (Finset.mem_filter.mp ht₁).2
  have hpair₂ : ({z, t₂} : Edge α) ∈ commonLink H V ({x, y} : Edge α) :=
    (Finset.mem_filter.mp ht₂).2
  have hznot₁ : t₁ ≠ z := by
    intro heq
    have hcard : ({z, t₁} : Edge α).card = 2 := by
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hpair₁).1).2
    simp [heq] at hcard
  have hznot₂ : t₂ ≠ z := by
    intro heq
    have hcard : ({z, t₂} : Edge α).card = 2 := by
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hpair₂).1).2
    simp [heq] at hcard
  have hc₁ := hcenter _ hpair₁
  have hc₂ := hcenter _ hpair₂
  by_contra hcz
  have hct₁ : center = t₁ := by
    have hmem : center = z ∨ center = t₁ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc₁
    rcases hmem with h | h
    · exact False.elim (hcz h)
    · exact h
  have hct₂ : center = t₂ := by
    have hmem : center = z ∨ center = t₂ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc₂
    rcases hmem with h | h
    · exact False.elim (hcz h)
    · exact h
  exact htNe (hct₁.symm.trans hct₂)

/-- Two roots with four common neighbors would both be the unique center
of the same actual common link. -/
theorem two_large_root_fibers_impossible
    {H : Family α} {V : Edge α} {b c x y : α}
    (hH : Admissible H)
    (hbV : b ∈ V) (hcV : c ∈ V) (hxV : x ∈ V) (hyV : y ∈ V)
    (hbc : b ≠ c) (hbx : b ≠ x) (hby : b ≠ y)
    (hcx : c ≠ x) (hcy : c ≠ y) (hxy : x ≠ y)
    (hB : 4 ≤ (rootCommonNeighbors H V b x y).card)
    (hC : 4 ≤ (rootCommonNeighbors H V c x y).card) : False := by
  have hq : ({x, y} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htx | hty
      · exact htx ▸ hxV
      · exact (Finset.mem_singleton.mp hty) ▸ hyV
    · exact Finset.card_pair hxy
  have hBfiber := root_common_neighbors_eq_common_link_fiber H V hbV
    hbx hby hxy
  have hClarge : 3 < (commonLink H V ({x, y} : Edge α)).card := by
    have hle := common_link_fiber_card_le_common_link_card
      H V ({x, y} : Edge α) b
    rw [← hBfiber] at hle
    omega
  obtain ⟨center, hcenter, hunique⟩ :=
    actual_common_link_unique_center_of_large hH hq hClarge
  have hcenterB := common_link_center_eq_of_root_fiber_large
    hbV hbx hby hxy (by omega) hcenter
  have hcenterC := common_link_center_eq_of_root_fiber_large
    hcV hcx hcy hxy (by omega) hcenter
  exact hbc (hcenterB.symm.trans hcenterC)

/-- If a positive rooted edge already has its book alternative, then every
different adjacent edge on the other endpoint must have at least four
common neighbors with the first endpoint. -/
theorem positive_rooted_edge_forces_other_common_neighbors_large
    {H : Family α} {V : Edge α} {z x c u y : α}
    (hsource : ({x, c} : Edge α) ∈ rootLink H V z)
    (hxc : x ≠ c) (hpositive : 0 < rootedSignedWeight H V z x c)
    (huWeak : u ∈ weakRightAlternatives H V z x c)
    (hcy : ({c, y} : Edge α) ∈ rootLink H V z)
    (hyx : y ≠ x) :
    4 ≤ (rootCommonNeighbors H V z x y).card := by
  by_contra hlarge
  have hsmall : (rootCommonNeighbors H V z x y).card ≤ 3 := by omega
  have hcyNe : c ≠ y := by
    intro h
    have hcard : ({c, y} : Edge α).card = 2 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hcy).1).2
    simp [h] at hcard
  have hyNeighbor : y ∈ rootNeighbors H V z c :=
    (root_link_edge_in_endpoint_neighbors H V hcy hcyNe).1
  have hyWeak : y ∈ weakLeftAlternatives H V z x c := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_erase.mpr ⟨hyx, hyNeighbor⟩
    · exact hsmall
  have hleft : 0 < (weakLeftAlternatives H V z x c).card :=
    Finset.card_pos.mpr ⟨y, hyWeak⟩
  have hright : 0 < (weakRightAlternatives H V z x c).card :=
    Finset.card_pos.mpr ⟨u, huWeak⟩
  have hcount := positive_rooted_signed_weight_weak_count_le_one
    H V hsource hxc hpositive
  omega

/-- The unequal-overlap branch of Theorem II.C.1.  The book equalities
produce the mandatory weak alternatives and the opposite adjacencies; the
positive-weight protection lemma then gives two incompatible centers of
the actual common link `J_xy`. -/
theorem double_bridge_books_x_ne_y_impossible
    {H : Family α} {V : Edge α} {a b c x u y v : α}
    (hH : Admissible H)
    (hBook : DoubleBridgeBook H V a b c x u y v)
    (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hxV : x ∈ V) (hyV : y ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxb : x ≠ b) (hxc : x ≠ c)
    (huc : u ≠ c) (hxu : x ≠ u)
    (hyb : y ≠ b) (hyc : y ≠ c) (hxy : x ≠ y)
    (hvb : v ≠ b) (hyv : y ≠ v)
    (hposB : 0 < rootedSignedWeight H V b x c)
    (hposC : 0 < rootedSignedWeight H V c y b) : False := by
  have hxcLink : ({x, c} : Edge α) ∈ orientedCommonLink H V b a := by
    rw [hBook.ab]
    simp
  have hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V b a := by
    rw [hBook.ab]
    simp
  have hybLink : ({y, b} : Edge α) ∈ orientedCommonLink H V c a := by
    rw [hBook.ac]
    simp
  have hyvLink : ({y, v} : Edge α) ∈ orientedCommonLink H V c a := by
    rw [hBook.ac]
    simp
  have hcyLink : ({c, y} : Edge α) ∈ orientedCommonLink H V b v := by
    rw [hBook.bv]
    simp
  have hbxLink : ({b, x} : Edge α) ∈ orientedCommonLink H V c u := by
    rw [hBook.cu]
    simp
  have hxcRoot : ({x, c} : Edge α) ∈ rootLink H V b :=
    oriented_common_link_pair_mem_root_link H V hxcLink
  have hybRoot : ({y, b} : Edge α) ∈ rootLink H V c :=
    oriented_common_link_pair_mem_root_link H V hybLink
  have hcyRoot : ({c, y} : Edge α) ∈ rootLink H V b :=
    oriented_common_link_pair_mem_root_link H V hcyLink
  have hbxRoot : ({b, x} : Edge α) ∈ rootLink H V c :=
    oriented_common_link_pair_mem_root_link H V hbxLink
  have huWeak : u ∈ weakRightAlternatives H V b x c :=
    second_book_pair_mem_weak_right_alternatives hH hbV haV
      (Ne.symm hab) hxc hxu (Ne.symm huc) hxcLink hxuLink
  have hvWeak : v ∈ weakRightAlternatives H V c y b :=
    second_book_pair_mem_weak_right_alternatives hH hcV haV
      (Ne.symm hac) hyb hyv (Ne.symm hvb) hybLink hyvLink
  have hmuB : 4 ≤ (rootCommonNeighbors H V b x y).card :=
    positive_rooted_edge_forces_other_common_neighbors_large
      hxcRoot hxc hposB huWeak hcyRoot (Ne.symm hxy)
  have hmuC : 4 ≤ (rootCommonNeighbors H V c y x).card :=
    positive_rooted_edge_forces_other_common_neighbors_large
      hybRoot hyb hposC hvWeak hbxRoot hxy
  have hmuC' : 4 ≤ (rootCommonNeighbors H V c x y).card := by
    simpa only [root_common_neighbors_comm] using hmuC
  exact two_large_root_fibers_impossible hH hbV hcV hxV hyV
    hbc (Ne.symm hxb) (Ne.symm hyb) (Ne.symm hxc) (Ne.symm hyc)
    hxy hmuB hmuC'

/-- Two positive reciprocal demands on one triple force the nine- or
ten-triple five-vertex block. This is Theorem II.C.1's complete structural
nonduplication statement for actual common-link books. -/
theorem double_bridge_books_do_not_overlap
    {H : Family α} {V : Edge α} {a b c x u y v : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hNoBlock : NoNineOrTenTripleBlock H)
    (hBook : DoubleBridgeBook H V a b c x u y v)
    (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (hxV : x ∈ V) (_huV : u ∈ V) (hyV : y ∈ V) (hvV : v ∈ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x)
    (hau : a ≠ u) (hbu : b ≠ u) (hcu : c ≠ u) (hxu : x ≠ u)
    (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c) (hyv : y ≠ v)
    (hposB : 0 < rootedSignedWeight H V b x c)
    (hposC : 0 < rootedSignedWeight H V c y b) : False := by
  by_cases hxyEq : x = y
  · subst y
    have huv : u = v := double_book_overlap_pages_equal hH hBook hvV
      hab hac hax hbx hcx hbc hbu hau hxu (Ne.symm hvc)
      (Ne.symm hva) hyv hcu (Ne.symm hvb)
    subst v
    have hOverlapTripleCard : (bridgeOverlapTripleSet a b c x u).card = 9 :=
      bridge_overlap_triple_set_card hab hac hax hau hbc hbx hbu hcx hcu hxu
    have h_ab_c : ({a, b} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have h_ab_u := oriented_link_right_extension h_ab_c
    have h_ax_c : ({a, x} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have h_ax_u := oriented_link_right_extension h_ax_c
    have h_bx_c : ({b, x} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have h_bx_u := oriented_link_right_extension h_bx_c
    have h_ac_v : ({a, c} : Edge α) ∈ orientedCommonLink H V b u := by
      rw [hBook.bv]
      simp
    have h_ax_v : ({a, x} : Edge α) ∈ orientedCommonLink H V b u := by
      rw [hBook.bv]
      simp
    have h_cx_v : ({c, x} : Edge α) ∈ orientedCommonLink H V b u := by
      rw [hBook.bv]
      simp
    have h₁ : ({a, b, c} : Edge α) ∈ H := by
      simpa using oriented_link_left_extension h_ab_c
    have h₂ : ({a, b, u} : Edge α) ∈ H := by
      simpa using h_ab_u
    have h₃ : ({a, c, x} : Edge α) ∈ H := by
      have hs : ({a, x} : Edge α) ∪ {c} = {a, c, x} := by
        ext t
        simp [or_comm]
      rw [← hs]
      exact oriented_link_left_extension h_ax_c
    have h₄ : ({a, x, u} : Edge α) ∈ H := by
      simpa using h_ax_u
    have h₅ : ({b, c, x} : Edge α) ∈ H := by
      have hs : ({b, x} : Edge α) ∪ {c} = {b, c, x} := by
        ext t
        simp [or_comm]
      rw [← hs]
      exact oriented_link_left_extension h_bx_c
    have h₆ : ({b, x, u} : Edge α) ∈ H := by
      simpa using h_bx_u
    have h₇ : ({a, c, u} : Edge α) ∈ H := by
      simpa using oriented_link_right_extension h_ac_v
    have h₈ : ({a, b, x} : Edge α) ∈ H := by
      have hs : ({a, x} : Edge α) ∪ {b} = {a, b, x} := by
        ext t
        simp [or_comm]
      rw [← hs]
      exact oriented_link_left_extension h_ax_v
    have h₉ : ({c, x, u} : Edge α) ∈ H := by
      simpa using oriented_link_right_extension h_cx_v
    let S : Edge α := {a, b, c, x, u}
    let T : Family α :=
      {{a, b, c}, {a, b, u}, {a, c, x}, {a, x, u}, {b, c, x},
        {b, x, u}, {a, c, u}, {a, b, x}, {c, x, u}}
    have hScard : S.card = 5 := by
      simp [S, hab, hac, hbc, hax, hbx, hcx, hau, hbu, hcu, hxu]
    have hTcard : T.card = 9 := by
      simpa [T, bridgeOverlapTripleSet] using hOverlapTripleCard
    have tripleSubset (r s t : α) (hr : r ∈ S) (hs : s ∈ S) (ht : t ∈ S) :
        ({r, s, t} : Edge α) ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw
      · exact hw ▸ hr
      · exact hw ▸ hs
      · exact hw ▸ ht
    have hTsub : T ⊆ (Finset.filter (fun E : Edge α => E ⊆ S) H) := by
      intro E hE
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with hE | hE | hE | hE | hE | hE | hE | hE | hE
      · subst E; exact Finset.mem_filter.mpr ⟨h₁, tripleSubset a b c (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₂, tripleSubset a b u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₃, tripleSubset a c x (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₄, tripleSubset a x u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₅, tripleSubset b c x (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₆, tripleSubset b x u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₇, tripleSubset a c u (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₈, tripleSubset a b x (by simp [S]) (by simp [S]) (by simp [S])⟩
      · subst E; exact Finset.mem_filter.mpr ⟨h₉, tripleSubset c x u (by simp [S]) (by simp [S]) (by simp [S])⟩
    have hCountLower : 9 ≤ (Finset.filter (fun E : Edge α => E ⊆ S) H).card := by
      rw [← hTcard]
      exact Finset.card_le_card hTsub
    have hFilteredSub : Finset.filter (fun E : Edge α => E ⊆ S) H ⊆
        S.powersetCard 3 := by
      intro E hE
      obtain ⟨hEH, hES⟩ := Finset.mem_filter.mp hE
      exact Finset.mem_powersetCard.mpr ⟨hES, hUniform hEH⟩
    have hCountUpper : (Finset.filter (fun E : Edge α => E ⊆ S) H).card ≤ 10 := by
      calc
        (Finset.filter (fun E : Edge α => E ⊆ S) H).card ≤ (S.powersetCard 3).card :=
          Finset.card_le_card hFilteredSub
        _ = 10 := by rw [Finset.card_powersetCard, hScard]; norm_num [Nat.choose]
    have hne := hNoBlock S hScard
    dsimp at hne
    omega
  · have hxy : x ≠ y := fun heq => hxyEq heq
    exact double_bridge_books_x_ne_y_impossible hH hBook haV hbV hcV hxV hyV
      hab hac hbc (Ne.symm hbx) (Ne.symm hcx) (Ne.symm hcu) hxu hyb hyc hxy hvb hyv
      hposB hposC

/-- When the overlap vertices agree, and the forced page vertices agree,
the four actual books contain the nine triples in the manuscript's block. -/
theorem double_book_eq_supplies_nine_triples
    {H : Family α} {V : Edge α} {a b c x u : α}
    (hBook : DoubleBridgeBook H V a b c x u x u) :
    ({a, b, c} : Edge α) ∈ H ∧ ({a, b, u} : Edge α) ∈ H ∧
    ({a, c, x} : Edge α) ∈ H ∧ ({a, x, u} : Edge α) ∈ H ∧
    ({b, c, x} : Edge α) ∈ H ∧ ({b, x, u} : Edge α) ∈ H ∧
    ({a, c, u} : Edge α) ∈ H ∧ ({a, b, x} : Edge α) ∈ H ∧
    ({c, x, u} : Edge α) ∈ H := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : ({a, b} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have := oriented_link_left_extension hp
    simpa using this
  · have hp : ({a, b} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have := oriented_link_right_extension hp
    simpa using this
  · have hp : ({a, x} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have := oriented_link_left_extension hp
    have hset : ({a, x} : Edge α) ∪ {c} = {a, c, x} := by
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← hset]
    exact this
  · have hp : ({a, x} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have := oriented_link_right_extension hp
    simpa using this
  · have hp : ({b, x} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have := oriented_link_left_extension hp
    have hset : ({b, x} : Edge α) ∪ {c} = {b, c, x} := by
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← hset]
    exact this
  · have hp : ({b, x} : Edge α) ∈ orientedCommonLink H V c u := by
      rw [hBook.cu]
      simp
    have := oriented_link_right_extension hp
    simpa using this
  · have hp : ({a, c} : Edge α) ∈ orientedCommonLink H V b u := by
      rw [hBook.bv]
      simp
    have := oriented_link_right_extension hp
    simpa using this
  · have hp : ({a, x} : Edge α) ∈ orientedCommonLink H V b u := by
      rw [hBook.bv]
      simp
    have := oriented_link_left_extension hp
    have hset : ({a, x} : Edge α) ∪ {b} = {a, b, x} := by
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← hset]
    exact this
  · have hp : ({c, x} : Edge α) ∈ orientedCommonLink H V b u := by
      rw [hBook.bv]
      simp
    have := oriented_link_right_extension hp
    simpa using this

/-- Nine actual triples on a five-set force the forbidden nine-or-ten block.
The book argument's remaining structural task is to construct `T` from its
four common-link equalities. -/
theorem nine_triples_contradict_no_block
    {H : JSP523.Family α} (hUniform : Uniform 3 H)
    (hNoBlock : NoNineOrTenTripleBlock H)
    (S : Edge α) (T : Family α) (hS : S.card = 5) (hT : T.card = 9)
    (hTsub : T ⊆ (Finset.filter (fun E : Edge α => E ⊆ S) H)) : False := by
  have hCountLower : 9 ≤ (Finset.filter (fun E : Edge α => E ⊆ S) H).card := by
    rw [← hT]
    exact Finset.card_le_card hTsub
  have hFilteredSub : Finset.filter (fun E : Edge α => E ⊆ S) H ⊆ S.powersetCard 3 := by
    intro E hE
    obtain ⟨hEH, hES⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_powersetCard.mpr ⟨hES, hUniform hEH⟩
  have hCountUpper : (Finset.filter (fun E : Edge α => E ⊆ S) H).card ≤ 10 := by
    calc
      (Finset.filter (fun E : Edge α => E ⊆ S) H).card ≤ (S.powersetCard 3).card :=
        Finset.card_le_card hFilteredSub
      _ = 10 := by rw [Finset.card_powersetCard, hS]; norm_num [Nat.choose]
  have hne := hNoBlock S hS
  dsimp at hne
  omega

end JSP523.Rank3
