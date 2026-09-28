import JSP523.Rank3.ReceiverCapacity
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace JSP523.Rank3

section ReceiverCapacityExtended

variable {α : Type*} [DecidableEq α]

/-- The reciprocal star case: a third spoke in the reciprocal link supplies
three completions to each original core, making all four directed charges at
most one half. -/
theorem double_receiver_star_capacity_le_two
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2)
    (hrecipStar : ∀ p ∈ commonLink H V ({y, u} : Edge α), x ∈ p)
    (hrecipLarge : 3 ≤ (commonLink H V ({y, u} : Edge α)).card) :
    actualCellChargeTotal H V z v ≤ 2 := by
  have h₁rev : ({x, y} : Edge α) ∈ commonLink H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₁
  have h₂rev : ({x, u} : Edge α) ∈ commonLink H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₂
  have h₁or := (mem_common_link_pair_iff_oriented H V hzv _).mp h₁
  have h₂or := (mem_common_link_pair_iff_oriented H V hzv _).mp h₂
  have h₁revOr := (mem_common_link_pair_iff_oriented H V (Ne.symm hzv) _).mp h₁rev
  have h₂revOr := (mem_common_link_pair_iff_oriented H V (Ne.symm hzv) _).mp h₂rev
  have hpv := reciprocal_pair_in_common_link H V hvV hxy hxu hyu h₁or h₂or
  have hpz := reciprocal_pair_in_common_link H V hzV hxy hxu hyu h₁revOr h₂revOr
  have hpv' : ({x, v} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpv
  have hpz' : ({x, z} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpz
  have hpvNePz : ({x, v} : Edge α) ≠ ({x, z} : Edge α) := by
    intro he
    have hv : v ∈ ({x, z} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hv with hvx | hvz
    · have hxv : x ≠ v := Finset.card_pair_eq_two_iff.mp
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpv').1).2
      exact hxv hvx.symm
    · exact hzv (Finset.mem_singleton.mp hvz).symm
  have hnotSub : ¬ commonLink H V ({y, u} : Edge α) ⊆
      ({({x, v} : Edge α), ({x, z} : Edge α)} : Family α) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hpvNePz] at hle
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.not_subset.mp hnotSub
  have hpneqv : p ≠ ({x, v} : Edge α) := by
    intro he
    apply hpnot
    rw [he]
    simp
  have hpneqz : p ≠ ({x, z} : Edge α) := by
    intro he
    apply hpnot
    rw [he]
    simp
  have hpx : x ∈ p := hrecipStar p hp
  obtain ⟨a, b, hab, hpEq⟩ :=
    Finset.card_eq_two.mp ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2)
  have hxa : x = a ∨ x = b := by
    have hxmem : x ∈ ({a, b} : Edge α) := by simpa [hpEq] using hpx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxmem
  let t : α := if x = a then b else a
  have hxt : x ≠ t := by
    dsimp [t]
    split_ifs with h
    · intro hxb
      exact hab (h.symm.trans hxb)
    · exact h
  have hpPair : p = ({x, t} : Edge α) := by
    rw [hpEq]
    dsimp [t]
    split_ifs with h
    · simp [h]
    · have hb : x = b := by
        rcases hxa with h' | h'
        · exact (h h').elim
        · exact h'
      simp [Finset.pair_comm, h, hb]
  obtain ⟨_, _, _, _, _, hdis, _, _⟩ := (Finset.mem_filter.mp hp).2
  have hty : t ≠ y := by
    intro h
    have htmem : t ∈ p := by rw [hpPair]; simp
    exact (Finset.disjoint_left.mp hdis) htmem (by simp [h])
  have htu : t ≠ u := by
    intro h
    have htmem : t ∈ p := by rw [hpPair]; simp
    exact (Finset.disjoint_left.mp hdis) htmem (by simp [h])
  have htv : t ≠ v := by
    intro h
    apply hpneqv
    rw [hpPair, h]
  have htz : t ≠ z := by
    intro h
    apply hpneqz
    rw [hpPair, h]
  have hs₁ := common_link_pair_gives_two_sources hzv h₁
  have hs₂ := common_link_pair_gives_two_sources hzv h₂
  have htSource : ({x, t} : Edge α) ∈ rootLink H V y := by
    have hroot := common_link_pair_gives_two_sources hyu hp
    simpa only [hpPair] using hroot.1
  have hrootT := Finset.mem_filter.mp htSource
  have htV : t ∈ V :=
    (Finset.mem_powersetCard.mp hrootT.1).1 (by simp)
  have hTriple : ({x, y} : Edge α) ∪ {t} ∈ H := by
    have heq : ({x, y} : Edge α) ∪ {t} = ({x, t} : Edge α) ∪ {y} := by
      ext w
      simp [Finset.mem_union, Finset.mem_insert, or_comm, or_left_comm, or_assoc]
    rw [heq]
    exact hrootT.2.2
  have htXY : t ∈ completionVertices H V ({x, y} : Edge α) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact htV
    · constructor
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        intro ht
        rcases (show t = x ∨ t = y by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using ht) with htx | hty'
        · exact hxt htx.symm
        · exact hty hty'
      · exact hTriple
  have hTripleU : ({x, u} : Edge α) ∪ {t} ∈ H := by
    have hrootU := common_link_pair_gives_two_sources hyu hp
    have hm := Finset.mem_filter.mp hrootU.2
    rw [hpPair] at hm
    have heq : ({x, u} : Edge α) ∪ {t} = ({x, t} : Edge α) ∪ {u} := by
      ext w
      simp [Finset.mem_union, Finset.mem_insert, or_comm, or_left_comm, or_assoc]
    rw [heq]
    exact hm.2.2
  have htXU : t ∈ completionVertices H V ({x, u} : Edge α) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact htV
    · constructor
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        intro ht
        rcases (show t = x ∨ t = u by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using ht) with htx | htu'
        · exact hxt htx.symm
        · exact htu htu'
      · exact hTripleU
  have hdegXY : 3 ≤ (completionVertices H V ({x, y} : Edge α)).card := by
    have hsub : ({z, v, t} : Finset α) ⊆ completionVertices H V ({x, y} : Edge α) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact root_mem_source_completion H V hzV hs₁.1
      · exact root_mem_source_completion H V hvV hs₁.2
      · exact htXY
    have hcard3 : ({z, v, t} : Finset α).card = 3 := by
      simp [hzv, Ne.symm hzv, htz, Ne.symm htz, htv, Ne.symm htv]
    rw [← hcard3]
    exact Finset.card_le_card hsub
  have hdegXU : 3 ≤ (completionVertices H V ({x, u} : Edge α)).card := by
    have hsub : ({z, v, t} : Finset α) ⊆ completionVertices H V ({x, u} : Edge α) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact root_mem_source_completion H V hzV hs₂.1
      · exact root_mem_source_completion H V hvV hs₂.2
      · exact htXU
    have hcard3 : ({z, v, t} : Finset α).card = 3 := by
      simp [hzv, Ne.symm hzv, htz, Ne.symm htz, htv, Ne.symm htv]
    rw [← hcard3]
    exact Finset.card_le_card hsub
  have hvXY : v ∈ (completionVertices H V ({x, y} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      root_mem_source_completion H V hvV hs₁.2⟩
  have hzXY : z ∈ (completionVertices H V ({x, y} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, root_mem_source_completion H V hzV hs₁.1⟩
  have hvXU : v ∈ (completionVertices H V ({x, u} : Edge α)).erase z :=
    Finset.mem_erase.mpr ⟨Ne.symm hzv,
      root_mem_source_completion H V hvV hs₂.2⟩
  have hzXU : z ∈ (completionVertices H V ({x, u} : Edge α)).erase v :=
    Finset.mem_erase.mpr ⟨hzv, root_mem_source_completion H V hzV hs₂.1⟩
  have hcharge₁ := actual_double_charge_lt_inverse_degree hH hzV hs₁.1 hxy hvXY hcard
  have hcharge₂ := actual_double_charge_lt_inverse_degree hH hvV hs₁.2 hxy hzXY
    (by simpa only [Finset.pair_comm] using hcard)
  have hcharge₃ := actual_double_charge_lt_inverse_degree hH hzV hs₂.1 hxu hvXU hcard
  have hcharge₄ := actual_double_charge_lt_inverse_degree hH hvV hs₂.2 hxu hzXU
    (by simpa only [Finset.pair_comm] using hcard)
  have hdenXY : 1 / (((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1) ≤ 1 / 2 := by
    have hd : (3 : ℚ) ≤ (completionVertices H V ({x, y} : Edge α)).card := by exact_mod_cast hdegXY
    have hdpos : (0 : ℚ) < ((completionVertices H V ({x, y} : Edge α)).card : ℚ) - 1 := by linarith
    apply (div_le_iff₀ hdpos).2
    norm_num
    linarith
  have hdenXU : 1 / (((completionVertices H V ({x, u} : Edge α)).card : ℚ) - 1) ≤ 1 / 2 := by
    have hd : (3 : ℚ) ≤ (completionVertices H V ({x, u} : Edge α)).card := by exact_mod_cast hdegXU
    have hdpos : (0 : ℚ) < ((completionVertices H V ({x, u} : Edge α)).card : ℚ) - 1 := by linarith
    apply (div_le_iff₀ hdpos).2
    norm_num
    linarith
  have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
    intro he
    have hyMem : y ∈ ({x, u} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hyMem with h | h
    · exact hxy h.symm
    · exact hyu (Finset.mem_singleton.mp h)
  have hcell := actual_cell_charge_total_eq_two_cores H V h₁ h₂ hne hcard
  have hxyCard : ({x, y} : Edge α).card = 2 := Finset.card_pair hxy
  have hxuCard : ({x, u} : Edge α).card = 2 := Finset.card_pair hxu
  have hrep₁ := core_receiver_charge_eq_displayed_pair H V
    ({x, y} : Edge α) z v x y hxyCard rfl
  have hrep₂ := core_receiver_charge_eq_displayed_pair H V
    ({x, y} : Edge α) v z x y hxyCard rfl
  have hrep₃ := core_receiver_charge_eq_displayed_pair H V
    ({x, u} : Edge α) z v x u hxuCard rfl
  have hrep₄ := core_receiver_charge_eq_displayed_pair H V
    ({x, u} : Edge α) v z x u hxuCard rfl
  rw [hcell, hrep₁, hrep₂, hrep₃, hrep₄]
  linarith [hcharge₁, hcharge₂, hcharge₃, hcharge₄, hdenXY, hdenXU]

/-- If the reciprocal common link of a two-core receiver has at least
three members and no common center, it is exactly the exceptional triangle
from §II.5. -/
theorem double_receiver_triangle_exception_of_no_center
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hyV : y ∈ V) (huV : u ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2)
    (hrecipLarge : 3 ≤ (commonLink H V ({y, u} : Edge α)).card)
    (hnocenter : ¬ ∃ a : α, ∀ p ∈ commonLink H V ({y, u} : Edge α), a ∈ p) :
    triangleExceptionalReceiverCell H V ({z, v} : Edge α) := by
  have h₁rev : ({x, y} : Edge α) ∈ commonLink H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₁
  have h₂rev : ({x, u} : Edge α) ∈ commonLink H V ({v, z} : Edge α) := by
    simpa only [Finset.pair_comm] using h₂
  have h₁or := (mem_common_link_pair_iff_oriented H V hzv _).mp h₁
  have h₂or := (mem_common_link_pair_iff_oriented H V hzv _).mp h₂
  have h₁revOr := (mem_common_link_pair_iff_oriented H V (Ne.symm hzv) _).mp h₁rev
  have h₂revOr := (mem_common_link_pair_iff_oriented H V (Ne.symm hzv) _).mp h₂rev
  have hpv := reciprocal_pair_in_common_link H V hvV hxy hxu hyu h₁or h₂or
  have hpz := reciprocal_pair_in_common_link H V hzV hxy hxu hyu h₁revOr h₂revOr
  have hpv' : ({x, v} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpv
  have hpz' : ({x, z} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
    simpa only [Finset.pair_comm] using hpz
  have hxv : x ≠ v := by
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpv').1).2
    exact Finset.card_pair_eq_two_iff.mp hc
  have hxz : x ≠ z := by
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hpz').1).2
    exact Finset.card_pair_eq_two_iff.mp hc
  have hthird : ∃ p ∈ commonLink H V ({y, u} : Edge α), x ∉ p := by
    by_contra h
    apply hnocenter
    refine ⟨x, ?_⟩
    intro p hp
    by_contra hpx
    exact h ⟨p, hp, hpx⟩
  obtain ⟨p, hp, hpx⟩ := hthird
  have hpy : y ≠ u := hyu
  have hpCard : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  have hvp : v ∈ p := by
    by_contra hvp
    apply common_link_pair_intersecting hH hyu hp hpv'
    apply Finset.disjoint_left.mpr
    intro a ha hpair
    rcases Finset.mem_insert.mp hpair with hax | hav
    · exact hpx (hax ▸ ha)
    · exact hvp ((Finset.mem_singleton.mp hav) ▸ ha)
  have hzp : z ∈ p := by
    by_contra hzp
    apply common_link_pair_intersecting hH hyu hp hpz'
    apply Finset.disjoint_left.mpr
    intro a ha hpair
    rcases Finset.mem_insert.mp hpair with hax | haz
    · exact hpx (hax ▸ ha)
    · exact hzp ((Finset.mem_singleton.mp haz) ▸ ha)
  have hsub : ({z, v} : Edge α) ⊆ p := by
    intro a ha
    rcases Finset.mem_insert.mp ha with haz | hav
    · exact haz ▸ hzp
    · exact (Finset.mem_singleton.mp hav) ▸ hvp
  have hpEq : p = ({z, v} : Edge α) := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_pair hzv, hpCard]
  have hp3 : ({z, v} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
    rw [← hpEq]
    exact hp
  have hpair₁ : ({x, z} : Edge α) ≠ ({x, v} : Edge α) := by
    intro he
    have hzm : z ∈ ({x, v} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hzm with hzx | hzv'
    · exact hxz hzx.symm
    · exact hzv (Finset.mem_singleton.mp hzv')
  have hpair₂ : ({z, v} : Edge α) ≠ ({x, z} : Edge α) := by
    intro he
    have hvm : v ∈ ({x, z} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hvm with hvx | hvz
    · exact hxv hvx.symm
    · exact hzv (Finset.mem_singleton.mp hvz).symm
  have hpair₃ : ({z, v} : Edge α) ≠ ({x, v} : Edge α) := by
    intro he
    have hzm : z ∈ ({x, v} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hzm with hzx | hzv'
    · exact hxz hzx.symm
    · exact hzv (Finset.mem_singleton.mp hzv')
  have htriCard :
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α).card = 3 := by
    have houter : ({x, z} : Edge α) ∉
        ({({x, v} : Edge α), ({z, v} : Edge α)} : Family α) := by
      simp [hpair₁, Ne.symm hpair₂]
    have hinner : ({x, v} : Edge α) ∉ ({({z, v} : Edge α)} : Family α) := by
      simp [Ne.symm hpair₃]
    rw [Finset.card_insert_of_notMem houter,
      Finset.card_insert_of_notMem hinner]
    simp
  have hCLCard : (commonLink H V ({y, u} : Edge α)).card = 3 := by
    have hclass := common_link_star_or_card_le_three hH hyV huV hyu
    rcases hclass with ⟨a, hstar⟩ | hsmall
    · exact False.elim (hnocenter ⟨a, hstar⟩)
    · omega
  have htriSub :
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α) ⊆
        commonLink H V ({y, u} : Edge α) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq | hq
    · simpa [hq] using hpz'
    · simpa [hq] using hpv'
    · simpa [hq] using hp3
  have htriEq : commonLink H V ({y, u} : Edge α) =
      ({({x, z} : Edge α), ({x, v} : Edge α), ({z, v} : Edge α)} : Family α) := by
    symm
    apply Finset.eq_of_subset_of_card_le htriSub
    rw [htriCard, hCLCard]
  have hneCores : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
    intro he
    have hyMem : y ∈ ({x, u} : Edge α) := by rw [← he]; simp
    rcases Finset.mem_insert.mp hyMem with h | h
    · exact hxy h.symm
    · exact hyu (Finset.mem_singleton.mp h)
  have hsourceCard :
      ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α).card = 2 :=
    Finset.card_pair hneCores
  have hsourceSub :
      ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α) ⊆
        commonLink H V ({z, v} : Edge α) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · simpa [hp] using h₁
    · simpa [hp] using h₂
  have hsourceEq : commonLink H V ({z, v} : Edge α) =
      ({({x, y} : Edge α), ({x, u} : Edge α)} : Family α) := by
    symm
    apply Finset.eq_of_subset_of_card_le hsourceSub
    rw [hsourceCard, hcard]
  have hxV : x ∈ V := by
    have hpV := (Finset.mem_filter.mp h₁).1
    exact (Finset.mem_powersetCard.mp hpV).1 (by simp)
  exact ⟨z, v, x, y, u, hzV, hvV, hxV, hyV, huV, rfl, hsourceEq, htriEq⟩

end ReceiverCapacityExtended

end JSP523.Rank3
