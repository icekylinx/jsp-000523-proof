import JSP523.Rank3.LocalBridgeMarked
import JSP523.Rank3.ChargeTransfer
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Source bounds and bridge payment in §II.D

The first theorem isolates the two actual common-neighbor alternatives used
in (II.D.2).  The second turns those bounds into (II.D.3), with the marked
bridge gain supplied by `bridge_book_actual_defect_gain`.
-/

namespace JSP523.Rank3

set_option maxHeartbeats 1000000

variable {α : Type*} [DecidableEq α]

private theorem triple_pair_mem_root_link
    {H : Family α} {V : Edge α} {z x y : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hE : ({z, x, y} : Edge α) ∈ H)
    (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y) :
    ({x, y} : Edge α) ∈ rootLink H V z := by
  have hxMem : x ∈ ({z, x, y} : Edge α) := by simp
  have hyMem : y ∈ ({z, x, y} : Edge α) := by simp
  have hxV := hground _ hE hxMem
  have hyV := hground _ hE hyMem
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    constructor
    · intro t ht
      rcases Finset.mem_insert.mp ht with htx | hty
      · exact htx ▸ hxV
      · exact (Finset.mem_singleton.mp hty) ▸ hyV
    · exact Finset.card_pair (by
        intro h
        exact hxy h)
  · constructor
    · simp [hzx, hzy]
    · have heq : ({x, y} : Edge α) ∪ {z} = {z, x, y} := by
        ext t
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hE

private theorem root_neighbor_of_actual_triple
    {H : Family α} {V : Edge α} {z x y : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hzx : z ≠ x) (hzy : z ≠ y) (hxy : x ≠ y)
    (hE : ({z, x, y} : Edge α) ∈ H) :
    y ∈ rootNeighbors H V z x := by
  have hyV : y ∈ V := hground _ hE (by simp)
  have hyOut : y ∉ ({z, x} : Edge α) := by
    intro hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hyz | hyx
    · exact hzy hyz.symm
    · exact hxy hyx.symm
  apply Finset.mem_filter.mpr
  refine ⟨hyV, hyOut, ?_⟩
  · have heq : ({z, x} : Edge α) ∪ {y} = {z, x, y} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact hE

/-- The two mandatory alternatives in G_a are actual vertices of the
erased neighborhoods: t in N_a(c) minus b from act, and x in N_a(b)
minus c from the page bx of J_at. -/
theorem bridge_book_source_alternatives_mem
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α)) :
    t ∈ (rootNeighbors H V a c).erase b ∧
      x ∈ (rootNeighbors H V a b).erase c ∧
      ({a, b, c} : Edge α) ∈ H ∧
      ({a, b, x} : Edge α) ∈ H := by
  have hBC : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]
    simp
  have hBX : ({b, x} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]
    simp
  obtain ⟨_, _, hABC, _⟩ := Finset.mem_filter.mp hBC
  obtain ⟨_, _, hABX, _⟩ := Finset.mem_filter.mp hBX
  have hDisj : Disjoint ({b, x} : Edge α) ({a, t} : Edge α) :=
    (Finset.mem_filter.mp hBX).2.1
  have hax : a ≠ x := by
    intro h
    have haP : a ∈ ({b, x} : Edge α) := by simpa [h]
    have haQ : a ∈ ({a, t} : Edge α) := by simp
    exact (Finset.disjoint_left.mp hDisj) haP haQ
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABC
    exact hABC
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABX
    exact hABX
  constructor
  · apply Finset.mem_erase.mpr
    refine ⟨Ne.symm hbt, root_neighbor_of_actual_triple hground hac hat hct hBridge⟩
  constructor
  · apply Finset.mem_erase.mpr
    refine ⟨Ne.symm hcx, root_neighbor_of_actual_triple hground hab hax
      hbx hABX'⟩
  exact ⟨hABC', hABX'⟩

/-- The two pages of the book both complete the source pair {b,c}; hence
its degree denominator is positive after subtracting the central page. -/
theorem bridge_book_source_pair_degree_ge_two
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α)) :
    2 ≤ (completionVertices H V ({b, c} : Edge α)).card := by
  have hPage : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]
    simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPage
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABC
    exact hABC
  have hTBC' : ({t, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {t} = {t, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hTBC
    exact hTBC
  have hBridgeV := hground _ hBridge
  have haV : a ∈ V := hBridgeV (by simp)
  have htV : t ∈ V := hBridgeV (by simp)
  have haComp : a ∈ completionVertices H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hab, hac]
    · have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
        ext q
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hABC'
  have htComp : t ∈ completionVertices H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨htV, ?_, ?_⟩
    · simp [hbt.symm, hct.symm]
    · have heq : ({b, c} : Edge α) ∪ {t} = {t, b, c} := by
        ext q
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hTBC'
  have hat' : a ≠ t := hat
  have hpair : ({a, t} : Edge α) ⊆ completionVertices H V ({b, c} : Edge α) := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqa | hqt
    · exact hqa ▸ haComp
    · exact (Finset.mem_singleton.mp hqt) ▸ htComp
  have hcard := Finset.card_le_card hpair
  rw [Finset.card_pair hat'] at hcard
  exact hcard

/-- The three-page common link J_cx has exactly two pairs through a and
through t; in the rooted graph these are the two common neighbors b and t,
or a and b, respectively. -/
theorem bridge_three_page_root_common_count
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H)
    (haV : a ∈ V) (hbV : b ∈ V) (htV : t ∈ V)
    (hcV : c ∈ V) (hxV : x ∈ V)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hac : a ≠ c) (hax : a ≠ x) (hcx : c ≠ x)
    (htc : t ≠ c) (htx : t ≠ x)
    (hBook : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α)) :
    (rootCommonNeighbors H V a c x).card = 2 ∧
      (rootCommonNeighbors H V t c x).card = 2 := by
  have hCommon : commonLink H V ({c, x} : Edge α) =
      ({{a, b}, {a, t}, {b, t}} : Family α) := by
    ext p
    exact (mem_common_link_pair_iff_oriented H V hcx p).trans
      (by rw [hBook])
  have hCell : ({c, x} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hcx⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqc | hqx
    · exact hqc ▸ hcV
    · exact (Finset.mem_singleton.mp hqx) ▸ hxV
  have hpbt : ({b, t} : Edge α) ∈ commonLink H V ({c, x} : Edge α) := by
    exact (mem_common_link_pair_iff_oriented H V hcx _).2
      (by rw [hBook]; simp)
  have hpab : ({a, b} : Edge α) ∈ commonLink H V ({c, x} : Edge α) := by
    exact (mem_common_link_pair_iff_oriented H V hcx _).2
      (by rw [hBook]; simp)
  have hpat : ({a, t} : Edge α) ∈ commonLink H V ({c, x} : Edge α) := by
    exact (mem_common_link_pair_iff_oriented H V hcx _).2
      (by rw [hBook]; simp)
  have hFiberA : commonLinkFiber H V ({c, x} : Edge α) a = {b, t} := by
    have haNot : a ∉ ({b, t} : Edge α) := by
      intro ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with hab' | hat'
      · exact hab hab'
      · exact hat hat'
    apply Finset.Subset.antisymm
    · exact common_link_fiber_subset_pair hH hCell hpbt haNot
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hqb | hqt
      · subst q
        unfold commonLinkFiber
        exact Finset.mem_filter.mpr ⟨hbV, hpab⟩
      · subst q
        unfold commonLinkFiber
        exact Finset.mem_filter.mpr ⟨htV, hpat⟩
  have hFiberT : commonLinkFiber H V ({c, x} : Edge α) t = {a, b} := by
    apply Finset.Subset.antisymm
    · exact common_link_fiber_subset_pair hH hCell hpab
        (by simp [Ne.symm hat, hbt.symm])
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hqa | hqb
      · subst q
        unfold commonLinkFiber
        exact Finset.mem_filter.mpr
          ⟨haV, by simpa [Finset.pair_comm] using hpat⟩
      · subst q
        unfold commonLinkFiber
        exact Finset.mem_filter.mpr
          ⟨hbV, by simpa [Finset.pair_comm] using hpbt⟩
  have hA := root_common_neighbors_eq_common_link_fiber H V
    haV hac hax hcx
  have hT := root_common_neighbors_eq_common_link_fiber H V
    htV htc htx hcx
  rw [hA, hFiberA, hT, hFiberT]
  constructor
  · rw [Finset.card_pair hbt]
  · rw [Finset.card_pair hab]

private theorem pair_eq_of_two_members_bridge
    {p : Edge α} {u v : α}
    (hp : p.card = 2) (hu : u ∈ p) (hv : v ∈ p) (huv : u ≠ v) :
  p = {u, v} := by
  have hsub : ({u, v} : Edge α) ⊆ p := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqu | hqv
    · exact hqu ▸ hu
    · exact (Finset.mem_singleton.mp hqv) ▸ hv
  have hcard : p.card ≤ ({u, v} : Edge α).card := by
    rw [hp, Finset.card_pair huv]
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- The book geometry bounds the receiving link J_bt by one central pair
plus the marked node's actual A-neighbors.  This is the link-to-degree
count c(bt) <= 1 + d_K(B_b), with the high-degree mixed-node condition
eliminating its C-neighbors. -/
theorem bridge_book_receiver_link_card_le_degree
    {H : Family α} {V : Edge α} {a t b c x : α} {r : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hrDegree : bipRightDegree (actualLocalTripartite H V c a t).ac
      ((actualLocalPartA H V c a t).erase x) b = r)
    (hr : 2 ≤ r) :
    (commonLink H V ({b, t} : Edge α)).card ≤ r + 2 := by
  let A := actualLocalPartA H V c a t
  let B := actualLocalPartB H V c a t
  let C := actualLocalPartC H V c a t
  let G := actualLocalTripartite H V c a t
  have hBCPage : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]
    simp
  have hBXPage : ({b, x} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]
    simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hBCPage
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hBXPage
  have hSrc : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABC
    exact hABC
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hTBX
    exact hTBX
  have hbV : b ∈ V := hground _ hSrc (by simp)
  have hcV : c ∈ V := hground _ hSrc (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have haV : a ∈ V := hground _ hBridge (by simp)
  have hCell : ({b, t} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hbt⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqb | hqt
    · exact hqb ▸ hbV
    · exact (Finset.mem_singleton.mp hqt) ▸ htV
  have hCenter : ({a, c} : Edge α) ∈ commonLink H V ({b, t} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, Finset.card_pair hac⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with hqa | hqc
      · exact hqa ▸ haV
      · exact (Finset.mem_singleton.mp hqc) ▸ hcV
    · refine ⟨b, by simp, t, by simp, hbt, ?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro q hqP hqCell
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqP hqCell
        rcases hqP with hqa | hqc <;>
          rcases hqCell with hqb | hqt
        · exact hab (hqa.symm.trans hqb)
        · exact hat (hqa.symm.trans hqt)
        · exact hbc.symm (hqc.symm.trans hqb)
        · exact hct (hqc.symm.trans hqt)
      · have heq : ({a, c} : Edge α) ∪ {b} = {a, b, c} := by
          ext q
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [heq]
        exact hSrc
      · have heq : ({a, c} : Edge α) ∪ {t} = {a, c, t} := by
          ext q
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [heq]
        exact hBridge
  have hBookNotAB : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq] at hABX
    exact hABX
  have hbC : b ∈ C := by
    change b ∈ actualLocalPartC H V c a t
    apply mem_actual_local_part_c.mpr
    refine ⟨hbV, ?_, ?_, ?_, ?_⟩
    · exact hbc
    · exact hab.symm
    · exact hbt
    · have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hSrc
  have hbB : b ∈ B := by
    change b ∈ actualLocalPartB H V c a t
    apply mem_actual_local_part_b.mpr
    refine ⟨hbV, ?_, ?_, ?_, ?_⟩
    · exact hbc
    · exact hab.symm
    · exact hbt
    · have heq : ({c, t, b} : Edge α) = ({b, c} : Edge α) ∪ {t} := by
        ext q
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hTBC
  have hABedge : (x, b) ∈ G.ab := by
    change (x, b) ∈ (actualLocalTripartite H V c a t).ab
    apply mem_actual_local_ab.mpr
    refine ⟨hx, hbB, ?_⟩
    have heq : ({t, b, x} : Edge α) = ({t, x, b} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact hTBX'
  have hACedge : (x, b) ∈ G.ac := by
    change (x, b) ∈ (actualLocalTripartite H V c a t).ac
    apply mem_actual_local_ac.mpr
    refine ⟨hx, hbC, ?_⟩
    have heq : ({a, b, x} : Edge α) = ({a, x, b} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [← heq]
    exact hBookNotAB
  have hMixed : MixedNodeDegreeTwo G A B C :=
    actual_local_tripartite_mixed_degree_two hH hUniform
      hac.symm hct hat
  have hABpos : 0 < bipLeftDegree G.ab B x := by
    exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbB, hABedge⟩⟩
  have hACpos : 0 < bipLeftDegree G.ac C x := by
    exact Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbC, hACedge⟩⟩
  have hACone : C.filter (fun z => (x, z) ∈ G.ac) = {b} := by
    have hCard : (C.filter (fun z => (x, z) ∈ G.ac)).card = 1 :=
      (hMixed.1 x hx hABpos hACpos).2
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hCard
    have hbmem : b ∈ C.filter (fun z => (x, z) ∈ G.ac) :=
      Finset.mem_filter.mpr ⟨hbC, hACedge⟩
    rw [hz] at hbmem
    have hbz : b = z := by simpa using hbmem
    simpa [hbz] using hz
  have hFullDegree : bipRightDegree G.ac A b = r + 1 := by
    have h := bip_right_degree_erase_left_neighbor
      G.ac A C x b hx hACone
    rw [hrDegree] at h
    exact h
  have hBCzero : bipRightDegree G.bc B b = 0 := by
    by_contra hne
    have hpos : 0 < bipRightDegree G.bc B b := Nat.pos_of_ne_zero hne
    have hOne := hMixed.2.2 b hbC
      (by rw [hFullDegree]; omega) hpos
    omega
  let N := A.filter (fun u => (u, b) ∈ G.ac)
  let T := insert ({a, c} : Edge α)
    (N.image fun u => ({a, u} : Edge α))
  have hJsub : commonLink H V ({b, t} : Edge α) ⊆ T := by
    intro p hp
    by_cases hpCenter : p = ({a, c} : Edge α)
    · rw [hpCenter]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    · obtain ⟨hpV, hpCert⟩ := Finset.mem_filter.mp hp
      obtain ⟨u, hu, v, hv, huv, hpDisj, hpu, hpv⟩ := hpCert
      have huCases : u = b ∨ u = t := by simpa using hu
      have hvCases : v = b ∨ v = t := by simpa using hv
      have hpb : p ∪ {b} ∈ H := by
        rcases huCases with rfl | rfl
        · rcases hvCases with rfl | rfl
          · exact False.elim (huv rfl)
          · exact hpu
        · rcases hvCases with rfl | rfl
          · exact hpv
          · exact False.elim (huv rfl)
      have hpt : p ∪ {t} ∈ H := by
        rcases huCases with rfl | rfl
        · rcases hvCases with rfl | rfl
          · exact False.elim (huv rfl)
          · exact hpv
        · rcases hvCases with rfl | rfl
          · exact hpu
          · exact False.elim (huv rfl)
      have hhit : ¬ Disjoint p ({a, c} : Edge α) :=
        common_link_intersecting_of_ground_cell hH hCell hp hCenter
      have hACmem : a ∈ p ∨ c ∈ p := by
        by_contra h
        apply hhit
        apply Finset.disjoint_left.mpr
        intro q hqP hqAC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hqAC
        rcases hqAC with hqa | hqc
        · exact (not_or.mp h).1 (hqa ▸ hqP)
        · exact (not_or.mp h).2 (hqc ▸ hqP)
      have hpCard : p.card = 2 :=
        (Finset.mem_powersetCard.mp hpV).2
      have hcNot : c ∉ p := by
        intro hcP
        have haNot : a ∉ p := by
          intro haP
          exact hpCenter (pair_eq_of_two_members_bridge hpCard haP hcP hac)
        have hMore : (p.erase c).Nonempty := by
          apply Finset.card_pos.mp
          have hErase := Finset.card_erase_add_one hcP
          omega
        obtain ⟨u, huErase⟩ := hMore
        have hcu : u ≠ c := (Finset.mem_erase.mp huErase).1
        have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
        have huNeA : u ≠ a := by
          intro hEq
          exact hpCenter (by
            rw [pair_eq_of_two_members_bridge hpCard hcP huP hcu.symm]
            simp [hEq, Finset.pair_comm])
        have huNeT : u ≠ t := by
          intro hEq
          have htP : t ∈ p := hEq ▸ huP
          exact (Finset.disjoint_left.mp hpDisj) htP (by simp)
        have huNeB : u ≠ b := by
          intro hEq
          have hbP : b ∈ p := hEq ▸ huP
          exact (Finset.disjoint_left.mp hpDisj) hbP (by simp)
        have huV : u ∈ V :=
          (Finset.mem_powersetCard.mp hpV).1 huP
        have huB : u ∈ B := by
          change u ∈ actualLocalPartB H V c a t
          apply mem_actual_local_part_b.mpr
          refine ⟨huV, hcu, huNeA, huNeT, ?_⟩
          have hpEq : p = ({c, u} : Edge α) :=
            pair_eq_of_two_members_bridge hpCard hcP huP hcu.symm
          have hpT : p ∪ {t} ∈ H := hpt
          have heq' : p ∪ {t} = {c, t, u} := by
            rw [hpEq]
            ext q
            simp [or_comm, or_left_comm, or_assoc]
          rw [← heq']
          exact hpT
        have huBC : (u, b) ∈ G.bc := by
          change (u, b) ∈ (actualLocalTripartite H V c a t).bc
          apply mem_actual_local_bc.mpr
          refine ⟨huB, hbC, ?_⟩
          have hpEq : p = ({c, u} : Edge α) :=
            pair_eq_of_two_members_bridge hpCard hcP huP hcu.symm
          have heq : p ∪ {b} = ({c, u, b} : Edge α) := by
            rw [hpEq]
            ext q
            simp
          rw [← heq]
          exact hpb
        have hposB : 0 < bipRightDegree G.bc B b := by
          exact Finset.card_pos.mpr
            ⟨u, Finset.mem_filter.mpr ⟨huB, huBC⟩⟩
        exact (Nat.ne_of_gt hposB) hBCzero
      have haP := hACmem.resolve_right hcNot
      have hMore : (p.erase a).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one haP
        omega
      obtain ⟨u, huErase⟩ := hMore
      have hau : a ≠ u := (Finset.mem_erase.mp huErase).1.symm
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huNeC : u ≠ c := by
        intro hEq
        exact hpCenter (by
          rw [pair_eq_of_two_members_bridge hpCard haP huP hau]
          simp [hEq, Finset.pair_comm])
      have huNeT : u ≠ t := by
        intro hEq
        have htP : t ∈ p := hEq ▸ huP
        exact (Finset.disjoint_left.mp hpDisj) htP (by simp)
      have huNeB : u ≠ b := by
        intro hEq
        have hbP : b ∈ p := hEq ▸ huP
        exact (Finset.disjoint_left.mp hpDisj) hbP (by simp)
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpV).1 huP
      have huA : u ∈ A := by
        change u ∈ actualLocalPartA H V c a t
        apply mem_actual_local_part_a.mpr
        refine ⟨huV, huNeC, Ne.symm hau, huNeT, ?_⟩
        have hpEq : p = ({a, u} : Edge α) :=
          pair_eq_of_two_members_bridge hpCard haP huP hau
        have heq : p ∪ {t} = ({a, t, u} : Edge α) := by
          rw [hpEq]
          ext q
          simp [or_comm, or_left_comm]
        rw [← heq]
        exact hpt
      have huAC : (u, b) ∈ G.ac := by
        change (u, b) ∈ (actualLocalTripartite H V c a t).ac
        apply mem_actual_local_ac.mpr
        refine ⟨huA, hbC, ?_⟩
        have hpEq : p = ({a, u} : Edge α) :=
          pair_eq_of_two_members_bridge hpCard haP huP hau
        have heq : p ∪ {b} = ({a, u, b} : Edge α) := by
          rw [hpEq]
          ext q
          simp
        rw [← heq]
        exact hpb
      have huN : u ∈ N := Finset.mem_filter.mpr ⟨huA, huAC⟩
      have hpEq : p = ({a, u} : Edge α) :=
        pair_eq_of_two_members_bridge hpCard haP huP hau
      rw [hpEq]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨u, huN, rfl⟩))
  have hCard : (commonLink H V ({b, t} : Edge α)).card ≤ T.card :=
    Finset.card_le_card hJsub
  have hTCard : T.card ≤ N.card + 1 := by
    dsimp [T]
    calc
      (insert ({a, c} : Edge α) (N.image fun u => ({a, u} : Edge α))).card ≤
          (N.image fun u => ({a, u} : Edge α)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ N.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
  have hNCard : N.card = r + 1 := by
    change (Finset.filter (fun u => (u, b) ∈ G.ac) A).card = r + 1
    exact hFullDegree
  rw [hNCard] at hTCard
  omega

private theorem oriented_common_link_swap
    (H : Family α) (V : Edge α) {a t : α} (hat : a ≠ t) :
    orientedCommonLink H V t a = orientedCommonLink H V a t := by
  unfold orientedCommonLink
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpV, hpDisj, hpt, hpa⟩
    refine ⟨hpV, ?_, hpa, hpt⟩
    simpa only [Finset.pair_comm] using hpDisj
  · rintro ⟨hpV, hpDisj, hpa, hpt⟩
    refine ⟨hpV, ?_, hpt, hpa⟩
    simpa only [Finset.pair_comm] using hpDisj

private theorem bridge_local_a_swap
    (H : Family α) (V : Edge α) (a c t : α) :
    actualLocalPartA H V c t a =
      actualLocalPartA H V c a t := by
  rw [actual_local_part_a_eq_completion_vertices_erase,
    actual_local_part_a_eq_completion_vertices_erase]
  simp [Finset.pair_comm]

private theorem bridge_local_c_swap
    (H : Family α) (V : Edge α) (a c t : α) :
    actualLocalPartC H V c t a =
      actualLocalPartB H V c a t := by
  rw [actual_local_part_c_eq_completion_vertices_erase,
    actual_local_part_b_eq_completion_vertices_erase]

private theorem bridge_graph_ac_swap
    (H : Family α) (V : Edge α) (a c t : α) :
    (actualLocalTripartite H V c t a).ac =
      (actualLocalTripartite H V c a t).ab := by
  ext e
  rcases e with ⟨u, v⟩
  rw [mem_actual_local_ac, mem_actual_local_ab,
    bridge_local_a_swap H V a c t,
    bridge_local_c_swap H V a c t]

/-- The other receiver-link bound follows by swapping the two bridge
roots.  It controls J_ab using the actual A-degree of the other marked
node, whose original local graph degree is in the AB pair graph. -/
theorem bridge_book_other_receiver_link_card_le_degree
    {H : Family α} {V : Edge α} {a t b c x : α} {s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hsDegree : bipRightDegree (actualLocalTripartite H V c a t).ab
      ((actualLocalPartA H V c a t).erase x) b = s)
    (hs : 2 ≤ s) :
    (commonLink H V ({a, b} : Edge α)).card ≤ s + 2 := by
  have hBookSwap : orientedCommonLink H V t a =
      ({{b, c}, {b, x}} : Family α) := by
    rw [oriented_common_link_swap H V hat, hBook]
  have hBridgeSwap : ({t, c, a} : Edge α) ∈ H := by
    have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact hBridge
  have hxSwap : x ∈ actualLocalPartA H V c t a := by
    rw [bridge_local_a_swap H V a c t]
    exact hx
  have hDegSwap : bipRightDegree (actualLocalTripartite H V c t a).ac
      ((actualLocalPartA H V c t a).erase x) b = s := by
    rw [bridge_graph_ac_swap H V a c t,
      bridge_local_a_swap H V a c t]
    exact hsDegree
  simpa [Finset.pair_comm] using bridge_book_receiver_link_card_le_degree
    (H := H) (V := V) (a := t) (t := a) (b := b) (c := c) (x := x)
    (hH := hH) (hUniform := hUniform) (hground := hground)
    (hab := hbt.symm) (hac := hct.symm) (hat := hat.symm)
    (hbc := hbc) (hbt := hab.symm) (hct := hac.symm)
    (hBridge := hBridgeSwap) (hBook := hBookSwap) (hx := hxSwap)
    (hrDegree := hDegSwap) (hr := hs)

/-- Two specified alternatives in the endpoint deficit give the source
weight bound used in (II.D.2).  The assumptions are actual rooted common
neighbor counts; no deficit estimate is hidden in the conclusion. -/
theorem rooted_signed_weight_le_weight_fraction_of_two_alternatives
    (H : Family α) (V : Edge α) {z x y u v : α} {k : ℕ}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y)
    (hu : u ∈ (rootNeighbors H V z y).erase x)
    (hv : v ∈ (rootNeighbors H V z x).erase y)
    (huCount : (rootCommonNeighbors H V z x u).card = 2)
    (hvCount : (rootCommonNeighbors H V z y v).card ≤ k) :
    rootedSignedWeight H V z x y ≤ weightFraction k := by
  let dx := (rootNeighbors H V z x).card
  let dy := (rootNeighbors H V z y).card
  have hDef1 : weightFraction dx - weightFraction 2 ≤
      (∑ q ∈ (rootNeighbors H V z y).erase x,
        (weightFraction dx -
          weightFraction (rootCommonNeighbors H V z x q).card)) := by
    have hAt : weightFraction dx - weightFraction 2 =
        weightFraction dx -
          weightFraction (rootCommonNeighbors H V z x u).card := by
      rw [huCount]
    rw [hAt]
    exact Finset.single_le_sum
      (f := fun q => weightFraction dx -
        weightFraction (rootCommonNeighbors H V z x q).card)
      (fun q hq => sub_nonneg.mpr (weight_fraction_mono (Finset.card_le_card
        (root_common_neighbors_subset_root_neighbors_left H V z x q)))) hu
  have hDef2 : weightFraction dy - weightFraction k ≤
      (∑ q ∈ (rootNeighbors H V z x).erase y,
        (weightFraction dy -
          weightFraction (rootCommonNeighbors H V z y q).card)) := by
    have hAtV : weightFraction dy - weightFraction k ≤
        weightFraction dy -
          weightFraction (rootCommonNeighbors H V z y v).card := by
      exact sub_le_sub_left (weight_fraction_mono hvCount) _
    exact hAtV.trans (Finset.single_le_sum
      (f := fun q => weightFraction dy -
        weightFraction (rootCommonNeighbors H V z y q).card)
      (fun q hq => sub_nonneg.mpr (weight_fraction_mono
        (Finset.card_le_card
          (root_common_neighbors_subset_root_neighbors_left H V z y q)))) hv)
  have hDef : weightFraction dx + weightFraction dy -
      (weightFraction 2 + weightFraction k) ≤
      rootedWeightDeficit H V z x y := by
    unfold rootedWeightDeficit
    have := add_le_add hDef1 hDef2
    dsimp [dx, dy] at this ⊢
    linarith
  have hEq := rooted_signed_weight_eq_base_sub_deficit H V hxy hxyNe
  have hBase := base_weight_le_twice_min dx dy
  have hMin : 2 * min (weightFraction dx) (weightFraction dy) ≤
      weightFraction dx + weightFraction dy := by
    have h₁ := min_le_left (weightFraction dx) (weightFraction dy)
    have h₂ := min_le_right (weightFraction dx) (weightFraction dy)
    linarith
  have h2 : weightFraction 2 = 0 := by norm_num [weightFraction]
  have hkNonneg := weight_fraction_nonneg k
  rw [h2] at hDef
  rw [hEq]
  have hTarget : weightFraction dx + weightFraction dy -
      (weightFraction dx + weightFraction dy - weightFraction k) ≤
      weightFraction k := by linarith
  linarith

/-- (II.D.2) in actual rooted-link notation.  It is stated for each
directed source: a degree bound on the second specified common-neighbor
fiber, together with the two-alternative count `2`, gives the manuscript's
`phi(r+1) = localPhi(r+1)` bound. -/
theorem rooted_signed_weight_le_local_phi_of_bridge_alternatives
    (H : Family α) (V : Edge α) {z x y u v : α} {r : ℕ}
    (hxy : ({x, y} : Edge α) ∈ rootLink H V z)
    (hxyNe : x ≠ y)
    (hu : u ∈ (rootNeighbors H V z y).erase x)
    (hv : v ∈ (rootNeighbors H V z x).erase y)
    (huCount : (rootCommonNeighbors H V z x u).card = 2)
    (hvCount : (rootCommonNeighbors H V z y v).card ≤ r + 2) :
    rootedSignedWeight H V z x y ≤ localPhi (r + 1) := by
  have h := rooted_signed_weight_le_weight_fraction_of_two_alternatives
    H V hxy hxyNe hu hv huCount hvCount
  simpa [localPhi, Nat.add_assoc] using h

/-- The central vertex and marked A vertex are distinct completion
points of the core pair {b,c}. -/
theorem bridge_core_pair_completion_degree_ge_two
    {H : Family α} {V : Edge α} {a b c x : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hx : x ∈ actualLocalPartA H V a b c) :
    2 ≤ (completionVertices H V ({b, c} : Edge α)).card := by
  have haV : a ∈ V := hground _ hE (by simp)
  have haComp : a ∈ completionVertices H V ({b, c} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hab, hac]
    · have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
        ext t
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hE
  have hxComp : x ∈ completionVertices H V ({b, c} : Edge α) := by
    rw [actual_local_part_a_eq_completion_vertices_erase] at hx
    exact (Finset.mem_erase.mp hx).2
  have hax : a ≠ x := (mem_actual_local_part_a.mp hx |>.2.1).symm
  have hpair : ({a, x} : Edge α) ⊆
      completionVertices H V ({b, c} : Edge α) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with hta | htx
    · exact hta ▸ haComp
    · exact (Finset.mem_singleton.mp htx) ▸ hxComp
  have hcard := Finset.card_le_card hpair
  rw [Finset.card_pair hax] at hcard
  exact hcard

/-- A tagged C vertex and the central vertex are distinct completion
points of {a,b}. -/
theorem bridge_other_pair_completion_degree_ge_two
    {H : Family α} {V : Edge α} {a b c d : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hd : d ∈ actualLocalPartC H V a b c) :
    2 ≤ (completionVertices H V ({a, b} : Edge α)).card := by
  have hcV : c ∈ V := hground _ hE (by simp)
  have hcComp : c ∈ completionVertices H V ({a, b} : Edge α) := by
    apply Finset.mem_filter.mpr
    refine ⟨hcV, ?_, ?_⟩
    · simp [hac.symm, hbc.symm]
    · have heq : ({a, b} : Edge α) ∪ {c} = {a, b, c} := by
        ext t
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [heq]
      exact hE
  have hdComp : d ∈ completionVertices H V ({a, b} : Edge α) := by
    rw [actual_local_part_c_eq_completion_vertices_erase] at hd
    exact (Finset.mem_erase.mp hd).2
  have hcd : c ≠ d := (mem_actual_local_part_c.mp hd |>.2.2.2.1).symm
  have hpair : ({c, d} : Edge α) ⊆
      completionVertices H V ({a, b} : Edge α) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with htc | htd
    · exact htc ▸ hcComp
    · exact (Finset.mem_singleton.mp htd) ▸ hdComp
  have hcard := Finset.card_le_card hpair
  rw [Finset.card_pair hcd] at hcard
  exact hcard

/-- Payment consequence of (II.D.2): once the marked graph degrees are
at least three and their marked neighborhoods meet only at the central
node, the local defect pays the smaller actual directed bridge demand.
The two source-weight bounds are explicit premises, so the combinatorial
alternative-count obligations remain visible to callers. -/
theorem bridge_actual_defect_pays_minimum_demand
    {H : Family α} {V : Edge α} {a b c d x : α} {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hx : x ∈ actualLocalPartA H V a b c)
    (hdB : d ∈ actualLocalPartB H V a b c)
    (hdC : d ∈ actualLocalPartC H V a b c)
    (hABEdge : (x, d) ∈ (actualLocalTripartite H V a b c).ab)
    (hACEdge : (x, d) ∈ (actualLocalTripartite H V a b c).ac)
    (hBook : orientedCommonLink H V b c = ({{d, a}, {d, x}} : Family α))
    (hrDegree : bipRightDegree (actualLocalTripartite H V a b c).ab
      ((actualLocalPartA H V a b c).erase x) d = r)
    (hsDegree : bipRightDegree (actualLocalTripartite H V a b c).ac
      ((actualLocalPartA H V a b c).erase x) d = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    {u₁ v₁ u₂ v₂ : α}
    (hu₁ : u₁ ∈ (rootNeighbors H V a c).erase b)
    (hv₁ : v₁ ∈ (rootNeighbors H V a b).erase c)
    (hu₁Count : (rootCommonNeighbors H V a b u₁).card = 2)
    (hv₁Count : (rootCommonNeighbors H V a c v₁).card ≤ r + 2)
    (hu₂ : u₂ ∈ (rootNeighbors H V c b).erase a)
    (hv₂ : v₂ ∈ (rootNeighbors H V c a).erase b)
    (hu₂Count : (rootCommonNeighbors H V c a u₂).card = 2)
    (hv₂Count : (rootCommonNeighbors H V c b v₂).card ≤ s + 2)
    :
    min
      (positiveRootedWeight H V a b c /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      (positiveRootedWeight H V c a b /
        (((completionVertices H V ({a, b} : Edge α)).card : ℚ) - 1)) ≤
      localSignedDefect H V ({a, b, c} : Edge α) := by
  have hGain := bridge_book_actual_defect_gain
    hH hUniform hground hab hac hbc hE hx hdB hdC hABEdge hACEdge hBook
    hrDegree hsDegree hr hs
  have hdegA := bridge_core_pair_completion_degree_ge_two
    hground hab hac hE hx
  have hdegT := bridge_other_pair_completion_degree_ge_two
    hground hac hbc hE hdC
  have hdenA : 1 ≤
      ((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1 := by
    have hq : (2 : ℚ) ≤ (completionVertices H V ({b, c} : Edge α)).card := by
      exact_mod_cast hdegA
    linarith
  have hdenT : 1 ≤
      ((completionVertices H V ({a, b} : Edge α)).card : ℚ) - 1 := by
    have hq : (2 : ℚ) ≤ (completionVertices H V ({a, b} : Edge α)).card := by
      exact_mod_cast hdegT
    linarith
  have hSourceA := triple_pair_mem_root_link (z := a) (x := b) (y := c)
    hground hE hab hac hbc
  have hTripleT : ({c, a, b} : Edge α) ∈ H := by
    have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq]
    exact hE
  have hSourceT := triple_pair_mem_root_link (z := c) (x := a) (y := b)
    hground hTripleT hac.symm hbc.symm hab
  have hwa := rooted_signed_weight_le_local_phi_of_bridge_alternatives
    H V hSourceA hbc hu₁ hv₁ hu₁Count hv₁Count
  have hwt := rooted_signed_weight_le_local_phi_of_bridge_alternatives
    H V hSourceT hab hu₂ hv₂ hu₂Count hv₂Count
  have hPosA : 0 ≤ positiveRootedWeight H V a b c := by
    unfold positiveRootedWeight
    exact le_max_right _ _
  have hPosT : 0 ≤ positiveRootedWeight H V c a b := by
    unfold positiveRootedWeight
    exact le_max_right _ _
  have hMaxA : positiveRootedWeight H V a b c ≤ localPhi (r + 1) := by
    unfold positiveRootedWeight
    exact max_le hwa (local_phi_nonneg _)
  have hMaxT : positiveRootedWeight H V c a b ≤ localPhi (s + 1) := by
    unfold positiveRootedWeight
    exact max_le hwt (local_phi_nonneg _)
  have hPayA : positiveRootedWeight H V a b c /
      (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1) ≤
      localPhi (r + 1) := by
    apply (div_le_iff₀ (by linarith : 0 <
      ((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1)).mpr
    nlinarith
  have hPayT : positiveRootedWeight H V c a b /
      (((completionVertices H V ({a, b} : Edge α)).card : ℚ) - 1) ≤
      localPhi (s + 1) := by
    apply (div_le_iff₀ (by linarith : 0 <
      ((completionVertices H V ({a, b} : Edge α)).card : ℚ) - 1)).mpr
    nlinarith
  exact (min_le_min hPayA hPayT).trans hGain

/-- Fully instantiated §II.D payment for the manuscript bridge triple
`{a,c,t}`.  The two source weights are rooted at `a` and `t` on the same
source pair `{b,c}`.  All alternatives, common-link counts, and the source
denominator are derived from the two-page book and the three-page `J_cx`.
The local marked degrees are supplied as the actual graph measurements. -/
theorem bridge_book_manuscript_payment
    {H : Family α} {V : Edge α} {a t b c x : α} {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hrDegree : bipRightDegree (actualLocalTripartite H V c a t).ac
      ((actualLocalPartA H V c a t).erase x) b = r)
    (hsDegree : bipRightDegree (actualLocalTripartite H V c a t).ab
      ((actualLocalPartA H V c a t).erase x) b = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    min
      (positiveRootedWeight H V a c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      (positiveRootedWeight H V t c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      ≤ localSignedDefect H V ({a, c, t} : Edge α) := by
  have hAlt := bridge_book_source_alternatives_mem hground hab hac hat
    hbc hbt hbx hct hcx htx hBridge hBookAt
  have hPageBC : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBookAt]
    simp
  have hPageBX : ({b, x} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBookAt]
    simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hPageBX
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hABC
  have hTBC' : ({t, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {t} = {t, b, c} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hTBC
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hABX
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hTBX
  have hxb : x ∈ (rootNeighbors H V a b).erase c := hAlt.2.1
  have hta : t ∈ (rootNeighbors H V a c).erase b := hAlt.1
  have hxt : x ∈ (rootNeighbors H V t b).erase c := by
    apply Finset.mem_erase.mpr
    refine ⟨hcx.symm, ?_⟩
    exact root_neighbor_of_actual_triple hground hbt.symm htx hbx hTBX'
  have hatN : a ∈ (rootNeighbors H V t c).erase b := by
    apply Finset.mem_erase.mpr
    refine ⟨hab, ?_⟩
    have hBridgeTCA : ({t, c, a} : Edge α) ∈ H := by
      have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact heq ▸ hBridge
    exact root_neighbor_of_actual_triple hground hct.symm hat.symm hac.symm hBridgeTCA
  have haV : a ∈ V := hground _ hBridge (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have hcV : c ∈ V := hground _ hBridge (by simp)
  have hbV : b ∈ V := by
    have hmem := (Finset.mem_filter.mp hPageBC).1
    exact (Finset.mem_powersetCard.mp hmem).1 (by simp)
  have hxV : x ∈ V := by
    have hmem := (Finset.mem_filter.mp hPageBX).1
    exact (Finset.mem_powersetCard.mp hmem).1 (by simp)
  have hCounts := bridge_three_page_root_common_count hH haV hbV htV hcV hxV
    hab hat hbt hac hax hcx hct.symm htx hBookCx
  have hCardBT : (commonLink H V ({b, t} : Edge α)).card ≤ r + 2 := by
    simpa [Finset.pair_comm] using
      bridge_book_receiver_link_card_le_degree hH hUniform hground
        hab hac hat hbc hbt hct hBridge hBookAt hx hrDegree hr
  have hCardBA : (commonLink H V ({b, a} : Edge α)).card ≤ s + 2 := by
    simpa [Finset.pair_comm] using
      bridge_book_other_receiver_link_card_le_degree hH hUniform hground
        hab hac hat hbc hbt hct hBridge hBookAt hx hsDegree hs
  have hCommonA : (rootCommonNeighbors H V a b t).card ≤ r + 2 := by
    have heq := root_common_neighbors_eq_common_link_fiber H V haV hab hat hbt
    rw [heq]
    exact (common_link_fiber_card_le_common_link_card H V {b, t} a).trans hCardBT
  have hCommonT : (rootCommonNeighbors H V t b a).card ≤ s + 2 := by
    have heq := root_common_neighbors_eq_common_link_fiber H V htV hbt.symm
      hat.symm hab.symm
    rw [heq]
    exact (common_link_fiber_card_le_common_link_card H V {b, a} t).trans hCardBA
  have hACB : ({a, c, b} : Edge α) ∈ H := by
    have heq : ({a, c, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hABC'
  have hTCB : ({t, c, b} : Edge α) ∈ H := by
    have heq : ({t, c, b} : Edge α) = ({t, b, c} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hTBC'
  have hRootA := triple_pair_mem_root_link (z := a) (x := c) (y := b)
    hground hACB hac hab hbc.symm
  have hRootT := triple_pair_mem_root_link (z := t) (x := c) (y := b)
    hground hTCB hct.symm hbt.symm hbc.symm
  have hWeightA := rooted_signed_weight_le_local_phi_of_bridge_alternatives
    H V hRootA hbc.symm hxb hta hCounts.1 hCommonA
  have hWeightT := rooted_signed_weight_le_local_phi_of_bridge_alternatives
    H V hRootT hbc.symm hxt hatN hCounts.2 hCommonT
  have hPositiveA : positiveRootedWeight H V a c b ≤ localPhi (r + 1) := by
    unfold positiveRootedWeight
    exact max_le hWeightA (local_phi_nonneg _)
  have hPositiveT : positiveRootedWeight H V t c b ≤ localPhi (s + 1) := by
    unfold positiveRootedWeight
    exact max_le hWeightT (local_phi_nonneg _)
  have hdeg := bridge_book_source_pair_degree_ge_two hground hab hac hat
    hbc hbt hbx hct hcx htx hBridge hBookAt
  have hden : 1 ≤
      ((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1 := by
    have hq : (2 : ℚ) ≤ (completionVertices H V ({b, c} : Edge α)).card := by
      exact_mod_cast hdeg
    linarith
  have hPayA : positiveRootedWeight H V a c b /
      (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1) ≤
      localPhi (r + 1) := by
    apply (div_le_iff₀ (by linarith : 0 <
      ((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1)).mpr
    have hnonneg : 0 ≤ positiveRootedWeight H V a c b := by
      unfold positiveRootedWeight
      exact le_max_right _ _
    nlinarith
  have hPayT : positiveRootedWeight H V t c b /
      (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1) ≤
      localPhi (s + 1) := by
    apply (div_le_iff₀ (by linarith : 0 <
      ((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1)).mpr
    have hnonneg : 0 ≤ positiveRootedWeight H V t c b := by
      unfold positiveRootedWeight
      exact le_max_right _ _
    nlinarith
  have hPartB : b ∈ actualLocalPartB H V c a t := by
    apply mem_actual_local_part_b.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, t, b} : Edge α) = ({t, b, c} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hTBC'
  have hPartC : b ∈ actualLocalPartC H V c a t := by
    apply mem_actual_local_part_c.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, a, b} : Edge α) = ({a, c, b} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hACB
  have hTBXCanon : ({t, x, b} : Edge α) ∈ H := by
    have heq : ({t, x, b} : Edge α) = ({t, b, x} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hTBX'
  have hABXCanon : ({a, x, b} : Edge α) ∈ H := by
    have heq : ({a, x, b} : Edge α) = ({a, b, x} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hABX'
  have hBridgeCAT : ({c, a, t} : Edge α) ∈ H := by
    have heq : ({c, a, t} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hBridge
  have hGain := bridge_book_actual_defect_gain
    (H := H) (V := V) (a := c) (b := a) (c := t) (d := b) (x := x)
    (r := s) (s := r)
    hH hUniform hground hac.symm hct hat hBridgeCAT hx hPartB hPartC
    (by
      apply mem_actual_local_ab.mpr
      exact ⟨hx, hPartB, hTBXCanon⟩)
    (by
      apply mem_actual_local_ac.mpr
      exact ⟨hx, hPartC, hABXCanon⟩)
    hBookAt hsDegree hrDegree hs hr
  have hMin : min (localPhi (r + 1)) (localPhi (s + 1)) ≤
      localSignedDefect H V ({a, c, t} : Edge α) := by
    have hEdge : ({c, a, t} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    simpa [hEdge, min_comm] using hGain
  exact (min_le_min hPayA hPayT).trans hMin

/-- The same payment theorem with the two roots of the book exchanged.
This is useful when the manuscript names the other book page as the
distinguished page; the marked local degrees exchange their AB/AC roles. -/
theorem bridge_book_manuscript_payment_symm
    {H : Family α} {V : Edge α} {a t b c x : α} {r s : ℕ}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x)
    (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hrDegree : bipRightDegree (actualLocalTripartite H V c a t).ac
      ((actualLocalPartA H V c a t).erase x) b = r)
    (hsDegree : bipRightDegree (actualLocalTripartite H V c a t).ab
      ((actualLocalPartA H V c a t).erase x) b = s)
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    min
      (positiveRootedWeight H V t c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      (positiveRootedWeight H V a c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      ≤ localSignedDefect H V ({a, c, t} : Edge α) := by
  have hBookSwap : orientedCommonLink H V t a =
      ({{b, c}, {b, x}} : Family α) := by
    rw [oriented_common_link_swap H V hat, hBookAt]
  have hBridgeSwap : ({t, c, a} : Edge α) ∈ H := by
    have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
      ext q
      simp [or_comm, or_left_comm]
    exact heq ▸ hBridge
  have hxSwap : x ∈ actualLocalPartA H V c t a := by
    rw [bridge_local_a_swap H V a c t]
    exact hx
  have hrSwap : bipRightDegree (actualLocalTripartite H V c t a).ac
      ((actualLocalPartA H V c t a).erase x) b = s := by
    rw [bridge_graph_ac_swap H V a c t, bridge_local_a_swap H V a c t]
    exact hsDegree
  have hsSwap : bipRightDegree (actualLocalTripartite H V c t a).ab
      ((actualLocalPartA H V c t a).erase x) b = r := by
    rw [← bridge_graph_ac_swap H V t c a,
      ← bridge_local_a_swap H V t c a]
    exact hrDegree
  have hBookCxSwap : orientedCommonLink H V c x =
      ({{t, b}, {t, a}, {b, a}} : Family α) := by
    rw [hBookCx]
    ext p
    simp [Finset.pair_comm]
    tauto
  have hPaid := bridge_book_manuscript_payment
    (H := H) (V := V) (a := t) (t := a) (b := b) (c := c) (x := x)
    (r := s) (s := r) hH hUniform hground hbt.symm hct.symm hat.symm hbc
    hab.symm hbx hac.symm hcx hax htx hBridgeSwap hBookSwap
    hBookCxSwap hxSwap hrSwap hsSwap hs hr
  have hEdge : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
    ext q
    simp [or_comm, or_left_comm]
  simpa [min_comm, hEdge] using hPaid

/-- If both directed source weights are genuinely positive, the minimum
payment furnished by the bridge theorem is positive, so the bridge defect
is positive as well. -/
theorem minimum_actual_demand_positive_forces_defect_positive
    {H : Family α} {V : Edge α} {a t b c : α}
    (hDegree : 2 ≤ (completionVertices H V ({b, c} : Edge α)).card)
    (hA : 0 < rootedSignedWeight H V a c b)
    (hT : 0 < rootedSignedWeight H V t c b)
    (hPaid : min
      (positiveRootedWeight H V a c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      (positiveRootedWeight H V t c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1)) ≤
      localSignedDefect H V ({a, c, t} : Edge α)) :
    0 < localSignedDefect H V ({a, c, t} : Edge α) := by
  have hden : 0 <
      ((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1 := by
    have hq : (2 : ℚ) ≤ (completionVertices H V ({b, c} : Edge α)).card := by
      exact_mod_cast hDegree
    linarith
  have hPosA : 0 < positiveRootedWeight H V a c b := by
    unfold positiveRootedWeight
    exact lt_of_lt_of_le hA (le_max_left _ _)
  have hPosT : 0 < positiveRootedWeight H V t c b := by
    unfold positiveRootedWeight
    exact lt_of_lt_of_le hT (le_max_left _ _)
  have hChargeA : 0 < positiveRootedWeight H V a c b /
      (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1) :=
    div_pos hPosA hden
  have hChargeT : 0 < positiveRootedWeight H V t c b /
      (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1) :=
    div_pos hPosT hden
  exact lt_of_lt_of_le (lt_min hChargeA hChargeT) hPaid

end JSP523.Rank3
