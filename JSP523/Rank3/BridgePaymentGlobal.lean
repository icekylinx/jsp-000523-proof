import JSP523.Rank3.BridgeDemandGlobal
import JSP523.Rank3.BridgePayment

/-!
# Global bridge-payment interface

This module proves the unconditional per-demand bridge payment. Positive
demands are paid from the marked reciprocal-book geometry; nonpositive
demands are paid by local defect nonnegativity.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

private theorem common_link_eq_oriented_of_ne_global
    (H : Family α) (V : Edge α) {z v : α} (hzv : z ≠ v) :
    commonLink H V ({z, v} : Edge α) = orientedCommonLink H V z v := by
  ext p
  exact mem_common_link_pair_iff_oriented H V hzv p

/-- Convert the canonical receiver-book equations into the oriented book
needed by the manuscript payment theorem. -/
theorem exceptional_book_oriented_links
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    orientedCommonLink H V d.z d.v =
        ({{d.x, d.y}, {d.x, d.u}} : Family α) ∧
      orientedCommonLink H V d.y d.u =
        ({{d.x, d.z}, {d.x, d.v}, {d.z, d.v}} : Family α) := by
  obtain ⟨hzv, hxy, hxu, hyu⟩ := exceptional_receiver_book_data_distinct d
  have hq' : q = ({d.z, d.v} : Edge α) := d.hq
  constructor
  · calc
      orientedCommonLink H V d.z d.v = commonLink H V ({d.z, d.v} : Edge α) :=
        (common_link_eq_oriented_of_ne_global H V hzv).symm
      _ = ({{d.x, d.y}, {d.x, d.u}} : Family α) := by simpa [hq'] using d.hbook
  · calc
      orientedCommonLink H V d.y d.u = commonLink H V ({d.y, d.u} : Edge α) :=
        (common_link_eq_oriented_of_ne_global H V hyu).symm
      _ = ({{d.x, d.z}, {d.x, d.v}, {d.z, d.v}} : Family α) := by
        simpa [Finset.pair_comm] using d.hreciprocal

/-- The reciprocal book page supplies the two bridge triples themselves. -/
theorem exceptional_book_bridge_triples_mem
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q) :
    ({d.z, d.v, d.y} : Edge α) ∈ H ∧
      ({d.z, d.v, d.u} : Edge α) ∈ H := by
  obtain ⟨_, _, _, _⟩ := exceptional_receiver_book_data_distinct d
  have hPages := exceptional_book_oriented_links d
  have hPage : ({d.z, d.v} : Edge α) ∈ orientedCommonLink H V d.y d.u := by
    rw [hPages.2]
    simp
  obtain ⟨_, _, hy, hu⟩ := Finset.mem_filter.mp hPage
  constructor
  · have heq : ({d.z, d.v} : Edge α) ∪ {d.y} =
        ({d.z, d.v, d.y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hy
  · have heq : ({d.z, d.v} : Edge α) ∪ {d.u} =
        ({d.z, d.v, d.u} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq ▸ hu

/-- Cardinal bookkeeping for the full auxiliary degree argument: every
noncentral receiver-link edge is assigned to a neighbor of one of the two
marked local parts. -/
theorem common_link_card_le_one_add_two_neighbor_sets
    (H : Family α) (V : Edge α) {a c b t : α}
    (N₁ N₂ : Finset α)
    (hSplit : ∀ p ∈ commonLink H V ({b, t} : Edge α),
      p ≠ ({a, c} : Edge α) →
        (∃ u ∈ N₁, p = ({a, u} : Edge α)) ∨
        (∃ u ∈ N₂, p = ({c, u} : Edge α))) :
    (commonLink H V ({b, t} : Edge α)).card ≤ N₁.card + N₂.card + 1 := by
  let S := insert ({a, c} : Edge α)
    ((N₁.image fun u => ({a, u} : Edge α)) ∪
      (N₂.image fun u => ({c, u} : Edge α)))
  have hSub : commonLink H V ({b, t} : Edge α) ⊆ S := by
    intro p hp
    by_cases heq : p = ({a, c} : Edge α)
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · rcases hSplit p hp heq with ⟨u, hu, heq⟩ | ⟨u, hu, heq⟩
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_image.mpr
        exact ⟨u, hu, heq.symm⟩
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        exact ⟨u, hu, heq.symm⟩
  have hCard := Finset.card_le_card hSub
  have hS : S.card ≤ N₁.card + N₂.card + 1 := by
    dsimp [S]
    calc
      (insert ({a, c} : Edge α)
        ((N₁.image fun u => ({a, u} : Edge α)) ∪
          (N₂.image fun u => ({c, u} : Edge α)))).card ≤
        ((N₁.image fun u => ({a, u} : Edge α)) ∪
          (N₂.image fun u => ({c, u} : Edge α))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (N₁.image fun u => ({a, u} : Edge α)).card +
          (N₂.image fun u => ({c, u} : Edge α)).card + 1 := by
          exact Nat.add_le_add_right
            (Finset.card_union_le
              (N₁.image fun u => ({a, u} : Edge α))
              (N₂.image fun u => ({c, u} : Edge α))) 1
      _ ≤ N₁.card + N₂.card + 1 := by
          exact Nat.add_le_add_right
            (Nat.add_le_add Finset.card_image_le Finset.card_image_le) 1
  exact hCard.trans hS

private theorem pair_eq_of_two_members_global
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

/-- The reciprocal book bounds the receiving link using both kinds of
neighbors of its marked B node.  A neighbor in A gives a pair through a;
a neighbor in C gives a pair through c. -/
theorem bridge_book_receiver_link_card_le_total_degree
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hct : c ≠ t)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBook : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t) :
    (commonLink H V ({b, t} : Edge α)).card ≤
      bipRightDegree (actualLocalTripartite H V c a t).ac
        (actualLocalPartA H V c a t) b +
      bipRightDegree (actualLocalTripartite H V c a t).bc
        (actualLocalPartB H V c a t) b + 1 := by
  let A := actualLocalPartA H V c a t
  let B := actualLocalPartB H V c a t
  let C := actualLocalPartC H V c a t
  let G := actualLocalTripartite H V c a t
  have hPageBC : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]; simp
  have hPageBX : ({b, x} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBook]; simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hPageBX
  have hSrc : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq] at hABC; exact hABC
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq] at hTBX; exact hTBX
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
        rcases hqP with hqa | hqc <;> rcases hqCell with hqb | hqt
        · exact hab (hqa.symm.trans hqb)
        · exact hat (hqa.symm.trans hqt)
        · exact hbc.symm (hqc.symm.trans hqb)
        · exact hct (hqc.symm.trans hqt)
      · have heq : ({a, c} : Edge α) ∪ {b} = {a, b, c} := by
          ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [heq]; exact hSrc
      · have heq : ({a, c} : Edge α) ∪ {t} = {a, c, t} := by
          ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [heq]; exact hBridge
  have hbB : b ∈ B := by
    change b ∈ actualLocalPartB H V c a t
    apply mem_actual_local_part_b.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, t, b} : Edge α) = ({b, c} : Edge α) ∪ {t} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hTBC
  have hbC : b ∈ C := by
    change b ∈ actualLocalPartC H V c a t
    apply mem_actual_local_part_c.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hSrc
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq] at hABX; exact hABX
  have hABedge : (x, b) ∈ G.ab := by
    change (x, b) ∈ (actualLocalTripartite H V c a t).ab
    apply mem_actual_local_ab.mpr
    refine ⟨hx, hbB, ?_⟩
    have heq : ({t, b, x} : Edge α) = ({t, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hTBX'
  have hACedge : (x, b) ∈ G.ac := by
    change (x, b) ∈ (actualLocalTripartite H V c a t).ac
    apply mem_actual_local_ac.mpr
    refine ⟨hx, hbC, ?_⟩
    have heq : ({a, b, x} : Edge α) = ({a, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hABX'
  let N₁ := A.filter (fun u => (u, b) ∈ G.ac)
  let N₂ := B.filter (fun u => (u, b) ∈ G.bc)
  have hSplit : ∀ p ∈ commonLink H V ({b, t} : Edge α),
      p ≠ ({a, c} : Edge α) →
        (∃ u ∈ N₁, p = ({a, u} : Edge α)) ∨
        (∃ u ∈ N₂, p = ({c, u} : Edge α)) := by
    intro p hp hpNe
    obtain ⟨hpV, hpCert⟩ := Finset.mem_filter.mp hp
    obtain ⟨v₁, hv₁, v₂, hv₂, hvne, hpDisj, hpB, hpT⟩ := hpCert
    have hhit : ¬ Disjoint p ({a, c} : Edge α) :=
      common_link_intersecting_of_ground_cell hH hCell hp hCenter
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hpV).2
    have hmeet : a ∈ p ∨ c ∈ p := by
      by_contra h
      apply hhit
      apply Finset.disjoint_left.mpr
      intro q hqp hqac
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqac
      rcases hqac with hqa | hqc
      · exact (not_or.mp h).1 (hqa ▸ hqp)
      · exact (not_or.mp h).2 (hqc ▸ hqp)
    have hPB : p ∪ {b} ∈ H := by
      have hc₁ : v₁ = b ∨ v₁ = t := by simpa using hv₁
      have hc₂ : v₂ = b ∨ v₂ = t := by simpa using hv₂
      rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
      · exact False.elim (hvne rfl)
      · exact hpB
      · exact hpT
      · exact False.elim (hvne rfl)
    have hPT : p ∪ {t} ∈ H := by
      have hc₁ : v₁ = b ∨ v₁ = t := by simpa using hv₁
      have hc₂ : v₂ = b ∨ v₂ = t := by simpa using hv₂
      rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
      · exact False.elim (hvne rfl)
      · exact hpT
      · exact hpB
      · exact False.elim (hvne rfl)
    rcases hmeet with haP | hcP
    · have huNeC : c ∉ p := by
        intro hcP'
        exact hpNe (pair_eq_of_two_members_global hp2 haP hcP' hac)
      have hrest : (p.erase a).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one haP
        omega
      obtain ⟨u, huErase⟩ := hrest
      have hau : a ≠ u := (Finset.mem_erase.mp huErase).1.symm
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpV).1 huP
      have huA : u ∈ A := by
        change u ∈ actualLocalPartA H V c a t
        apply mem_actual_local_part_a.mpr
        refine ⟨huV, ?_, Ne.symm hau, ?_, ?_⟩
        · intro he; subst u; exact huNeC huP
        · intro he; subst u; exact (Finset.disjoint_left.mp hpDisj) huP (by simp)
        · have heq : p ∪ {t} = ({a, t, u} : Edge α) := by
            rw [pair_eq_of_two_members_global hp2 haP huP hau]
            ext q; simp [or_comm]
          rw [← heq]; exact hPT
      have huAC : (u, b) ∈ G.ac := by
        change (u, b) ∈ (actualLocalTripartite H V c a t).ac
        apply mem_actual_local_ac.mpr
        refine ⟨huA, hbC, ?_⟩
        have heq : p ∪ {b} = ({a, u, b} : Edge α) := by
          rw [pair_eq_of_two_members_global hp2 haP huP hau]
          ext q; simp [or_comm]
        rw [heq] at hPB
        simpa [or_comm, or_left_comm] using hPB
      left
      exact ⟨u, by change u ∈ A.filter (fun u => (u, b) ∈ G.ac); exact Finset.mem_filter.mpr ⟨huA, huAC⟩,
        pair_eq_of_two_members_global hp2 haP huP hau⟩
    · have huNeA : a ∉ p := by
        intro haP'
        exact hpNe (by simpa [Finset.pair_comm] using pair_eq_of_two_members_global hp2 hcP haP' hac.symm)
      have hrest : (p.erase c).Nonempty := by
        apply Finset.card_pos.mp
        have hErase := Finset.card_erase_add_one hcP
        omega
      obtain ⟨u, huErase⟩ := hrest
      have hcu : c ≠ u := (Finset.mem_erase.mp huErase).1.symm
      have huP : u ∈ p := (Finset.mem_erase.mp huErase).2
      have huV : u ∈ V := (Finset.mem_powersetCard.mp hpV).1 huP
      have huB : u ∈ B := by
        change u ∈ actualLocalPartB H V c a t
        apply mem_actual_local_part_b.mpr
        refine ⟨huV, Ne.symm hcu, ?_, ?_, ?_⟩
        · intro he; subst u; exact huNeA huP
        · intro he; subst u
          exact (Finset.disjoint_left.mp hpDisj) huP (by simp)
        · have heq : p ∪ {t} = ({c, t, u} : Edge α) := by
            rw [pair_eq_of_two_members_global hp2 hcP huP hcu]
            ext q; simp [or_comm]
          rw [← heq]; exact hPT
      have huBC : (u, b) ∈ G.bc := by
        change (u, b) ∈ (actualLocalTripartite H V c a t).bc
        apply mem_actual_local_bc.mpr
        refine ⟨huB, hbC, ?_⟩
        have heq : p ∪ {b} = ({c, u, b} : Edge α) := by
          rw [pair_eq_of_two_members_global hp2 hcP huP hcu]
          ext q; simp [or_comm]
        rw [heq] at hPB
        simpa [or_comm, or_left_comm] using hPB
      right
      exact ⟨u, by change u ∈ B.filter (fun u => (u, b) ∈ G.bc); exact Finset.mem_filter.mpr ⟨huB, huBC⟩,
        pair_eq_of_two_members_global hp2 hcP huP hcu⟩
  have hCard := common_link_card_le_one_add_two_neighbor_sets H V N₁ N₂ hSplit
  simpa [N₁, N₂, bipRightDegree, bipLeftDegree, A, B, G] using hCard

/-- A positive source cannot have fewer than three total marked
neighbors.  The receiving-link count includes both its AC and BC
neighbors, exactly as in the manuscript's identity `c(bt)=1+d_K(B_b)`. -/
theorem bridge_book_positive_source_forces_marked_total_degree
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hpositive : 0 < rootedSignedWeight H V a c b) :
    3 ≤ bipRightDegree (actualLocalTripartite H V c a t).ac
        (actualLocalPartA H V c a t) b +
      bipRightDegree (actualLocalTripartite H V c a t).bc
        (actualLocalPartB H V c a t) b := by
  have hAlt := bridge_book_source_alternatives_mem hground hab hac hat
    hbc hbt hbx hct hcx htx hBridge hBookAt
  have hPageBC : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBookAt]; simp
  have hPageBX : ({b, x} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBookAt]; simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hABC
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
  have hCardBT := bridge_book_receiver_link_card_le_total_degree
    hH hground hab hac hat hbc hbt hct hBridge hBookAt hx
  have hCommonA : (rootCommonNeighbors H V a b t).card ≤
      bipRightDegree (actualLocalTripartite H V c a t).ac
        (actualLocalPartA H V c a t) b +
      bipRightDegree (actualLocalTripartite H V c a t).bc
        (actualLocalPartB H V c a t) b + 1 := by
    have heq := root_common_neighbors_eq_common_link_fiber H V haV hab hat hbt
    rw [heq]
    exact (common_link_fiber_card_le_common_link_card H V {b, t} a).trans hCardBT
  have hRoot : ({c, b} : Edge α) ∈ rootLink H V a := by
    simpa [Finset.pair_comm] using oriented_common_link_pair_mem_root_link H V hPageBC
  have hWeight := rooted_signed_weight_le_weight_fraction_of_two_alternatives
    H V hRoot hbc.symm hAlt.2.1 hAlt.1 hCounts.1 hCommonA
  let D := bipRightDegree (actualLocalTripartite H V c a t).ac
        (actualLocalPartA H V c a t) b +
      bipRightDegree (actualLocalTripartite H V c a t).bc
        (actualLocalPartB H V c a t) b
  have hWeightD : rootedSignedWeight H V a c b ≤ weightFraction (D + 1) := by
    dsimp [D] at hWeight ⊢
    exact hWeight
  have hFractionPos : 0 < weightFraction (D + 1) := lt_of_lt_of_le hpositive hWeightD
  by_contra hD
  have hSmall : D + 1 ≤ 3 := by omega
  rw [weight_fraction_eq_zero_of_le_three hSmall] at hFractionPos
  norm_num at hFractionPos

/-- Once the marked node has total degree at least three, the mixed-node
property rules out BC neighbors and leaves at least two erased AC
neighbors. -/
theorem bridge_book_positive_source_forces_erased_ac_degree_ge_two
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hpositive : 0 < rootedSignedWeight H V a c b) :
    2 ≤ bipRightDegree (actualLocalTripartite H V c a t).ac
      ((actualLocalPartA H V c a t).erase x) b := by
  let A := actualLocalPartA H V c a t
  let B := actualLocalPartB H V c a t
  let C := actualLocalPartC H V c a t
  let G := actualLocalTripartite H V c a t
  have hTotal := bridge_book_positive_source_forces_marked_total_degree
    hH hground hab hac hat hbc hbt hbx hct hcx htx hax hBridge
    hBookAt hBookCx hx hpositive
  have hPageBC : ({b, c} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBookAt]; simp
  have hPageBX : ({b, x} : Edge α) ∈ orientedCommonLink H V a t := by
    rw [hBookAt]; simp
  obtain ⟨_, _, hABC, hTBC⟩ := Finset.mem_filter.mp hPageBC
  obtain ⟨_, _, hABX, hTBX⟩ := Finset.mem_filter.mp hPageBX
  have hABC' : ({a, b, c} : Edge α) ∈ H := by
    have heq : ({b, c} : Edge α) ∪ {a} = {a, b, c} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hABC
  have hTBX' : ({t, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {t} = {t, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hTBX
  have hbV : b ∈ V := hground _ hABC' (by simp)
  have htV : t ∈ V := hground _ hBridge (by simp)
  have haV : a ∈ V := hground _ hBridge (by simp)
  have hbB : b ∈ B := by
    apply mem_actual_local_part_b.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, t, b} : Edge α) = ({b, c} : Edge α) ∪ {t} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hTBC
  have hbC : b ∈ C := by
    apply mem_actual_local_part_c.mpr
    refine ⟨hbV, hbc, hab.symm, hbt, ?_⟩
    have heq : ({c, a, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [heq]; exact hABC'
  have hABX' : ({a, b, x} : Edge α) ∈ H := by
    have heq : ({b, x} : Edge α) ∪ {a} = {a, b, x} := by
      ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    exact heq.symm ▸ hABX
  have hABedge : (x, b) ∈ G.ab := by
    apply mem_actual_local_ab.mpr
    refine ⟨hx, hbB, ?_⟩
    have heq : ({t, b, x} : Edge α) = ({t, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hTBX'
  have hACedge : (x, b) ∈ G.ac := by
    apply mem_actual_local_ac.mpr
    refine ⟨hx, hbC, ?_⟩
    have heq : ({a, b, x} : Edge α) = ({a, x, b} : Edge α) := by
      ext q; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [← heq]; exact hABX'
  have hMixed : MixedNodeDegreeTwo G A B C :=
    actual_local_tripartite_mixed_degree_two hH hUniform hac.symm hct hat
  have hABpos : 0 < bipLeftDegree G.ab B x :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbB, hABedge⟩⟩
  have hACposX : 0 < bipLeftDegree G.ac C x :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbC, hACedge⟩⟩
  have hACone : C.filter (fun z => (x, z) ∈ G.ac) = {b} := by
    have hCard : (C.filter (fun z => (x, z) ∈ G.ac)).card = 1 :=
      (hMixed.1 x hx hABpos hACposX).2
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hCard
    have hbmem : b ∈ C.filter (fun z => (x, z) ∈ G.ac) :=
      Finset.mem_filter.mpr ⟨hbC, hACedge⟩
    rw [hz] at hbmem
    have hbz : b = z := by simpa using hbmem
    simpa [hbz] using hz
  have hACpos : 0 < bipRightDegree G.ac A b := by
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hACedge⟩⟩
  have hBCzero : bipRightDegree G.bc B b = 0 := by
    by_contra hzero
    have hBCpos : 0 < bipRightDegree G.bc B b := Nat.pos_of_ne_zero hzero
    have hOne := hMixed.2.2 b hbC hACpos hBCpos
    rcases hOne with ⟨hAConeB, hBConeB⟩
    rw [hAConeB, hBConeB] at hTotal
    omega
  have hACgeThree : 3 ≤ bipRightDegree G.ac A b := by
    rw [hBCzero] at hTotal
    exact hTotal
  have hACerase : bipRightDegree G.ac A b =
      bipRightDegree G.ac (A.erase x) b + 1 :=
    bip_right_degree_erase_left_neighbor G.ac A C x b hx hACone
  rw [hACerase] at hACgeThree
  change 3 ≤ bipRightDegree G.ac (A.erase x) b + 1 at hACgeThree
  change 2 ≤ bipRightDegree G.ac (A.erase x) b
  omega

private theorem bridge_local_a_swap_global
    (H : Family α) (V : Edge α) (a c t : α) :
    actualLocalPartA H V c t a = actualLocalPartA H V c a t := by
  rw [actual_local_part_a_eq_completion_vertices_erase,
    actual_local_part_a_eq_completion_vertices_erase]
  simp [Finset.pair_comm]

private theorem bridge_local_c_swap_global
    (H : Family α) (V : Edge α) (a c t : α) :
    actualLocalPartC H V c t a = actualLocalPartB H V c a t := by
  rw [actual_local_part_c_eq_completion_vertices_erase,
    actual_local_part_b_eq_completion_vertices_erase]

private theorem bridge_graph_ac_swap_global
    (H : Family α) (V : Edge α) (a c t : α) :
    (actualLocalTripartite H V c t a).ac =
      (actualLocalTripartite H V c a t).ab := by
  ext e
  rcases e with ⟨u, v⟩
  rw [mem_actual_local_ac, mem_actual_local_ab,
    bridge_local_a_swap_global H V a c t,
    bridge_local_c_swap_global H V a c t]

private theorem oriented_common_link_swap_global
    (H : Family α) (V : Edge α) {a t : α} :
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

/-- Positive sources at both roots force both erased marked degrees to be
at least two. -/
theorem bridge_book_both_positive_sources_force_erased_degrees
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hpositiveA : 0 < rootedSignedWeight H V a c b)
    (hpositiveT : 0 < rootedSignedWeight H V t c b) :
    2 ≤ bipRightDegree (actualLocalTripartite H V c a t).ac
        ((actualLocalPartA H V c a t).erase x) b ∧
      2 ≤ bipRightDegree (actualLocalTripartite H V c a t).ab
        ((actualLocalPartA H V c a t).erase x) b := by
  have hA := bridge_book_positive_source_forces_erased_ac_degree_ge_two
    hH hUniform hground hab hac hat hbc hbt hbx hct hcx htx hax hBridge
    hBookAt hBookCx hx hpositiveA
  have hBookSwap : orientedCommonLink H V t a =
      ({{b, c}, {b, x}} : Family α) := by
    rw [oriented_common_link_swap_global H V, hBookAt]
  have hBridgeSwap : ({t, c, a} : Edge α) ∈ H := by
    have heq : ({t, c, a} : Edge α) = ({a, c, t} : Edge α) := by
      ext q; simp [or_comm, or_left_comm]
    exact heq ▸ hBridge
  have hxSwap : x ∈ actualLocalPartA H V c t a := by
    rw [bridge_local_a_swap_global H V a c t]
    exact hx
  have hBookCxSwap : orientedCommonLink H V c x =
      ({{t, b}, {t, a}, {b, a}} : Family α) := by
    rw [hBookCx]
    ext p
    simp [Finset.pair_comm]
    tauto
  have hT := bridge_book_positive_source_forces_erased_ac_degree_ge_two
    (H := H) (V := V) (a := t) (t := a) (b := b) (c := c) (x := x)
    hH hUniform hground hbt.symm hct.symm hat.symm hbc hab.symm hbx
    hac.symm hcx hax htx hBridgeSwap hBookSwap hBookCxSwap hxSwap hpositiveT
  constructor
  · exact hA
  · simpa [bridge_graph_ac_swap_global H V a c t,
      bridge_local_a_swap_global H V a c t] using hT

/-- The manuscript's marked-node payment with its degree hypotheses
derived solely from positivity of the two directed source weights. -/
theorem bridge_book_manuscript_payment_of_positive_sources
    {H : Family α} {V : Edge α} {a t b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hat : a ≠ t)
    (hbc : b ≠ c) (hbt : b ≠ t) (hbx : b ≠ x)
    (hct : c ≠ t) (hcx : c ≠ x) (htx : t ≠ x) (hax : a ≠ x)
    (hBridge : ({a, c, t} : Edge α) ∈ H)
    (hBookAt : orientedCommonLink H V a t =
      ({{b, c}, {b, x}} : Family α))
    (hBookCx : orientedCommonLink H V c x =
      ({{a, b}, {a, t}, {b, t}} : Family α))
    (hx : x ∈ actualLocalPartA H V c a t)
    (hpositiveA : 0 < rootedSignedWeight H V a c b)
    (hpositiveT : 0 < rootedSignedWeight H V t c b) :
    min
      (positiveRootedWeight H V a c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      (positiveRootedWeight H V t c b /
        (((completionVertices H V ({b, c} : Edge α)).card : ℚ) - 1))
      ≤ localSignedDefect H V ({a, c, t} : Edge α) := by
  have hdeg := bridge_book_both_positive_sources_force_erased_degrees
    hH hUniform hground hab hac hat hbc hbt hbx hct hcx htx hax hBridge
    hBookAt hBookCx hx hpositiveA hpositiveT
  let r := bipRightDegree (actualLocalTripartite H V c a t).ac
      ((actualLocalPartA H V c a t).erase x) b
  let s := bipRightDegree (actualLocalTripartite H V c a t).ab
      ((actualLocalPartA H V c a t).erase x) b
  have hr : 2 ≤ r := by exact hdeg.1
  have hs : 2 ≤ s := by exact hdeg.2
  have hPaid := bridge_book_manuscript_payment hH hUniform hground
    hab hac hat hbc hbt hbx hct hcx htx hax hBridge hBookAt hBookCx hx
    (by rfl) (by rfl) hr hs
  exact hPaid

/-- A concrete exceptional book's two actual directed charges are paid by
its bridge defect whenever both source weights are positive. -/
theorem exceptional_book_actual_charge_paid
    {H : Family α} {V q : Edge α}
    (d : ExceptionalReceiverBookData H V q)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hpositiveZ : 0 < rootedSignedWeight H V d.z d.x d.y)
    (hpositiveV : 0 < rootedSignedWeight H V d.v d.x d.y) :
    min (actualReceiverCharge H V d.z d.x d.y d.v)
      (actualReceiverCharge H V d.v d.x d.y d.z) ≤
      localSignedDefect H V ({d.z, d.v, d.y} : Edge α) := by
  obtain ⟨hzv, hxy, hxu, hyu⟩ := exceptional_receiver_book_data_distinct d
  obtain ⟨_, hzx, hzy, hzu, hvx, hvy, hvu, _, _, _⟩ :=
    exceptional_receiver_book_data_five_distinct d
  have hPages := exceptional_book_oriented_links d
  have hBridgePair := exceptional_book_bridge_triples_mem d
  have hBridge := hBridgePair.1
  have hBridgeX := hBridgePair.2
  have hxA : d.u ∈ actualLocalPartA H V d.y d.z d.v := by
    apply mem_actual_local_part_a.mpr
    refine ⟨d.huV, ?_, ?_, ?_, hBridgeX⟩
    · exact hyu.symm
    · exact hzu.symm
    · exact hvu.symm
  have hBookAt := hPages.1
  have hBookCx := hPages.2
  have hBridgeY : ({d.z, d.y, d.v} : Edge α) ∈ H := by
    have heq : ({d.z, d.y, d.v} : Edge α) =
        ({d.z, d.v, d.y} : Edge α) := by
      ext q
      simp [or_comm]
    exact heq ▸ hBridge
  have hBookCx' : orientedCommonLink H V d.y d.u =
      ({{d.z, d.x}, {d.z, d.v}, {d.x, d.v}} : Family α) := by
    rw [hBookCx]
    ext p
    simp [Finset.pair_comm]
  have hPay := bridge_book_manuscript_payment_of_positive_sources
    (H := H) (V := V) (a := d.z) (t := d.v) (b := d.x) (c := d.y) (x := d.u)
    hH hUniform hground hzx hzy hzv hxy hvx.symm hxu
    hvy.symm hyu hvu hzu hBridgeY hBookAt hBookCx' hxA
    (by simpa [rooted_signed_weight_comm] using hpositiveZ)
    (by simpa [rooted_signed_weight_comm] using hpositiveV)
  have hRootZ : ({d.x, d.y} : Edge α) ∈ rootLink H V d.z := by
    have hp : ({d.x, d.y} : Edge α) ∈ orientedCommonLink H V d.z d.v := by
      rw [hBookAt]; simp
    exact oriented_common_link_pair_mem_root_link H V hp
  have hBookSwap : orientedCommonLink H V d.v d.z =
      orientedCommonLink H V d.z d.v := oriented_common_link_swap_global H V
  have hRootV : ({d.x, d.y} : Edge α) ∈ rootLink H V d.v := by
    have hp : ({d.x, d.y} : Edge α) ∈ orientedCommonLink H V d.v d.z := by
      rw [hBookSwap, hBookAt]; simp
    exact oriented_common_link_pair_mem_root_link H V hp
  have hzComp : d.z ∈ completionVertices H V ({d.x, d.y} : Edge α) :=
    root_mem_source_completion H V d.hzV hRootZ
  have hvComp : d.v ∈ completionVertices H V ({d.x, d.y} : Edge α) :=
    root_mem_source_completion H V d.hvV hRootV
  have hvErase : d.v ∈
      (completionVertices H V ({d.x, d.y} : Edge α)).erase d.z :=
    Finset.mem_erase.mpr ⟨hzv.symm, hvComp⟩
  have hzErase : d.z ∈
      (completionVertices H V ({d.x, d.y} : Edge α)).erase d.v :=
    Finset.mem_erase.mpr ⟨hzv, hzComp⟩
  have hChargeZ : actualReceiverCharge H V d.z d.x d.y d.v =
      positiveRootedWeight H V d.z d.x d.y /
        (((completionVertices H V ({d.x, d.y} : Edge α)).card : ℚ) - 1) := by
    simp [actualReceiverCharge, hvErase, chargePerOtherCompletion]
  have hChargeV : actualReceiverCharge H V d.v d.x d.y d.z =
      positiveRootedWeight H V d.v d.x d.y /
        (((completionVertices H V ({d.x, d.y} : Edge α)).card : ℚ) - 1) := by
    simp [actualReceiverCharge, hzErase, chargePerOtherCompletion]
  rw [hChargeZ, hChargeV]
  rw [positive_rooted_weight_comm H V d.z d.x d.y,
    positive_rooted_weight_comm H V d.v d.x d.y]
  have hEdge : ({d.z, d.y, d.v} : Edge α) =
      ({d.z, d.v, d.y} : Edge α) := by
    ext q
    simp [or_comm]
  rw [hEdge] at hPay
  exact hPay

/-- A nonpositive indexed bridge demand is paid by the actual local
nonnegativity of the triple defect. -/
theorem bridge_demand_le_local_signed_defect_of_nonpositive
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ F ∈ H, F ⊆ V) (hE : E ∈ H)
    (hDemand : bridgeDemand H V q E ≤ 0) :
    bridgeDemand H V q E ≤ localSignedDefect H V E := by
  have hdef := local_signed_defect_nonneg hH hUniform hground hE
  linarith

/-- Every positive indexed bridge demand is paid by the defect of its
bridge triple. -/
theorem bridge_demand_le_local_signed_defect_of_positive
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ F ∈ H, F ⊆ V) (_hE : E ∈ H)
    (hDemand : 0 < bridgeDemand H V q E) :
    bridgeDemand H V q E ≤ localSignedDefect H V E := by
  classical
  by_cases hq : triangleExceptionalReceiverCell H V q
  · let d := canonicalExceptionalReceiverBookData H V q hq
    have hFormula : bridgeDemand H V q E =
        if E = ({d.z, d.v, d.y} : Edge α) then
          min (actualReceiverCharge H V d.z d.x d.y d.v)
            (actualReceiverCharge H V d.v d.x d.y d.z)
        else if E = ({d.z, d.v, d.u} : Edge α) then
          min (actualReceiverCharge H V d.z d.x d.u d.v)
            (actualReceiverCharge H V d.v d.x d.u d.z)
        else 0 := by
      simp [bridgeDemand, hq, d]
    by_cases hEy : E = ({d.z, d.v, d.y} : Edge α)
    · have hMinPos : 0 < min
          (actualReceiverCharge H V d.z d.x d.y d.v)
          (actualReceiverCharge H V d.v d.x d.y d.z) := by
        rw [hFormula, ite_eq_left hEy] at hDemand
        exact hDemand
      have hsrcZ : 0 < rootedSignedWeight H V d.z d.x d.y :=
        actual_receiver_charge_pos_signed_weight H V _ _ _ _ (lt_min_iff.mp hMinPos).1
      have hsrcV : 0 < rootedSignedWeight H V d.v d.x d.y :=
        actual_receiver_charge_pos_signed_weight H V _ _ _ _ (lt_min_iff.mp hMinPos).2
      have hPaid := exceptional_book_actual_charge_paid d hH hUniform hground
        hsrcZ hsrcV
      have hEdge : ({d.z, d.v, d.y} : Edge α) = E := hEy.symm
      rw [hFormula, ite_eq_left hEy, ← hEdge]
      exact hPaid
    · by_cases hEu : E = ({d.z, d.v, d.u} : Edge α)
      · have hMinPos : 0 < min
            (actualReceiverCharge H V d.z d.x d.u d.v)
            (actualReceiverCharge H V d.v d.x d.u d.z) := by
          rw [hFormula, ite_eq_right hEy, ite_eq_left hEu] at hDemand
          exact hDemand
        let d' := swapExceptionalReceiverBookPages d
        have hsrcZ : 0 < rootedSignedWeight H V d'.z d'.x d'.y := by
          simpa [d', swapExceptionalReceiverBookPages] using
            actual_receiver_charge_pos_signed_weight H V d.z d.x d.u d.v
              (lt_min_iff.mp hMinPos).1
        have hsrcV : 0 < rootedSignedWeight H V d'.v d'.x d'.y := by
          simpa [d', swapExceptionalReceiverBookPages] using
            actual_receiver_charge_pos_signed_weight H V d.v d.x d.u d.z
              (lt_min_iff.mp hMinPos).2
        have hPaid := exceptional_book_actual_charge_paid d' hH hUniform hground
          hsrcZ hsrcV
        have hDemandEq : bridgeDemand H V q E =
            min (actualReceiverCharge H V d'.z d'.x d'.y d'.v)
              (actualReceiverCharge H V d'.v d'.x d'.y d'.z) := by
          rw [hFormula, ite_eq_right hEy, ite_eq_left hEu]
          simp [d', swapExceptionalReceiverBookPages]
        have hEdge : ({d'.z, d'.v, d'.y} : Edge α) = E := by
          simpa [d', swapExceptionalReceiverBookPages] using hEu.symm
        rw [hDemandEq, ← hEdge]
        exact hPaid
      · rw [hFormula, ite_eq_right hEy, ite_eq_right hEu] at hDemand
        norm_num at hDemand
  · simp [bridgeDemand, hq] at hDemand

/-- Geometry and nonnegativity together give the per demand payment used
by the finite bridge-demand sum. -/
theorem bridge_demand_le_local_signed_defect_of_geometry
    (H : Family α) (V : Edge α) (q E : Edge α)
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ F ∈ H, F ⊆ V) (hE : E ∈ H) :
    bridgeDemand H V q E ≤ localSignedDefect H V E := by
  by_cases hDemand : bridgeDemand H V q E ≤ 0
  · exact bridge_demand_le_local_signed_defect_of_nonpositive
      H V q E hH hUniform hground hE hDemand
  · exact bridge_demand_le_local_signed_defect_of_positive
      H V q E hH hUniform hground hE (lt_of_not_ge hDemand)

end JSP523.Rank3
