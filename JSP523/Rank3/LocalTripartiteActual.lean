import JSP523.Rank3.LocalTripartiteComplete
import JSP523.Rank3.CommonLinkIntersecting

/-!
# The actual local tripartite graph around a triple

The three node parts consist of the other completion vertices of the
central triple's pairs.  The pair-type edges are actual triples of the
parent hypergraph.  This is the graph used in §II.A.1.
-/

namespace JSP523.Rank3

section ActualTripartite

variable {α : Type*} [DecidableEq α]

def actualLocalPartA
    (H : Family α) (V : Edge α) (a b c : α) : Edge α :=
  V.filter fun x => x ≠ a ∧ x ≠ b ∧ x ≠ c ∧
    ({b, c, x} : Edge α) ∈ H

def actualLocalPartB
    (H : Family α) (V : Edge α) (a b c : α) : Edge α :=
  V.filter fun y => y ≠ a ∧ y ≠ b ∧ y ≠ c ∧
    ({a, c, y} : Edge α) ∈ H

def actualLocalPartC
    (H : Family α) (V : Edge α) (a b c : α) : Edge α :=
  V.filter fun z => z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
    ({a, b, z} : Edge α) ∈ H

theorem mem_actualLocalPartA
    {H : Family α} {V : Edge α} {a b c x : α} :
    x ∈ actualLocalPartA H V a b c ↔
      x ∈ V ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧
        ({b, c, x} : Edge α) ∈ H := by
  simp [actualLocalPartA]

theorem mem_actualLocalPartB
    {H : Family α} {V : Edge α} {a b c y : α} :
    y ∈ actualLocalPartB H V a b c ↔
      y ∈ V ∧ y ≠ a ∧ y ≠ b ∧ y ≠ c ∧
        ({a, c, y} : Edge α) ∈ H := by
  simp [actualLocalPartB]

theorem mem_actualLocalPartC
    {H : Family α} {V : Edge α} {a b c z : α} :
    z ∈ actualLocalPartC H V a b c ↔
      z ∈ V ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
        ({a, b, z} : Edge α) ∈ H := by
  simp [actualLocalPartC]

/-- The tagged `A` nodes are exactly the other actual completions of
    the central pair `{b,c}`. -/
theorem actualLocalPartA_eq_completionVertices_erase
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartA H V a b c =
      (completionVertices H V ({b, c} : Edge α)).erase a := by
  ext x
  have hEdgeEq : ({b, c} : Edge α) ∪ {x} =
      ({b, c, x} : Edge α) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [mem_actualLocalPartA, Finset.mem_erase,
    completionVertices, Finset.mem_filter]
  rw [hEdgeEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem actualLocalPartB_eq_completionVertices_erase
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartB H V a b c =
      (completionVertices H V ({a, c} : Edge α)).erase b := by
  ext y
  have hEdgeEq : ({a, c} : Edge α) ∪ {y} =
      ({a, c, y} : Edge α) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [mem_actualLocalPartB, Finset.mem_erase,
    completionVertices, Finset.mem_filter]
  rw [hEdgeEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem actualLocalPartC_eq_completionVertices_erase
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartC H V a b c =
      (completionVertices H V ({a, b} : Edge α)).erase c := by
  ext z
  have hEdgeEq : ({a, b} : Edge α) ∪ {z} =
      ({a, b, z} : Edge α) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  simp only [mem_actualLocalPartC, Finset.mem_erase,
    completionVertices, Finset.mem_filter]
  rw [hEdgeEq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The three pair-type edge sets are filtered from the genuine product
    of their tagged node parts. -/
def actualLocalTripartite
    (H : Family α) (V : Edge α) (a b c : α) :
    TripartitePairGraphs α :=
  let A := actualLocalPartA H V a b c
  let B := actualLocalPartB H V a b c
  let C := actualLocalPartC H V a b c
  ⟨(A.product B).filter (fun e =>
      ({c, e.1, e.2} : Edge α) ∈ H),
   (A.product C).filter (fun e =>
      ({b, e.1, e.2} : Edge α) ∈ H),
   (B.product C).filter (fun e =>
      ({a, e.1, e.2} : Edge α) ∈ H)⟩

theorem mem_actualLocalAB
    {H : Family α} {V : Edge α} {a b c x y : α} :
    (x, y) ∈ (actualLocalTripartite H V a b c).ab ↔
      x ∈ actualLocalPartA H V a b c ∧
      y ∈ actualLocalPartB H V a b c ∧
      ({c, x, y} : Edge α) ∈ H := by
  simp only [actualLocalTripartite, Finset.mem_filter]
  constructor
  · rintro ⟨hxy, hEdge⟩
    exact ⟨(Finset.mem_product.mp hxy).1,
      (Finset.mem_product.mp hxy).2, hEdge⟩
  · rintro ⟨hx, hy, hEdge⟩
    exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hEdge⟩

theorem mem_actualLocalAC
    {H : Family α} {V : Edge α} {a b c x z : α} :
    (x, z) ∈ (actualLocalTripartite H V a b c).ac ↔
      x ∈ actualLocalPartA H V a b c ∧
      z ∈ actualLocalPartC H V a b c ∧
      ({b, x, z} : Edge α) ∈ H := by
  simp only [actualLocalTripartite, Finset.mem_filter]
  constructor
  · rintro ⟨hxz, hEdge⟩
    exact ⟨(Finset.mem_product.mp hxz).1,
      (Finset.mem_product.mp hxz).2, hEdge⟩
  · rintro ⟨hx, hz, hEdge⟩
    exact ⟨Finset.mem_product.mpr ⟨hx, hz⟩, hEdge⟩

theorem mem_actualLocalBC
    {H : Family α} {V : Edge α} {a b c y z : α} :
    (y, z) ∈ (actualLocalTripartite H V a b c).bc ↔
      y ∈ actualLocalPartB H V a b c ∧
      z ∈ actualLocalPartC H V a b c ∧
      ({a, y, z} : Edge α) ∈ H := by
  simp only [actualLocalTripartite, Finset.mem_filter]
  constructor
  · rintro ⟨hyz, hEdge⟩
    exact ⟨(Finset.mem_product.mp hyz).1,
      (Finset.mem_product.mp hyz).2, hEdge⟩
  · rintro ⟨hy, hz, hEdge⟩
    exact ⟨Finset.mem_product.mpr ⟨hy, hz⟩, hEdge⟩

/-- A generic crossed-completion obstruction.  Two pairs supported over
    the same two completion vertices cannot have four crossed parent edges
    unless their external labels agree. -/
theorem crossed_completion_labels_eq
    {H : Family α} {u v s t y z : α}
    (hH : Admissible H)
    (huv : u ≠ v)
    (hst : s ≠ t)
    (hys : y ≠ s) (hyt : y ≠ t)
    (hzs : z ≠ s) (hzt : z ≠ t)
    (huOut : u ∉ ({s, t, y, z} : Edge α))
    (hvOut : v ∉ ({s, t, y, z} : Edge α))
    (hsyu : ({s, y} : Edge α) ∪ {u} ∈ H)
    (hsyv : ({s, y} : Edge α) ∪ {v} ∈ H)
    (htzu : ({t, z} : Edge α) ∪ {u} ∈ H)
    (htzv : ({t, z} : Edge α) ∪ {v} ∈ H) :
    y = z := by
  by_contra hyz
  have hpq : Disjoint ({s, y} : Edge α) ({t, z} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro w hwP hwQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwP hwQ
    rcases hwP with rfl | rfl <;> rcases hwQ with rfl | rfl
    · exact hst rfl
    · exact hzs rfl
    · exact hyt rfl
    · exact hyz rfl
  have huP : u ∉ ({s, y} : Edge α) := by
    intro h
    exact huOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  have hvP : v ∉ ({s, y} : Edge α) := by
    intro h
    exact hvOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  have huQ : u ∉ ({t, z} : Edge α) := by
    intro h
    exact huOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  have hvQ : v ∉ ({t, z} : Edge α) := by
    intro h
    exact hvOut (by simp only [Finset.mem_insert, Finset.mem_singleton] at *; tauto)
  exact common_link_rectangle_forbidden hH huv hpq
    (by simp) (by simp) huP hvP huQ hvQ
    hsyu hsyv htzu htzv

private theorem outer_vertices_distinct_of_triple
    {H : Family α} {s x y : α}
    (hUniform : Uniform 3 H)
    (hEdge : ({s, x, y} : Edge α) ∈ H)
    (hsx : s ≠ x) :
    x ≠ y := by
  intro hxy
  subst y
  have hCard := hUniform hEdge
  have hEq : ({s, x, x} : Edge α) = ({s, x} : Edge α) := by simp
  rw [hEq, Finset.card_pair hsx] at hCard
  omega

/-- A node in the actual `A` part touching both other parts has the same
    physical label at every neighbor in those two parts.  The proof uses
    four actual hyperedges in a forbidden crossed-completion switch. -/
theorem actual_A_cross_neighbor_labels_eq
    {H : Family α} {V : Edge α} {a b c x y z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAB : (x, y) ∈ (actualLocalTripartite H V a b c).ab)
    (hAC : (x, z) ∈ (actualLocalTripartite H V a b c).ac) :
    y = z := by
  obtain ⟨hxA, hyB, hCXY⟩ := mem_actualLocalAB.mp hAB
  obtain ⟨_, hzC, hBXZ⟩ := mem_actualLocalAC.mp hAC
  obtain ⟨_, hxa, hxb, hxc, _⟩ := mem_actualLocalPartA.mp hxA
  obtain ⟨_, hya, hyb, hyc, hACY⟩ := mem_actualLocalPartB.mp hyB
  obtain ⟨_, hza, hzb, hzc, hABZ⟩ := mem_actualLocalPartC.mp hzC
  have hxy : x ≠ y :=
    outer_vertices_distinct_of_triple hUniform hCXY hxc.symm
  have hxz : x ≠ z :=
    outer_vertices_distinct_of_triple hUniform hBXZ hxb.symm
  have haOut : a ∉ ({c, b, y, z} : Edge α) := by
    simp [hac, hab, Ne.symm hya, Ne.symm hza]
  have hxOut : x ∉ ({c, b, y, z} : Edge α) := by
    simp [hxc, hxb, hxy, hxz]
  have hCY_A : ({c, y} : Edge α) ∪ {a} ∈ H := by
    have hEq : ({c, y} : Edge α) ∪ {a} =
        ({a, c, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hACY
  have hCY_X : ({c, y} : Edge α) ∪ {x} ∈ H := by
    have hEq : ({c, y} : Edge α) ∪ {x} =
        ({c, x, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hCXY
  have hBZ_A : ({b, z} : Edge α) ∪ {a} ∈ H := by
    have hEq : ({b, z} : Edge α) ∪ {a} =
        ({a, b, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hABZ
  have hBZ_X : ({b, z} : Edge α) ∪ {x} ∈ H := by
    have hEq : ({b, z} : Edge α) ∪ {x} =
        ({b, x, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBXZ
  exact crossed_completion_labels_eq hH (Ne.symm hxa)
    hbc.symm hyc hyb hzc hzb haOut hxOut
    hCY_A hCY_X hBZ_A hBZ_X

/-- The `A`-part clause of §II.A.1's mixed-node degree-two property,
    derived from actual triple edges and admissibility. -/
theorem actual_A_mixed_degrees_one
    {H : Family α} {V : Edge α} {a b c x : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hABpos : 0 < bipLeftDegree
      (actualLocalTripartite H V a b c).ab
      (actualLocalPartB H V a b c) x)
    (hACpos : 0 < bipLeftDegree
      (actualLocalTripartite H V a b c).ac
      (actualLocalPartC H V a b c) x) :
    bipLeftDegree (actualLocalTripartite H V a b c).ab
        (actualLocalPartB H V a b c) x = 1 ∧
      bipLeftDegree (actualLocalTripartite H V a b c).ac
        (actualLocalPartC H V a b c) x = 1 := by
  let G := actualLocalTripartite H V a b c
  let B := actualLocalPartB H V a b c
  let C := actualLocalPartC H V a b c
  change 0 < (B.filter fun y => (x, y) ∈ G.ab).card at hABpos
  change 0 < (C.filter fun z => (x, z) ∈ G.ac).card at hACpos
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hABpos
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hACpos
  have hAB : (x, y) ∈ G.ab := (Finset.mem_filter.mp hy).2
  have hAC : (x, z) ∈ G.ac := (Finset.mem_filter.mp hz).2
  have hABsub : B.filter (fun y' => (x, y') ∈ G.ab) ⊆
      ({z} : Edge α) := by
    intro y' hy'
    have hAB' : (x, y') ∈ G.ab := (Finset.mem_filter.mp hy').2
    have hy'z := actual_A_cross_neighbor_labels_eq
      hH hUniform hab hac hbc hAB' hAC
    exact Finset.mem_singleton.mpr hy'z
  have hACsub : C.filter (fun z' => (x, z') ∈ G.ac) ⊆
      ({y} : Edge α) := by
    intro z' hz'
    have hAC' : (x, z') ∈ G.ac := (Finset.mem_filter.mp hz').2
    have hyz' := actual_A_cross_neighbor_labels_eq
      hH hUniform hab hac hbc hAB hAC'
    exact Finset.mem_singleton.mpr hyz'.symm
  have hABle : (B.filter fun y' => (x, y') ∈ G.ab).card ≤ 1 :=
    (Finset.card_le_card hABsub).trans (by simp)
  have hACle : (C.filter fun z' => (x, z') ∈ G.ac).card ≤ 1 :=
    (Finset.card_le_card hACsub).trans (by simp)
  change (B.filter fun y' => (x, y') ∈ G.ab).card = 1 ∧
    (C.filter fun z' => (x, z') ∈ G.ac).card = 1
  constructor <;> omega

/-- The cyclic `B`-part crossed-completion obstruction. -/
theorem actual_B_cross_neighbor_labels_eq
    {H : Family α} {V : Edge α} {a b c x y z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAB : (x, y) ∈ (actualLocalTripartite H V a b c).ab)
    (hBC : (y, z) ∈ (actualLocalTripartite H V a b c).bc) :
    z = x := by
  obtain ⟨hxA, hyB, hCXY⟩ := mem_actualLocalAB.mp hAB
  obtain ⟨_, hzC, hAYZ⟩ := mem_actualLocalBC.mp hBC
  obtain ⟨_, hxa, hxb, hxc, hBCX⟩ := mem_actualLocalPartA.mp hxA
  obtain ⟨_, hya, hyb, hyc, _⟩ := mem_actualLocalPartB.mp hyB
  obtain ⟨_, hza, hzb, hzc, hABZ⟩ := mem_actualLocalPartC.mp hzC
  have hxy : x ≠ y :=
    outer_vertices_distinct_of_triple hUniform hCXY hxc.symm
  have hyz : y ≠ z :=
    outer_vertices_distinct_of_triple hUniform hAYZ hya.symm
  have hbOut : b ∉ ({a, c, z, x} : Edge α) := by
    simp [Ne.symm hab, hbc, Ne.symm hzb, Ne.symm hxb]
  have hyOut : y ∉ ({a, c, z, x} : Edge α) := by
    simp [hya, hyc, hyz, Ne.symm hxy]
  have hAZ_B : ({a, z} : Edge α) ∪ {b} ∈ H := by
    have hEq : ({a, z} : Edge α) ∪ {b} =
        ({a, b, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hABZ
  have hAZ_Y : ({a, z} : Edge α) ∪ {y} ∈ H := by
    have hEq : ({a, z} : Edge α) ∪ {y} =
        ({a, y, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hAYZ
  have hCX_B : ({c, x} : Edge α) ∪ {b} ∈ H := by
    have hEq : ({c, x} : Edge α) ∪ {b} =
        ({b, c, x} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBCX
  have hCX_Y : ({c, x} : Edge α) ∪ {y} ∈ H := by
    have hEq : ({c, x} : Edge α) ∪ {y} =
        ({c, x, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hCXY
  exact crossed_completion_labels_eq hH (Ne.symm hyb)
    hac hza hzc hxa hxc hbOut hyOut
    hAZ_B hAZ_Y hCX_B hCX_Y

/-- The cyclic `C`-part crossed-completion obstruction. -/
theorem actual_C_cross_neighbor_labels_eq
    {H : Family α} {V : Edge α} {a b c x y z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hAC : (x, z) ∈ (actualLocalTripartite H V a b c).ac)
    (hBC : (y, z) ∈ (actualLocalTripartite H V a b c).bc) :
    x = y := by
  obtain ⟨hxA, hzC, hBXZ⟩ := mem_actualLocalAC.mp hAC
  obtain ⟨hyB, _, hAYZ⟩ := mem_actualLocalBC.mp hBC
  obtain ⟨_, hxa, hxb, hxc, hBCX⟩ := mem_actualLocalPartA.mp hxA
  obtain ⟨_, hya, hyb, hyc, hACY⟩ := mem_actualLocalPartB.mp hyB
  obtain ⟨_, hza, hzb, hzc, _⟩ := mem_actualLocalPartC.mp hzC
  have hxz : x ≠ z :=
    outer_vertices_distinct_of_triple hUniform hBXZ hxb.symm
  have hyz : y ≠ z :=
    outer_vertices_distinct_of_triple hUniform hAYZ hya.symm
  have hcOut : c ∉ ({b, a, x, y} : Edge α) := by
    simp [Ne.symm hbc, Ne.symm hac, Ne.symm hxc, Ne.symm hyc]
  have hzOut : z ∉ ({b, a, x, y} : Edge α) := by
    simp [hzb, hza, Ne.symm hxz, Ne.symm hyz]
  have hBX_C : ({b, x} : Edge α) ∪ {c} ∈ H := by
    have hEq : ({b, x} : Edge α) ∪ {c} =
        ({b, c, x} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBCX
  have hBX_Z : ({b, x} : Edge α) ∪ {z} ∈ H := by
    have hEq : ({b, x} : Edge α) ∪ {z} =
        ({b, x, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hBXZ
  have hAY_C : ({a, y} : Edge α) ∪ {c} ∈ H := by
    have hEq : ({a, y} : Edge α) ∪ {c} =
        ({a, c, y} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hACY
  have hAY_Z : ({a, y} : Edge α) ∪ {z} ∈ H := by
    have hEq : ({a, y} : Edge α) ∪ {z} =
        ({a, y, z} : Edge α) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hAYZ
  exact crossed_completion_labels_eq hH (Ne.symm hzc)
    hab.symm hxb hxa hyb hya hcOut hzOut
    hBX_C hBX_Z hAY_C hAY_Z

private theorem paired_left_degrees_one_of_cross_eq
    (G₁ G₂ : Finset (α × α)) (B C : Edge α) (x : α)
    (h₁ : 0 < bipLeftDegree G₁ B x)
    (h₂ : 0 < bipLeftDegree G₂ C x)
    (hCross : ∀ y z, (x, y) ∈ G₁ → (x, z) ∈ G₂ → y = z) :
    bipLeftDegree G₁ B x = 1 ∧
      bipLeftDegree G₂ C x = 1 := by
  change 0 < (B.filter fun y => (x, y) ∈ G₁).card at h₁
  change 0 < (C.filter fun z => (x, z) ∈ G₂).card at h₂
  obtain ⟨y, hy⟩ := Finset.card_pos.mp h₁
  obtain ⟨z, hz⟩ := Finset.card_pos.mp h₂
  have hEdge₁ : (x, y) ∈ G₁ := (Finset.mem_filter.mp hy).2
  have hEdge₂ : (x, z) ∈ G₂ := (Finset.mem_filter.mp hz).2
  have hSub₁ : B.filter (fun y' => (x, y') ∈ G₁) ⊆
      ({z} : Edge α) := by
    intro y' hy'
    exact Finset.mem_singleton.mpr
      (hCross y' z (Finset.mem_filter.mp hy').2 hEdge₂)
  have hSub₂ : C.filter (fun z' => (x, z') ∈ G₂) ⊆
      ({y} : Edge α) := by
    intro z' hz'
    exact Finset.mem_singleton.mpr
      (hCross y z' hEdge₁ (Finset.mem_filter.mp hz').2).symm
  have hLe₁ : (B.filter fun y' => (x, y') ∈ G₁).card ≤ 1 :=
    (Finset.card_le_card hSub₁).trans (by simp)
  have hLe₂ : (C.filter fun z' => (x, z') ∈ G₂).card ≤ 1 :=
    (Finset.card_le_card hSub₂).trans (by simp)
  change (B.filter fun y' => (x, y') ∈ G₁).card = 1 ∧
    (C.filter fun z' => (x, z') ∈ G₂).card = 1
  constructor <;> omega

/-- The `B`-part clause of the actual mixed-node property. -/
theorem actual_B_mixed_degrees_one
    {H : Family α} {V : Edge α} {a b c y : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hABpos : 0 < bipRightDegree
      (actualLocalTripartite H V a b c).ab
      (actualLocalPartA H V a b c) y)
    (hBCpos : 0 < bipLeftDegree
      (actualLocalTripartite H V a b c).bc
      (actualLocalPartC H V a b c) y) :
    bipRightDegree (actualLocalTripartite H V a b c).ab
        (actualLocalPartA H V a b c) y = 1 ∧
      bipLeftDegree (actualLocalTripartite H V a b c).bc
        (actualLocalPartC H V a b c) y = 1 := by
  let G := actualLocalTripartite H V a b c
  let A := actualLocalPartA H V a b c
  let C := actualLocalPartC H V a b c
  have hFlipPos : 0 < bipLeftDegree (flipBipartiteGraph G.ab) A y := by
    rw [flip_bipLeftDegree]
    exact hABpos
  have hCross : ∀ z x,
      (y, z) ∈ G.bc →
      (y, x) ∈ flipBipartiteGraph G.ab → z = x := by
    intro z x hBC hFlip
    have hAB : (x, y) ∈ G.ab :=
      (mem_flipBipartiteGraph G.ab x y).mp hFlip
    exact actual_B_cross_neighbor_labels_eq
      hH hUniform hab hac hbc hAB hBC
  have hPair := paired_left_degrees_one_of_cross_eq
    G.bc (flipBipartiteGraph G.ab) C A y hBCpos hFlipPos hCross
  rw [flip_bipLeftDegree] at hPair
  exact ⟨hPair.2, hPair.1⟩

/-- The `C`-part clause of the actual mixed-node property. -/
theorem actual_C_mixed_degrees_one
    {H : Family α} {V : Edge α} {a b c z : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hACpos : 0 < bipRightDegree
      (actualLocalTripartite H V a b c).ac
      (actualLocalPartA H V a b c) z)
    (hBCpos : 0 < bipRightDegree
      (actualLocalTripartite H V a b c).bc
      (actualLocalPartB H V a b c) z) :
    bipRightDegree (actualLocalTripartite H V a b c).ac
        (actualLocalPartA H V a b c) z = 1 ∧
      bipRightDegree (actualLocalTripartite H V a b c).bc
        (actualLocalPartB H V a b c) z = 1 := by
  let G := actualLocalTripartite H V a b c
  let A := actualLocalPartA H V a b c
  let B := actualLocalPartB H V a b c
  have hFlipAC : 0 < bipLeftDegree (flipBipartiteGraph G.ac) A z := by
    rw [flip_bipLeftDegree]
    exact hACpos
  have hFlipBC : 0 < bipLeftDegree (flipBipartiteGraph G.bc) B z := by
    rw [flip_bipLeftDegree]
    exact hBCpos
  have hCross : ∀ x y,
      (z, x) ∈ flipBipartiteGraph G.ac →
      (z, y) ∈ flipBipartiteGraph G.bc → x = y := by
    intro x y hFlipACEdge hFlipBCEdge
    have hAC : (x, z) ∈ G.ac :=
      (mem_flipBipartiteGraph G.ac x z).mp hFlipACEdge
    have hBC : (y, z) ∈ G.bc :=
      (mem_flipBipartiteGraph G.bc y z).mp hFlipBCEdge
    exact actual_C_cross_neighbor_labels_eq
      hH hUniform hab hac hbc hAC hBC
  have hPair := paired_left_degrees_one_of_cross_eq
    (flipBipartiteGraph G.ac) (flipBipartiteGraph G.bc)
    A B z hFlipAC hFlipBC hCross
  rw [flip_bipLeftDegree, flip_bipLeftDegree] at hPair
  exact hPair

/-- §II.A.1's mixed-node graph property for the graph formed from
    the actual triple system. -/
theorem actualLocalTripartite_mixed_degree_two
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    MixedNodeDegreeTwo (actualLocalTripartite H V a b c)
      (actualLocalPartA H V a b c)
      (actualLocalPartB H V a b c)
      (actualLocalPartC H V a b c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hAB hAC
    exact actual_A_mixed_degrees_one hH hUniform hab hac hbc hAB hAC
  · intro y hy hAB hBC
    exact actual_B_mixed_degrees_one hH hUniform hab hac hbc hAB hBC
  · intro z hz hAC hBC
    exact actual_C_mixed_degrees_one hH hUniform hab hac hbc hAC hBC

/-- Inequality (II.A.2) on the genuine graph attached to any triple of an
admissible rank-three family.  The full finite graph theorem supplies
the payment after the mixed-node property is derived from admissibility. -/
theorem actual_local_payment
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    TripartiteLocalPayment
      (actualLocalTripartite H V a b c)
      (actualLocalPartA H V a b c)
      (actualLocalPartB H V a b c)
      (actualLocalPartC H V a b c) :=
  tripartite_local_payment
    (actualLocalTripartite H V a b c)
    (actualLocalPartA H V a b c)
    (actualLocalPartB H V a b c)
    (actualLocalPartC H V a b c)
    (actualLocalTripartite_mixed_degree_two
      hH hUniform hab hac hbc)

/-- The pure-node branch of §II.A.4 applies directly to the graph
formed from actual triples.  The three hypotheses state that no tagged
node meets both other parts. -/
theorem actual_pure_local_payment
    (H : Family α) (V : Edge α) (a b c : α)
    (hPureA : ∀ x ∈ actualLocalPartA H V a b c,
      bipLeftDegree (actualLocalTripartite H V a b c).ab
          (actualLocalPartB H V a b c) x = 0 ∨
        bipLeftDegree (actualLocalTripartite H V a b c).ac
          (actualLocalPartC H V a b c) x = 0)
    (hPureB : ∀ y ∈ actualLocalPartB H V a b c,
      bipRightDegree (actualLocalTripartite H V a b c).ab
          (actualLocalPartA H V a b c) y = 0 ∨
        bipLeftDegree (actualLocalTripartite H V a b c).bc
          (actualLocalPartC H V a b c) y = 0)
    (hPureC : ∀ z ∈ actualLocalPartC H V a b c,
      bipRightDegree (actualLocalTripartite H V a b c).ac
          (actualLocalPartA H V a b c) z = 0 ∨
        bipRightDegree (actualLocalTripartite H V a b c).bc
          (actualLocalPartB H V a b c) z = 0) :
    localGraphBudget (actualLocalPartA H V a b c).card +
        localGraphBudget (actualLocalPartB H V a b c).card +
        localGraphBudget (actualLocalPartC H V a b c).card ≤
      localGraphPayment
        (actualLocalPartA H V a b c).card
        (actualLocalPartB H V a b c).card
        (actualLocalPartC H V a b c).card
        (bipartitePhiTotal (actualLocalTripartite H V a b c).ab
          (actualLocalPartA H V a b c)
          (actualLocalPartB H V a b c))
        (bipartitePhiTotal (actualLocalTripartite H V a b c).ac
          (actualLocalPartA H V a b c)
          (actualLocalPartC H V a b c))
        (bipartitePhiTotal (actualLocalTripartite H V a b c).bc
          (actualLocalPartB H V a b c)
          (actualLocalPartC H V a b c)) := by
  exact pure_tripartite_local_payment
    (actualLocalTripartite H V a b c)
    (actualLocalPartA H V a b c)
    (actualLocalPartB H V a b c)
    (actualLocalPartC H V a b c)
    hPureA hPureB hPureC

/-- The positive `AB` pair-type case of the local payment theorem now
    applies to the genuine graph of an admissible triple system. -/
theorem actual_positive_ab_local_payment
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hPositive :
      localGraphBudget (actualLocalPartA H V a b c).card +
          localGraphBudget (actualLocalPartB H V a b c).card <
        bipartitePhiTotal (actualLocalTripartite H V a b c).ab
          (actualLocalPartA H V a b c)
          (actualLocalPartB H V a b c)) :
    localGraphBudget (actualLocalPartA H V a b c).card +
        localGraphBudget (actualLocalPartB H V a b c).card +
        localGraphBudget (actualLocalPartC H V a b c).card ≤
      localGraphPayment
        (actualLocalPartA H V a b c).card
        (actualLocalPartB H V a b c).card
        (actualLocalPartC H V a b c).card
        (bipartitePhiTotal (actualLocalTripartite H V a b c).ab
          (actualLocalPartA H V a b c)
          (actualLocalPartB H V a b c))
        (bipartitePhiTotal (actualLocalTripartite H V a b c).ac
          (actualLocalPartA H V a b c)
          (actualLocalPartC H V a b c))
        (bipartitePhiTotal (actualLocalTripartite H V a b c).bc
          (actualLocalPartB H V a b c)
          (actualLocalPartC H V a b c)) := by
  exact positive_ab_local_payment
    (actualLocalTripartite H V a b c)
    (actualLocalPartA H V a b c)
    (actualLocalPartB H V a b c)
    (actualLocalPartC H V a b c)
    (actualLocalTripartite_mixed_degree_two hH hUniform hab hac hbc)
    hPositive

/-- At an `A_x` node, the rooted common neighbors of `a,x` at root `c`
    are the central vertex `b` together with its actual `AB` neighbors. -/
theorem actual_AB_left_common_neighbors
    {H : Family α} {V : Edge α} {a b c x : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hxA : x ∈ actualLocalPartA H V a b c) :
    rootCommonNeighbors H V c a x =
      insert b ((actualLocalPartB H V a b c).filter fun y =>
        (x, y) ∈ (actualLocalTripartite H V a b c).ab) := by
  obtain ⟨_, _, hxb, hxc, hBCX⟩ := mem_actualLocalPartA.mp hxA
  have hbV : b ∈ V := hground _ hE (by simp)
  have hbRoot : b ∈ rootCommonNeighbors H V c a x := by
    apply Finset.mem_filter.mpr
    refine ⟨hbV, hbc, Ne.symm hab, Ne.symm hxb, ?_, ?_⟩
    · have hEq : ({a, b} : Edge α) ∪ {c} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
    · have hEq : ({x, b} : Edge α) ∪ {c} =
          ({b, c, x} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hBCX
  ext t
  constructor
  · intro htRoot
    by_cases htb : t = b
    · subst t
      exact Finset.mem_insert_self b _
    · obtain ⟨htV, htc, hta, htx, hACT, hXCT⟩ :=
        Finset.mem_filter.mp htRoot
      have hACY : ({a, c, t} : Edge α) ∈ H := by
        have hEq : ({a, t} : Edge α) ∪ {c} =
            ({a, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hACT
      have hCXT : ({c, x, t} : Edge α) ∈ H := by
        have hEq : ({x, t} : Edge α) ∪ {c} =
            ({c, x, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hXCT
      have htB : t ∈ actualLocalPartB H V a b c :=
        mem_actualLocalPartB.mpr ⟨htV, hta, htb, htc, hACY⟩
      have hAB : (x, t) ∈ (actualLocalTripartite H V a b c).ab :=
        mem_actualLocalAB.mpr ⟨hxA, htB, hCXT⟩
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨htB, hAB⟩))
  · intro ht
    rcases Finset.mem_insert.mp ht with htb | htTail
    · exact htb ▸ hbRoot
    · obtain ⟨htB, hAB⟩ := Finset.mem_filter.mp htTail
      obtain ⟨htV, hta, _, htc, hACT⟩ := mem_actualLocalPartB.mp htB
      have hCXT : ({c, x, t} : Edge α) ∈ H :=
        (mem_actualLocalAB.mp hAB).2.2
      have hxt : x ≠ t :=
        outer_vertices_distinct_of_triple hUniform hCXT hxc.symm
      apply Finset.mem_filter.mpr
      refine ⟨htV, htc, hta, hxt.symm, ?_, ?_⟩
      · have hEq : ({a, t} : Edge α) ∪ {c} =
            ({a, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hACT
      · have hEq : ({x, t} : Edge α) ∪ {c} =
            ({c, x, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hCXT

/-- At a `B_y` node, the rooted common neighbors of `b,y` at root `c`
    are the central vertex `a` together with its actual `AB` neighbors. -/
theorem actual_AB_right_common_neighbors
    {H : Family α} {V : Edge α} {a b c y : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hyB : y ∈ actualLocalPartB H V a b c) :
    rootCommonNeighbors H V c b y =
      insert a ((actualLocalPartA H V a b c).filter fun x =>
        (x, y) ∈ (actualLocalTripartite H V a b c).ab) := by
  obtain ⟨_, hya, _, hyc, hACY⟩ := mem_actualLocalPartB.mp hyB
  have haV : a ∈ V := hground _ hE (by simp)
  have haRoot : a ∈ rootCommonNeighbors H V c b y := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, hac, hab, Ne.symm hya, ?_, ?_⟩
    · have hEq : ({b, a} : Edge α) ∪ {c} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
    · have hEq : ({y, a} : Edge α) ∪ {c} =
          ({a, c, y} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hACY
  ext t
  constructor
  · intro htRoot
    by_cases hta : t = a
    · subst t
      exact Finset.mem_insert_self a _
    · obtain ⟨htV, htc, htb, hty, hBCT, hYCT⟩ :=
        Finset.mem_filter.mp htRoot
      have hBCX : ({b, c, t} : Edge α) ∈ H := by
        have hEq : ({b, t} : Edge α) ∪ {c} =
            ({b, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hBCT
      have hCXT : ({c, t, y} : Edge α) ∈ H := by
        have hEq : ({y, t} : Edge α) ∪ {c} =
            ({c, t, y} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq ▸ hYCT
      have htA : t ∈ actualLocalPartA H V a b c :=
        mem_actualLocalPartA.mpr ⟨htV, hta, htb, htc, hBCX⟩
      have hAB : (t, y) ∈ (actualLocalTripartite H V a b c).ab :=
        mem_actualLocalAB.mpr ⟨htA, hyB, hCXT⟩
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨htA, hAB⟩))
  · intro ht
    rcases Finset.mem_insert.mp ht with hta | htTail
    · exact hta ▸ haRoot
    · obtain ⟨htA, hAB⟩ := Finset.mem_filter.mp htTail
      obtain ⟨htV, _, htb, htc, hBCT⟩ := mem_actualLocalPartA.mp htA
      have hCTY : ({c, t, y} : Edge α) ∈ H :=
        (mem_actualLocalAB.mp hAB).2.2
      have hty : t ≠ y :=
        outer_vertices_distinct_of_triple hUniform hCTY (Ne.symm htc)
      apply Finset.mem_filter.mpr
      refine ⟨htV, htc, htb, hty, ?_, ?_⟩
      · have hEq : ({b, t} : Edge α) ∪ {c} =
            ({b, c, t} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hBCT
      · have hEq : ({y, t} : Edge α) ∪ {c} =
            ({c, t, y} : Edge α) := by
          ext w
          simp only [Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          tauto
        exact hEq.symm ▸ hCTY

theorem actual_AB_left_common_neighbor_fraction
    {H : Family α} {V : Edge α} {a b c x : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hxA : x ∈ actualLocalPartA H V a b c) :
    weightFraction (rootCommonNeighbors H V c a x).card =
      localPhi (bipLeftDegree
        (actualLocalTripartite H V a b c).ab
        (actualLocalPartB H V a b c) x) := by
  rw [actual_AB_left_common_neighbors hUniform hground hab hbc hE hxA]
  have hbNot : b ∉
      (actualLocalPartB H V a b c).filter
        (fun y => (x, y) ∈ (actualLocalTripartite H V a b c).ab) := by
    intro hb
    have hbPart := (Finset.mem_filter.mp hb).1
    obtain ⟨_, _, hbb, _, _⟩ := mem_actualLocalPartB.mp hbPart
    exact hbb rfl
  rw [Finset.card_insert_of_notMem hbNot]
  rfl

theorem actual_AB_right_common_neighbor_fraction
    {H : Family α} {V : Edge α} {a b c y : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H)
    (hyB : y ∈ actualLocalPartB H V a b c) :
    weightFraction (rootCommonNeighbors H V c b y).card =
      localPhi (bipRightDegree
        (actualLocalTripartite H V a b c).ab
        (actualLocalPartA H V a b c) y) := by
  rw [actual_AB_right_common_neighbors hUniform hground hab hac hE hyB]
  have haNot : a ∉
      (actualLocalPartA H V a b c).filter
        (fun x => (x, y) ∈ (actualLocalTripartite H V a b c).ab) := by
    intro ha
    have haPart := (Finset.mem_filter.mp ha).1
    obtain ⟨_, haa, _, _, _⟩ := mem_actualLocalPartA.mp haPart
    exact haa rfl
  rw [Finset.card_insert_of_notMem haNot]
  rfl

theorem actual_AB_left_root_neighbors_erase
    (H : Family α) (V : Edge α) (a b c : α) :
    (rootNeighbors H V c b).erase a =
      actualLocalPartA H V a b c := by
  change (completionVertices H V ({c, b} : Edge α)).erase a = _
  have hPair : ({c, b} : Edge α) = ({b, c} : Edge α) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
  exact (actualLocalPartA_eq_completionVertices_erase H V a b c).symm

theorem actual_AB_right_root_neighbors_erase
    (H : Family α) (V : Edge α) (a b c : α) :
    (rootNeighbors H V c a).erase b =
      actualLocalPartB H V a b c := by
  change (completionVertices H V ({c, a} : Edge α)).erase b = _
  have hPair : ({c, a} : Edge α) = ({a, c} : Edge α) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]
  exact (actualLocalPartB_eq_completionVertices_erase H V a b c).symm

theorem actual_AB_left_root_neighbors_card
    {H : Family α} {V : Edge α} {a b c : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    (rootNeighbors H V c b).card =
      (actualLocalPartA H V a b c).card + 1 := by
  have haV : a ∈ V := hground _ hE (by simp)
  have haRoot : a ∈ rootNeighbors H V c b := by
    apply Finset.mem_filter.mpr
    refine ⟨haV, ?_, ?_⟩
    · simp [hac, hab]
    · have hEq : ({c, b} : Edge α) ∪ {a} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
  have hCard := Finset.card_erase_add_one haRoot
  rw [actual_AB_left_root_neighbors_erase] at hCard
  exact hCard.symm

theorem actual_AB_right_root_neighbors_card
    {H : Family α} {V : Edge α} {a b c : α}
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    (rootNeighbors H V c a).card =
      (actualLocalPartB H V a b c).card + 1 := by
  have hbV : b ∈ V := hground _ hE (by simp)
  have hbRoot : b ∈ rootNeighbors H V c a := by
    apply Finset.mem_filter.mpr
    refine ⟨hbV, ?_, ?_⟩
    · simp [hab.symm, hbc]
    · have hEq : ({c, a} : Edge α) ∪ {b} =
          ({a, b, c} : Edge α) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      exact hEq.symm ▸ hE
  have hCard := Finset.card_erase_add_one hbRoot
  rw [actual_AB_right_root_neighbors_erase] at hCard
  exact hCard.symm

/-- §II.A.1 for the root `c`: the actual signed weight of the
    central link edge `{a,b}` is exactly the `AB` graph score minus the
    two actual part budgets. -/
theorem actual_AB_signed_weight_eq_graph_score
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    rootedSignedWeight H V c a b =
      bipartitePhiTotal (actualLocalTripartite H V a b c).ab
        (actualLocalPartA H V a b c)
        (actualLocalPartB H V a b c) -
      localGraphBudget (actualLocalPartA H V a b c).card -
      localGraphBudget (actualLocalPartB H V a b c).card := by
  let A := actualLocalPartA H V a b c
  let B := actualLocalPartB H V a b c
  let G := actualLocalTripartite H V a b c
  have hLeftSum :
      (∑ x ∈ A,
        weightFraction (rootCommonNeighbors H V c a x).card) =
      ∑ x ∈ A, localPhi (bipLeftDegree G.ab B x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact actual_AB_left_common_neighbor_fraction
      hUniform hground hab hbc hE hx
  have hRightSum :
      (∑ y ∈ B,
        weightFraction (rootCommonNeighbors H V c b y).card) =
      ∑ y ∈ B, localPhi (bipRightDegree G.ab A y) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact actual_AB_right_common_neighbor_fraction
      hUniform hground hab hac hE hy
  have hBudgetA : weightPairBudget (rootNeighbors H V c b).card =
      localGraphBudget A.card := by
    rw [actual_AB_left_root_neighbors_card hground hab hac hE]
    exact (localGraphBudget_eq_shifted_pairBudget A.card).symm
  have hBudgetB : weightPairBudget (rootNeighbors H V c a).card =
      localGraphBudget B.card := by
    rw [actual_AB_right_root_neighbors_card hground hab hbc hE]
    exact (localGraphBudget_eq_shifted_pairBudget B.card).symm
  unfold rootedSignedWeight bipartitePhiTotal
  rw [actual_AB_left_root_neighbors_erase,
    actual_AB_right_root_neighbors_erase,
    hLeftSum, hRightSum, hBudgetA, hBudgetB]
  ring

private theorem actualPartA_swap_bc
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartA H V a c b = actualLocalPartA H V a b c := by
  rw [actualLocalPartA_eq_completionVertices_erase,
    actualLocalPartA_eq_completionVertices_erase]
  have hPair : ({c, b} : Edge α) = ({b, c} : Edge α) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]

private theorem actualPartB_acb_eq_C
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartB H V a c b = actualLocalPartC H V a b c := by
  rw [actualLocalPartB_eq_completionVertices_erase,
    actualLocalPartC_eq_completionVertices_erase]

private theorem actualGraphAB_acb_eq_AC
    (H : Family α) (V : Edge α) (a b c : α) :
    (actualLocalTripartite H V a c b).ab =
      (actualLocalTripartite H V a b c).ac := by
  ext p
  rcases p with ⟨x, z⟩
  rw [mem_actualLocalAB, mem_actualLocalAC,
    actualPartA_swap_bc H V a b c,
    actualPartB_acb_eq_C H V a b c]

private theorem actualPartA_bca_eq_B
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartA H V b c a = actualLocalPartB H V a b c := by
  rw [actualLocalPartA_eq_completionVertices_erase,
    actualLocalPartB_eq_completionVertices_erase]
  have hPair : ({c, a} : Edge α) = ({a, c} : Edge α) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]

private theorem actualPartB_bca_eq_C
    (H : Family α) (V : Edge α) (a b c : α) :
    actualLocalPartB H V b c a = actualLocalPartC H V a b c := by
  rw [actualLocalPartB_eq_completionVertices_erase,
    actualLocalPartC_eq_completionVertices_erase]
  have hPair : ({b, a} : Edge α) = ({a, b} : Edge α) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hPair]

private theorem actualGraphAB_bca_eq_BC
    (H : Family α) (V : Edge α) (a b c : α) :
    (actualLocalTripartite H V b c a).ab =
      (actualLocalTripartite H V a b c).bc := by
  ext p
  rcases p with ⟨y, z⟩
  rw [mem_actualLocalAB, mem_actualLocalBC,
    actualPartA_bca_eq_B H V a b c,
    actualPartB_bca_eq_C H V a b c]

/-- §II.A.1 for the root `b`, corresponding to the `AC` type. -/
theorem actual_AC_signed_weight_eq_graph_score
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    rootedSignedWeight H V b a c =
      bipartitePhiTotal (actualLocalTripartite H V a b c).ac
        (actualLocalPartA H V a b c)
        (actualLocalPartC H V a b c) -
      localGraphBudget (actualLocalPartA H V a b c).card -
      localGraphBudget (actualLocalPartC H V a b c).card := by
  have hPerm : ({a, c, b} : Edge α) ∈ H := by
    have hEq : ({a, c, b} : Edge α) = ({a, b, c} : Edge α) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hE
  have hAB := actual_AB_signed_weight_eq_graph_score
    hUniform hground hac hab hbc.symm hPerm
  rw [actualPartA_swap_bc H V a b c,
    actualPartB_acb_eq_C H V a b c,
    actualGraphAB_acb_eq_AC H V a b c] at hAB
  exact hAB

/-- §II.A.1 for the root `a`, corresponding to the `BC` type. -/
theorem actual_BC_signed_weight_eq_graph_score
    {H : Family α} {V : Edge α} {a b c : α}
    (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    rootedSignedWeight H V a b c =
      bipartitePhiTotal (actualLocalTripartite H V a b c).bc
        (actualLocalPartB H V a b c)
        (actualLocalPartC H V a b c) -
      localGraphBudget (actualLocalPartB H V a b c).card -
      localGraphBudget (actualLocalPartC H V a b c).card := by
  have hPerm : ({b, c, a} : Edge α) ∈ H := by
    have hEq : ({b, c, a} : Edge α) = ({a, b, c} : Edge α) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact hEq.symm ▸ hE
  have hAB := actual_AB_signed_weight_eq_graph_score
    hUniform hground hbc hab.symm hac.symm hPerm
  rw [actualPartA_bca_eq_B H V a b c,
    actualPartB_bca_eq_C H V a b c,
    actualGraphAB_bca_eq_BC H V a b c] at hAB
  exact hAB

/-- The complete graph theorem and the three exact score identities give
the original three-root negative-weight payment for every admissible
triple.  The remaining comparison with `localSignedDefect` is a finite
orientation and pair-budget normalization. -/
theorem actual_three_root_negative_payment
    {H : Family α} {V : Edge α} {a b c : α}
    (hH : Admissible H) (hUniform : Uniform 3 H)
    (hground : ∀ E ∈ H, E ⊆ V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hE : ({a, b, c} : Edge α) ∈ H) :
    localGraphBudget (actualLocalPartA H V a b c).card +
        localGraphBudget (actualLocalPartB H V a b c).card +
        localGraphBudget (actualLocalPartC H V a b c).card ≤
      negativeRootedWeight H V c a b +
        negativeRootedWeight H V b a c +
        negativeRootedWeight H V a b c := by
  have hPay := actual_local_payment
    (V := V) (a := a) (b := b) (c := c)
    hH hUniform hab hac hbc
  have hAB := actual_AB_signed_weight_eq_graph_score
    hUniform hground hab hac hbc hE
  have hAC := actual_AC_signed_weight_eq_graph_score
    hUniform hground hab hac hbc hE
  have hBC := actual_BC_signed_weight_eq_graph_score
    hUniform hground hab hac hbc hE
  unfold TripartiteLocalPayment localGraphPayment at hPay
  unfold negativeRootedWeight
  rw [hAB, hAC, hBC]
  convert hPay using 1
  ring_nf

end ActualTripartite

end JSP523.Rank3
