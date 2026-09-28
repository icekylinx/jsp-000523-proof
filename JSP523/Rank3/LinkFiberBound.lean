import JSP523.Rank3.PairGraphClassification
import Lean.Elab.Tactic.Omega

/-!
# A two-vertex bound on fibers of an actual common link

The signed-payment argument repeatedly uses the fact that an admissible
common link is intersecting.  Once a pair `p` avoids a vertex `z`, every
other link pair of the form `{z,t}` must meet `p` at `t`.  This packages the
local obstruction without assuming anything about degrees or a star center.
-/

namespace JSP523.Rank3

section LinkFiberBound

variable {α : Type*} [DecidableEq α]

/-- Vertices `t` for which `{z,t}` is a base pair in the common link of `q`. -/
def commonLinkFiber (H : Family α) (V q : Edge α) (z : α) : Edge α :=
  V.filter (fun t => ({z, t} : Edge α) ∈ commonLink H V q)

/-- Intersectingness forces every such `t` into any fixed link pair avoiding
    `z`.  The pair `p` need not itself be a star center certificate. -/
theorem common_link_fiber_subset_pair
    {H : Family α} {V q p : Edge α} {z : α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ commonLink H V q)
    (hzp : z ∉ p) :
    commonLinkFiber H V q z ⊆ p := by
  intro t ht
  have hzt : ({z, t} : Edge α) ∈ commonLink H V q :=
    (Finset.mem_filter.mp ht).2
  have hmeet : ¬ Disjoint p ({z, t} : Edge α) :=
    common_link_intersecting_of_ground_cell hH hq hp hzt
  by_contra htp
  apply hmeet
  apply Finset.disjoint_left.mpr
  intro x hx hxzt
  rcases Finset.mem_insert.mp hxzt with hzx | hxt
  · exact hzp (hzx ▸ hx)
  · exact htp ((Finset.mem_singleton.mp hxt) ▸ hx)

/-- The fiber has at most two vertices because its containing link edge is
    a genuine pair. -/
theorem common_link_fiber_card_le_two
    {H : Family α} {V q p : Edge α} {z : α}
    (hH : Admissible H)
    (hq : q ∈ V.powersetCard 2)
    (hp : p ∈ commonLink H V q)
    (hzp : z ∉ p) :
    (commonLinkFiber H V q z).card ≤ 2 := by
  have hsub := common_link_fiber_subset_pair hH hq hp hzp
  have hp2 : p.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  exact (Finset.card_le_card hsub).trans_eq hp2

/-- Two base pairs `{x,y}` and `{x,u}` in the cell `{z,v}` produce the
    reciprocal base pair `{v,x}` in the cell `{y,u}`.  This is the concrete
    first half of the manuscript's reciprocal grouping, and requires no
    admissibility assumption. -/
theorem reciprocal_pair_in_common_link
    (H : Family α) (V : Edge α)
    {z v x y u : α}
    (hvV : v ∈ V)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V z v) :
    ({v, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) := by
  obtain ⟨hxyV, hxyOut, _, hxyv⟩ := Finset.mem_filter.mp hxyLink
  obtain ⟨_, hxuOut, _, hxuv⟩ := Finset.mem_filter.mp hxuLink
  have hxV : x ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
  have hvNotXY : v ∉ ({x, y} : Edge α) := by
    intro hv
    exact (Finset.disjoint_left.mp hxyOut) hv (by simp)
  have hvNotXU : v ∉ ({x, u} : Edge α) := by
    intro hv
    exact (Finset.disjoint_left.mp hxuOut) hv (by simp)
  have hvx : v ≠ x := by
    intro h
    exact hvNotXY (by simp [h])
  have hvy : v ≠ y := by
    intro h
    exact hvNotXY (by simp [h])
  have hvu : v ≠ u := by
    intro h
    exact hvNotXU (by simp [h])
  have hpV : ({v, x} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' : w = v ∨ w = x := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
      rcases hw' with rfl | rfl
      · exact hvV
      · exact hxV
    · exact Finset.card_pair hvx
  have hpOut : Disjoint ({v, x} : Edge α) ({y, u} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro w hw hcell
    have hw' : w = v ∨ w = x := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    have hcell' : w = y ∨ w = u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcell
    rcases hw' with hwv | hwx
    · rcases hcell' with hwy | hwu
      · exact hvy (hwv.symm.trans hwy)
      · exact hvu (hwv.symm.trans hwu)
    · rcases hcell' with hwy | hwu
      · exact hxy (hwx.symm.trans hwy)
      · exact hxu (hwx.symm.trans hwu)
  have hpy : ({v, x} : Edge α) ∪ {y} ∈ H := by
    have heq : ({v, x} : Edge α) ∪ {y} =
        ({x, y} : Edge α) ∪ {v} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hxyv
  have hpu : ({v, x} : Edge α) ∪ {u} ∈ H := by
    have heq : ({v, x} : Edge α) ∪ {u} =
        ({x, u} : Edge α) ∪ {v} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ hxuv
  have hpOrient : ({v, x} : Edge α) ∈ orientedCommonLink H V y u :=
    Finset.mem_filter.mpr ⟨hpV, hpOut, hpy, hpu⟩
  exact (mem_common_link_pair_iff_oriented H V hyu _).mpr hpOrient

/-- Common neighbors of `y,u` in the graph link at `z`, with all vertices
    required to be distinct where the three-uniform interpretation needs it. -/
def rootCommonNeighbors
    (H : Family α) (V : Edge α) (z y u : α) : Edge α :=
  V.filter (fun t => t ≠ z ∧ t ≠ y ∧ t ≠ u ∧
    ({y, t} : Edge α) ∪ {z} ∈ H ∧
    ({u, t} : Edge α) ∪ {z} ∈ H)

/-- Every rooted common neighbor gives a base pair `{z,t}` in the reciprocal
    common link of the cell `{y,u}`. -/
theorem root_common_neighbors_subset_common_link_fiber
    (H : Family α) (V : Edge α)
    {z y u : α}
    (hzV : z ∈ V) (hzy : z ≠ y) (hzu : z ≠ u) (hyu : y ≠ u) :
    rootCommonNeighbors H V z y u ⊆
      commonLinkFiber H V ({y, u} : Edge α) z := by
  intro t ht
  obtain ⟨htV, htz, hty, htu, htyz, htuz⟩ := Finset.mem_filter.mp ht
  have hztV : ({z, t} : Edge α) ∈ V.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' : w = z ∨ w = t := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
      rcases hw' with rfl | rfl
      · exact hzV
      · exact htV
    · exact Finset.card_pair (Ne.symm htz)
  have hdis : Disjoint ({z, t} : Edge α) ({y, u} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro w hw hcell
    have hw' : w = z ∨ w = t := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    have hcell' : w = y ∨ w = u := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcell
    rcases hw' with hwz | hwt
    · rcases hcell' with hwy | hwu
      · exact hzy (hwz.symm.trans hwy)
      · exact hzu (hwz.symm.trans hwu)
    · rcases hcell' with hwy | hwu
      · exact hty (hwt.symm.trans hwy)
      · exact htu (hwt.symm.trans hwu)
  have hzyEdge : ({z, t} : Edge α) ∪ {y} ∈ H := by
    have heq : ({z, t} : Edge α) ∪ {y} =
        ({y, t} : Edge α) ∪ {z} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ htyz
  have hzuEdge : ({z, t} : Edge α) ∪ {u} ∈ H := by
    have heq : ({z, t} : Edge α) ∪ {u} =
        ({u, t} : Edge α) ∪ {z} := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    exact heq.symm ▸ htuz
  have hOrient : ({z, t} : Edge α) ∈ orientedCommonLink H V y u :=
    Finset.mem_filter.mpr ⟨hztV, hdis, hzyEdge, hzuEdge⟩
  exact Finset.mem_filter.mpr
    ⟨htV, (mem_common_link_pair_iff_oriented H V hyu _).mpr hOrient⟩

/-- The local weak-alternative obstruction from §4 of the rank-three
    manuscript: two common-link base pairs sharing `x` force the rooted
    common-neighbor count of their other endpoints to be at most two. -/
theorem root_common_neighbors_card_le_two_of_two_book_pairs
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (hxyLink : ({x, y} : Edge α) ∈ orientedCommonLink H V z v)
    (hxuLink : ({x, u} : Edge α) ∈ orientedCommonLink H V z v) :
    (rootCommonNeighbors H V z y u).card ≤ 2 := by
  have hrecip : ({v, x} : Edge α) ∈ commonLink H V ({y, u} : Edge α) :=
    reciprocal_pair_in_common_link H V hvV hxy hxu hyu hxyLink hxuLink
  obtain ⟨_, hxyOut, _, _⟩ := Finset.mem_filter.mp hxyLink
  obtain ⟨_, hxuOut, _, _⟩ := Finset.mem_filter.mp hxuLink
  have hzNotXY : z ∉ ({x, y} : Edge α) := by
    intro hz
    exact (Finset.disjoint_left.mp hxyOut) hz (by simp)
  have hzNotXU : z ∉ ({x, u} : Edge α) := by
    intro hz
    exact (Finset.disjoint_left.mp hxuOut) hz (by simp)
  have hzx : z ≠ x := by
    intro h
    exact hzNotXY (by simp [h])
  have hzy : z ≠ y := by
    intro h
    exact hzNotXY (by simp [h])
  have hzu : z ≠ u := by
    intro h
    exact hzNotXU (by simp [h])
  have hzNotVX : z ∉ ({v, x} : Edge α) := by
    simp [hzv, hzx]
  have hcell : ({y, u} : Edge α) ∈ V.powersetCard 2 := by
    have hxyV : ({x, y} : Edge α) ∈ V.powersetCard 2 :=
      (Finset.mem_filter.mp hxyLink).1
    have hxuV : ({x, u} : Edge α) ∈ V.powersetCard 2 :=
      (Finset.mem_filter.mp hxuLink).1
    have hyV : y ∈ V := (Finset.mem_powersetCard.mp hxyV).1 (by simp)
    have huV : u ∈ V := (Finset.mem_powersetCard.mp hxuV).1 (by simp)
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      have hw' : w = y ∨ w = u := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
      rcases hw' with rfl | rfl
      · exact hyV
      · exact huV
    · exact Finset.card_pair hyu
  have hfiber : (commonLinkFiber H V ({y, u} : Edge α) z).card ≤ 2 :=
    common_link_fiber_card_le_two hH hcell hrecip hzNotVX
  exact (Finset.card_le_card
    (root_common_neighbors_subset_common_link_fiber H V hzV hzy hzu hyu)).trans hfiber

end LinkFiberBound

end JSP523.Rank3
