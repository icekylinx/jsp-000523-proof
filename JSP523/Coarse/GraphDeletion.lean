import JSP523.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Powerset

/-!
# The finite graph deletion lemma from Part I

The manuscript calls an unordered pair a *diagonal* when its vertices have
at least two common neighbors.  A finite graph has no four-cycle exactly
when it has no diagonals.  This module uses `Sym2` for unordered pairs, so
each diagonal is counted once, as in Lemma I.2.
-/

namespace JSP523.Coarse

open Finset
open scoped Sym2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of common neighbors of two vertices in a finite graph. -/
def graphCodegree (G : SimpleGraph α) [DecidableRel G.Adj]
    (x y : α) : ℕ :=
  (G.neighborFinset x ∩ G.neighborFinset y).card

theorem graph_codegree_comm (G : SimpleGraph α) [DecidableRel G.Adj]
    (x y : α) : graphCodegree G x y = graphCodegree G y x := by
  simp [graphCodegree, Finset.inter_comm]

theorem two_le_graph_codegree_of_common
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x y u v : α} (huv : u ≠ v)
    (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) :
    2 ≤ graphCodegree G x y := by
  have hsub : ({u, v} : Finset α) ⊆
      G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [SimpleGraph.mem_neighborFinset, hxu, hyu]
    · simp [SimpleGraph.mem_neighborFinset, hxv, hyv]
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_pair huv, graphCodegree] using hcard

theorem graph_codegree_mono {G H : SimpleGraph α}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (x y : α) :
    graphCodegree G x y ≤ graphCodegree H x y := by
  unfold graphCodegree
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz ⊢
  exact ⟨hGH hz.1, hGH hz.2⟩

/-- The unordered pairs with at least two common neighbors. -/
def graphDiagonals (G : SimpleGraph α) [DecidableRel G.Adj] :
    Finset (Sym2 α) :=
  Finset.univ.filter fun p =>
    ∃ x y : α, x ≠ y ∧ p = s(x, y) ∧ 2 ≤ graphCodegree G x y

theorem mem_graph_diagonals_iff (G : SimpleGraph α) [DecidableRel G.Adj]
    {x y : α} (hxy : x ≠ y) :
    s(x, y) ∈ graphDiagonals G ↔
      2 ≤ graphCodegree G x y := by
  classical
  constructor
  · intro h
    obtain ⟨a, b, hab, heq, hcodeg⟩ :=
      (Finset.mem_filter.mp h).2
    have hab' : s(a, b) = s(x, y) := heq.symm
    rcases Sym2.eq_iff.mp hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcodeg
    · simpa only [graph_codegree_comm] using hcodeg
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨x, y, hxy, rfl, h⟩⟩

theorem graph_diagonals_mono {G H : SimpleGraph α}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) : graphDiagonals G ⊆ graphDiagonals H := by
  intro p hp
  obtain ⟨x, y, hxy, rfl, htwo⟩ := (Finset.mem_filter.mp hp).2
  exact (mem_graph_diagonals_iff H hxy).2
    (htwo.trans (graph_codegree_mono hGH x y))

theorem not_mem_graph_diagonals_self (G : SimpleGraph α)
    [DecidableRel G.Adj] (x : α) :
    s(x, x) ∉ graphDiagonals G := by
  intro h
  obtain ⟨a, b, hab, heq, _⟩ := (Finset.mem_filter.mp h).2
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hab rfl
  · exact hab rfl

/-- For an oriented edge `uv`, these are the neighbors `x` of `v` for
which `ux` is a diagonal, as in the first set in Lemma I.2. -/
def graphDeleteSide (G : SimpleGraph α) [DecidableRel G.Adj]
    (u v : α) : Finset α :=
  (G.neighborFinset v).filter fun x => s(u, x) ∈ graphDiagonals G

theorem mem_graph_delete_side_iff (G : SimpleGraph α) [DecidableRel G.Adj]
    {u v x : α} :
    x ∈ graphDeleteSide G u v ↔
      G.Adj v x ∧ s(u, x) ∈ graphDiagonals G := by
  simp [graphDeleteSide, SimpleGraph.mem_neighborFinset]

theorem graph_delete_side_ne_left (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v x : α}
    (hx : x ∈ graphDeleteSide G u v) : x ≠ u := by
  intro h
  subst x
  have hdiag := (mem_graph_delete_side_iff G).mp hx |>.2
  exact (not_mem_graph_diagonals_self G u) hdiag

theorem graph_delete_side_ne_right (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v x : α}
    (hx : x ∈ graphDeleteSide G u v) : x ≠ v := by
  intro h
  subst x
  exact G.irrefl ((mem_graph_delete_side_iff G).mp hx).1

/-- The batch of graph edges deleted at the `uv` step of Lemma I.2. -/
def graphDeleteBatch (G : SimpleGraph α) [DecidableRel G.Adj]
    (u v : α) : Finset (Sym2 α) :=
  (graphDeleteSide G u v).image (fun x => s(v, x)) ∪
    (graphDeleteSide G v u).image (fun y => s(u, y))

theorem graph_delete_batch_subset_edges (G : SimpleGraph α)
    [DecidableRel G.Adj] (u v : α) :
    graphDeleteBatch G u v ⊆ G.edgeFinset := by
  intro e he
  simp only [graphDeleteBatch, Finset.mem_union, Finset.mem_image] at he
  rcases he with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · exact (SimpleGraph.mem_edgeFinset.trans G.mem_edgeSet).2
      ((mem_graph_delete_side_iff G).mp hx).1
  · exact (SimpleGraph.mem_edgeFinset.trans G.mem_edgeSet).2
      ((mem_graph_delete_side_iff G).mp hy).1

theorem graph_delete_batch_kills_left (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v x : α}
    (huv : G.Adj u v) (hx : x ∈ graphDeleteSide G u v) :
    graphCodegree (G.deleteEdges (graphDeleteBatch G u v)) u x = 0 := by
  classical
  let R := graphDeleteBatch G u v
  let H := G.deleteEdges R
  apply Finset.card_eq_zero.mpr
  ext w
  constructor
  · intro hw
    have huw : H.Adj u w :=
      by simpa only [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_inter.mp hw).1
    have hxw : H.Adj x w :=
      by simpa only [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_inter.mp hw).2
    have hux : u ≠ x := (graph_delete_side_ne_left G hx).symm
    have hvx : G.Adj v x := ((mem_graph_delete_side_iff G).mp hx).1
    have hdelVX : s(v, x) ∈ R := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hwv : w ≠ v := by
      intro h
      subst w
      have hnot : s(x, v) ∉ R :=
        (SimpleGraph.deleteEdges_adj.mp hxw).2
      exact hnot (by simpa only [Sym2.eq_swap] using hdelVX)
    have hdiagVW : s(v, w) ∈ graphDiagonals G := by
      apply (mem_graph_diagonals_iff G hwv.symm).2
      apply two_le_graph_codegree_of_common G hux
      · exact huv.symm
      · exact (SimpleGraph.deleteEdges_adj.mp huw).1.symm
      · exact hvx
      · exact (SimpleGraph.deleteEdges_adj.mp hxw).1.symm
    have hY : w ∈ graphDeleteSide G v u :=
      (mem_graph_delete_side_iff G).2
        ⟨(SimpleGraph.deleteEdges_adj.mp huw).1, hdiagVW⟩
    have hdelUW : s(u, w) ∈ R := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨w, hY, rfl⟩
    exact False.elim ((SimpleGraph.deleteEdges_adj.mp huw).2 hdelUW)
  · simp

theorem graph_delete_batch_kills_right (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v y : α}
    (huv : G.Adj u v) (hy : y ∈ graphDeleteSide G v u) :
    graphCodegree (G.deleteEdges (graphDeleteBatch G u v)) v y = 0 := by
  have hswap : graphDeleteBatch G v u = graphDeleteBatch G u v := by
    simp only [graphDeleteBatch, Finset.union_comm]
  simpa only [hswap] using graph_delete_batch_kills_left G huv.symm hy

/-- The diagonals lost in the same batch of Lemma I.2. -/
def graphKilledDiagonals (G : SimpleGraph α) [DecidableRel G.Adj]
    (u v : α) : Finset (Sym2 α) :=
  (graphDeleteSide G u v).image (fun x => s(u, x)) ∪
    (graphDeleteSide G v u).image (fun y => s(v, y))

omit [Fintype α] [DecidableEq α] in
private theorem sym2_fixed_injective (a : α) :
    Function.Injective (fun x : α => s(a, x)) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with ⟨_, hxy⟩ | ⟨hay, hxa⟩
  · exact hxy
  · exact hxa.trans hay

omit [Fintype α] in
private theorem sym2_images_disjoint
    {X Y : Finset α} {a b : α} (hab : a ≠ b)
    (hX : ∀ x ∈ X, x ≠ b) :
    Disjoint (X.image (fun x => s(a, x)))
      (Y.image (fun y => s(b, y))) := by
  apply Finset.disjoint_left.mpr
  intro e heX heY
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp heX
  obtain ⟨y, hy, hEq⟩ := Finset.mem_image.mp heY
  rcases Sym2.eq_iff.mp hEq with ⟨h, _⟩ | ⟨h, _⟩
  · exact hab h.symm
  · exact hX x hx h.symm

theorem graph_delete_batch_card (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v : α} (huv : G.Adj u v) :
    (graphDeleteBatch G u v).card =
      (graphDeleteSide G u v).card +
        (graphDeleteSide G v u).card := by
  have huv' : v ≠ u := huv.ne.symm
  have hdisj : Disjoint
      ((graphDeleteSide G u v).image (fun x => s(v, x)))
      ((graphDeleteSide G v u).image (fun y => s(u, y))) :=
    sym2_images_disjoint huv'
      (fun x hx => graph_delete_side_ne_left G hx)
  unfold graphDeleteBatch
  rw [Finset.card_union_of_disjoint hdisj]
  simp only [Finset.card_image_of_injective _ (sym2_fixed_injective _)]

theorem graph_killed_diagonals_card (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v : α} (huv : G.Adj u v) :
    (graphKilledDiagonals G u v).card =
      (graphDeleteSide G u v).card +
        (graphDeleteSide G v u).card := by
  have hdisj : Disjoint
      ((graphDeleteSide G u v).image (fun x => s(u, x)))
      ((graphDeleteSide G v u).image (fun y => s(v, y))) :=
    sym2_images_disjoint huv.ne
      (fun x hx => graph_delete_side_ne_right G hx)
  unfold graphKilledDiagonals
  rw [Finset.card_union_of_disjoint hdisj]
  simp only [Finset.card_image_of_injective _ (sym2_fixed_injective _)]

theorem graph_killed_diagonals_subset_lost (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v : α} (huv : G.Adj u v) :
    graphKilledDiagonals G u v ⊆
      graphDiagonals G \
        graphDiagonals (G.deleteEdges (graphDeleteBatch G u v)) := by
  classical
  intro e he
  simp only [graphKilledDiagonals, Finset.mem_union,
    Finset.mem_image] at he
  rcases he with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · apply Finset.mem_sdiff.mpr
    constructor
    · exact ((mem_graph_delete_side_iff G).mp hx).2
    · intro h
      have htwo := (mem_graph_diagonals_iff
        (G.deleteEdges (graphDeleteBatch G u v))
          (graph_delete_side_ne_left G hx).symm).mp h
      rw [graph_delete_batch_kills_left G huv hx] at htwo
      omega
  · apply Finset.mem_sdiff.mpr
    constructor
    · exact ((mem_graph_delete_side_iff G).mp hy).2
    · intro h
      have htwo := (mem_graph_diagonals_iff
        (G.deleteEdges (graphDeleteBatch G u v))
          (graph_delete_side_ne_left G hy).symm).mp h
      rw [graph_delete_batch_kills_right G huv hy] at htwo
      omega

/-- Each edge in one deletion batch is paid for by a distinct diagonal
destroyed in that batch. -/
theorem graph_delete_batch_budget (G : SimpleGraph α)
    [DecidableRel G.Adj] {u v : α} (huv : G.Adj u v) :
    (graphDeleteBatch G u v).card +
      (graphDiagonals (G.deleteEdges (graphDeleteBatch G u v))).card ≤
        (graphDiagonals G).card := by
  classical
  let R := graphDeleteBatch G u v
  let H := G.deleteEdges R
  have hDH : graphDiagonals H ⊆ graphDiagonals G :=
    graph_diagonals_mono (G.deleteEdges_le R)
  have hQ : (graphKilledDiagonals G u v).card ≤
      (graphDiagonals G \ graphDiagonals H).card :=
    Finset.card_le_card (graph_killed_diagonals_subset_lost G huv)
  rw [graph_killed_diagonals_card G huv] at hQ
  rw [graph_delete_batch_card G huv]
  have hsplit := Finset.card_sdiff_add_card_eq_card hDH
  dsimp [H, R] at hQ hsplit
  omega

theorem graph_delete_batch_exists_of_diagonals
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hD : (graphDiagonals G).Nonempty) :
    ∃ u v : α, G.Adj u v ∧
      (graphDeleteBatch G u v).Nonempty := by
  obtain ⟨p, hp⟩ := hD
  obtain ⟨u, x, hux, rfl, htwo⟩ := (Finset.mem_filter.mp hp).2
  have hone : 1 < (G.neighborFinset u ∩ G.neighborFinset x).card := by
    dsimp [graphCodegree] at htwo
    omega
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp hone
  have huv : G.Adj u v := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hv).1
  have hxv : G.Adj x v := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hv).2
  have hside : x ∈ graphDeleteSide G u v :=
    (mem_graph_delete_side_iff G).2 ⟨hxv.symm,
      (mem_graph_diagonals_iff G hux).2 htwo⟩
  refine ⟨u, v, huv, s(v, x), ?_⟩
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨x, hside, rfl⟩)

/-- A finite graph has no four-cycle when every distinct vertex pair has at
most one common neighbor. -/
def FourCycleFree (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ x y : α, x ≠ y → graphCodegree G x y ≤ 1

theorem FourCycleFree.mono {G H : SimpleGraph α}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (hH : FourCycleFree H) :
    FourCycleFree G := by
  intro x y hxy
  exact (graph_codegree_mono hGH x y).trans (hH x y hxy)

theorem four_cycle_free_iff_diagonals_empty
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    FourCycleFree G ↔ graphDiagonals G = ∅ := by
  classical
  constructor
  · intro h
    ext p
    constructor
    · intro hp
      obtain ⟨x, y, hxy, rfl, htwo⟩ := (Finset.mem_filter.mp hp).2
      have hone := h x y hxy
      omega
    · simp
  · intro h x y hxy
    have hnot : s(x, y) ∉ graphDiagonals G := by simp [h]
    rw [mem_graph_diagonals_iff G hxy] at hnot
    omega

private theorem graph_deletion_aux :
    ∀ n : ℕ, ∀ (G : SimpleGraph α) [DecidableRel G.Adj],
      G.edgeFinset.card ≤ n →
        ∃ R : Finset (Sym2 α), R ⊆ G.edgeFinset ∧
          R.card ≤ (graphDiagonals G).card ∧
          FourCycleFree (G.deleteEdges R) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ hsize
    classical
    by_cases hD : graphDiagonals G = ∅
    · refine ⟨∅, by simp, by simp [hD], ?_⟩
      simpa only [Finset.coe_empty, SimpleGraph.deleteEdges_empty] using
        (four_cycle_free_iff_diagonals_empty G).2 hD
    · obtain ⟨u, v, huv, hRnon⟩ :=
        graph_delete_batch_exists_of_diagonals G
          (Finset.nonempty_of_ne_empty hD)
      let R₀ := graphDeleteBatch G u v
      let H := G.deleteEdges R₀
      have hRsub : R₀ ⊆ G.edgeFinset :=
        graph_delete_batch_subset_edges G u v
      have hRpos : 0 < R₀.card := Finset.card_pos.mpr hRnon
      have hRcard : R₀.card ≤ G.edgeFinset.card :=
        Finset.card_le_card hRsub
      have hlt : H.edgeFinset.card < G.edgeFinset.card := by
        dsimp [H]
        rw [SimpleGraph.edgeFinset_deleteEdges,
          Finset.card_sdiff_of_subset hRsub]
        omega
      obtain ⟨R₁, hR₁sub, hR₁bd, hfree⟩ :=
        ih H.edgeFinset.card (hlt.trans_le hsize) H le_rfl
      have hHedges : H.edgeFinset ⊆ G.edgeFinset :=
        SimpleGraph.edgeFinset_mono (G.deleteEdges_le R₀)
      have hR₁subG : R₁ ⊆ G.edgeFinset := hR₁sub.trans hHedges
      have hB : R₀.card + (graphDiagonals H).card ≤
          (graphDiagonals G).card :=
        graph_delete_batch_budget G huv
      refine ⟨R₀ ∪ R₁, Finset.union_subset hRsub hR₁subG, ?_, ?_⟩
      · have hUnion := Finset.card_union_le R₀ R₁
        omega
      · simpa only [H, SimpleGraph.deleteEdges_deleteEdges,
          Finset.coe_union] using hfree

/-- Lemma I.2: delete at most one graph edge per original unordered
diagonal to eliminate every four-cycle. -/
theorem graph_delete_four_cycles (G : SimpleGraph α)
    [DecidableRel G.Adj] :
    ∃ R : Finset (Sym2 α), R ⊆ G.edgeFinset ∧
      R.card ≤ (graphDiagonals G).card ∧
      FourCycleFree (G.deleteEdges R) := by
  exact graph_deletion_aux G.edgeFinset.card G le_rfl

end JSP523.Coarse
