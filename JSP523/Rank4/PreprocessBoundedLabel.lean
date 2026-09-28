import JSP523.Rank4.LocalDirtyPairGraph
import JSP523.Rank4.PreprocessCollisionMoment

/-!
# Fixed-center pair-node graph for bounded-label separation

At a fixed completion vertex x, the pair nodes are the roots P for which
the triple xP belongs to Q.  A proper coloring of this link makes each
color class a matching.  The graph below records actual disjoint four-edge
unions between two such color classes.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pair roots of the Q-link at a fixed vertex. -/
def fixedCenterPairNodes (Q : Family α) (V : Edge α) (x : α) : Type _ :=
  {P : Edge α // P ∈ (V.powersetCard 2).filter fun P => insert x P ∈ Q}

noncomputable instance fixedCenterPairNodesDecEq
    (Q : Family α) (V : Edge α) (x : α) :
    DecidableEq (fixedCenterPairNodes Q V x) := Classical.decEq _

noncomputable instance fixedCenterPairNodesFintype
    (Q : Family α) (V : Edge α) (x : α) :
    Fintype (fixedCenterPairNodes Q V x) := by
  classical
  exact Fintype.ofFinset
    ((V.powersetCard 2).filter fun P => insert x P ∈ Q) (fun _ => Iff.rfl)

noncomputable instance fixedCenterPairNodeColorClassFintype
    (Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i : ℕ) :
    Fintype {P : fixedCenterPairNodes Q V x // color P = i} :=
  Fintype.ofFinite _

noncomputable instance fixedCenterPairNodeColorClassDecEq
    (Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i : ℕ) :
    DecidableEq {P : fixedCenterPairNodes Q V x // color P = i} :=
  Classical.decEq _

/-- Adjacency in the pair-node union graph between colors `i` and `j`. -/
def fixedCenterPairNodeAdj (F : Family α) :
    Sum (Edge α) (Edge α) → Sum (Edge α) (Edge α) → Prop
  | Sum.inl P, Sum.inr Q => Disjoint P Q ∧ P ∪ Q ∈ F
  | Sum.inr Q, Sum.inl P => Disjoint Q P ∧ Q ∪ P ∈ F
  | _, _ => False

/-- The actual pair-node graph between two link-color classes. -/
def fixedCenterPairNodeGraph (F : Family α) (Q : Family α)
    (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i j : ℕ) :
    SimpleGraph (Sum
      {P : fixedCenterPairNodes Q V x // color P = i}
      {P : fixedCenterPairNodes Q V x // color P = j}) where
  Adj A B := match A, B with
    | Sum.inl P, Sum.inr R =>
        Disjoint P.1.1 R.1.1 ∧ P.1.1 ∪ R.1.1 ∈ F
    | Sum.inr R, Sum.inl P =>
        Disjoint R.1.1 P.1.1 ∧ R.1.1 ∪ P.1.1 ∈ F
    | _, _ => False
  symm.symm A B := by
    cases A with
    | inl P => cases B with
      | inl R => exact id
      | inr R => intro h; exact ⟨h.1.symm,
          by simpa [Finset.union_comm] using h.2⟩
    | inr R => cases B with
      | inl P => intro h; exact ⟨h.1.symm,
          by simpa [Finset.union_comm] using h.2⟩
      | inr S => exact id
  loopless.irrefl A := by
    cases A <;> simp

noncomputable instance fixedCenterPairNodeGraphDecidableRel
    (F Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i j : ℕ) :
    DecidableRel (fixedCenterPairNodeGraph F Q V x color i j).Adj := by
  classical
  intro A B
  cases A <;> cases B <;> infer_instance

omit [Fintype α] in
/-- A proper link coloring makes each color class a matching of actual pair
roots: distinct same-color nodes are disjoint. -/
theorem fixedCenter_color_class_matching
    (Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ)
    (hProper : ∀ P R : fixedCenterPairNodes Q V x,
      P.1 ≠ R.1 → ¬ Disjoint P.1 R.1 → color P ≠ color R)
    {i : ℕ} {P R : fixedCenterPairNodes Q V x}
    (hPi : color P = i) (hRi : color R = i) (hNe : P.1 ≠ R.1) :
    Disjoint P.1 R.1 := by
  by_contra hDisj
  exact hProper P R hNe hDisj (hPi.trans hRi.symm)

omit [Fintype α] in
/-- A rectangle between two pair-node color classes is an actual forbidden
two-versus-two trade. -/
theorem fixedCenter_pairNode_rectangle_forbidden
    (F Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i j : ℕ)
    (hProper : ∀ P R : fixedCenterPairNodes Q V x,
      P.1 ≠ R.1 → ¬ Disjoint P.1 R.1 → color P ≠ color R)
    (hAdmissible : Admissible F)
    (P R : {P : fixedCenterPairNodes Q V x // color P = i})
    (Q' S : {P : fixedCenterPairNodes Q V x // color P = j})
    (hPR : P.1.1 ≠ R.1.1) (hQS : Q'.1.1 ≠ S.1.1)
    (hPQ : Disjoint P.1.1 Q'.1.1) (hPS : Disjoint P.1.1 S.1.1)
    (hRQ : Disjoint R.1.1 Q'.1.1) (hRS : Disjoint R.1.1 S.1.1)
    (hEPQ : P.1.1 ∪ Q'.1.1 ∈ F)
    (hERS : R.1.1 ∪ S.1.1 ∈ F)
    (hEPS : P.1.1 ∪ S.1.1 ∈ F)
    (hERQ : R.1.1 ∪ Q'.1.1 ∈ F) : False := by
  have hPNe : P.1.1.Nonempty := by
    have hmem := (Finset.mem_filter.mp P.1.2).1
    have hcard := (Finset.mem_powersetCard.mp hmem).2
    exact Finset.card_pos.mp (by omega)
  have hPRdisj : Disjoint P.1.1 R.1.1 :=
    fixedCenter_color_class_matching Q V x color hProper
      (P := P.1) (R := R.1) P.2 R.2 hPR
  have hQSdisj : Disjoint Q'.1.1 S.1.1 :=
    fixedCenter_color_class_matching Q V x color hProper
      (P := Q'.1) (R := S.1) Q'.2 S.2 hQS
  exact disjoint_pair_cycle_forbidden hPNe hPR hQS hPRdisj hPQ hPS hRQ hRS hQSdisj
    hEPQ hERS hEPS hERQ hAdmissible

omit [Fintype α] in
/-- Every fixed pair of colors gives a C4-free pair-node graph. -/
theorem fixedCenterPairNodeGraph_fourCycleFree
    (F Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i j : ℕ)
    (hProper : ∀ P R : fixedCenterPairNodes Q V x,
      P.1 ≠ R.1 → ¬ Disjoint P.1 R.1 → color P ≠ color R)
    (hAdmissible : Admissible F) :
    JSP523.Coarse.FourCycleFree
      (fixedCenterPairNodeGraph F Q V x color i j) := by
  classical
  let G := fixedCenterPairNodeGraph F Q V x color i j
  intro A B hAB
  unfold JSP523.Coarse.graphCodegree
  apply Finset.card_le_one_iff.mpr
  intro C D hC hD
  by_contra hCD
  have hAC : G.Adj A C := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hC).1
  have hBC : G.Adj B C := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hC).2
  have hAD : G.Adj A D := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hD).1
  have hBD : G.Adj B D := by
    simpa only [SimpleGraph.mem_neighborFinset] using
      (Finset.mem_inter.mp hD).2
  cases A with
  | inl P =>
    cases B with
    | inl R =>
      cases C with
      | inl T => change False at hAC; exact hAC.elim
      | inr Q' =>
        cases D with
        | inl T => change False at hAD; exact hAD.elim
        | inr S =>
          have hPR : P.1.1 ≠ R.1.1 := by
            intro h
            apply hAB
            exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
          have hQS : Q'.1.1 ≠ S.1.1 := by
            intro h
            apply hCD
            exact congrArg Sum.inr (Subtype.ext (Subtype.ext h))
          change Disjoint P.1.1 Q'.1.1 ∧ P.1.1 ∪ Q'.1.1 ∈ F at hAC
          change Disjoint R.1.1 Q'.1.1 ∧ R.1.1 ∪ Q'.1.1 ∈ F at hBC
          change Disjoint P.1.1 S.1.1 ∧ P.1.1 ∪ S.1.1 ∈ F at hAD
          change Disjoint R.1.1 S.1.1 ∧ R.1.1 ∪ S.1.1 ∈ F at hBD
          exact fixedCenter_pairNode_rectangle_forbidden F Q V x color i j
            hProper hAdmissible P R Q' S hPR hQS
            hAC.1 hAD.1 hBC.1 hBD.1 hAC.2 hBD.2 hAD.2 hBC.2
    | inr Q' =>
      cases C <;> cases D <;>
        simp [G, fixedCenterPairNodeGraph] at hAC hBC
  | inr Q' =>
    cases B with
    | inl P =>
      cases C <;> cases D <;>
        simp [G, fixedCenterPairNodeGraph] at hAC hBC
    | inr S =>
      cases C with
      | inr T => change False at hAC; exact hAC.elim
      | inl P =>
        cases D with
        | inr T => change False at hAD; exact hAD.elim
        | inl R =>
          have hQS : Q'.1.1 ≠ S.1.1 := by
            intro h
            apply hAB
            exact congrArg Sum.inr (Subtype.ext (Subtype.ext h))
          have hPR : P.1.1 ≠ R.1.1 := by
            intro h
            apply hCD
            exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
          have hAC' : Disjoint P.1.1 Q'.1.1 ∧
              P.1.1 ∪ Q'.1.1 ∈ F := by
            exact ⟨hAC.1.symm, by simpa [Finset.union_comm] using hAC.2⟩
          have hBC' : Disjoint P.1.1 S.1.1 ∧
              P.1.1 ∪ S.1.1 ∈ F := by
            exact ⟨hBC.1.symm, by simpa [Finset.union_comm] using hBC.2⟩
          have hAD' : Disjoint R.1.1 Q'.1.1 ∧
              R.1.1 ∪ Q'.1.1 ∈ F := by
            exact ⟨hAD.1.symm, by simpa [Finset.union_comm] using hAD.2⟩
          have hBD' : Disjoint R.1.1 S.1.1 ∧
              R.1.1 ∪ S.1.1 ∈ F := by
            exact ⟨hBD.1.symm, by simpa [Finset.union_comm] using hBD.2⟩
          exact fixedCenter_pairNode_rectangle_forbidden F Q V x color i j
            hProper hAdmissible P R Q' S hPR hQS
            hAC'.1 hBC'.1 hAD'.1 hBD'.1 hAC'.2 hBD'.2 hBC'.2 hAD'.2

omit [Fintype α] in
/-- The existing finite C4 bound applies directly to each actual fixed-x,
fixed-color pair-node graph. -/
theorem fixedCenterPairNodeGraph_edge_bound
    (F Q : Family α) (V : Edge α) (x : α)
    (color : fixedCenterPairNodes Q V x → ℕ) (i j : ℕ)
    (hProper : ∀ P R : fixedCenterPairNodes Q V x,
      P.1 ≠ R.1 → ¬ Disjoint P.1 R.1 → color P ≠ color R)
    (hAdmissible : Admissible F) :
    ((fixedCenterPairNodeGraph F Q V x color i j).edgeFinset.card : ℝ) ≤
      (Real.sqrt ((Fintype.card (Sum
        {P : fixedCenterPairNodes Q V x // color P = i}
        {P : fixedCenterPairNodes Q V x // color P = j}) : ℝ) ^ 3) +
        (Fintype.card (Sum
          {P : fixedCenterPairNodes Q V x // color P = i}
          {P : fixedCenterPairNodes Q V x // color P = j}) : ℝ) / 2) / 2 := by
  exact fourCycleFree_edge_sqrt_bound _
    (fixedCenterPairNodeGraph_fourCycleFree F Q V x color i j
      hProper hAdmissible)

/-- Actual four-edges represented by a disjoint pair of Q-link pair nodes.
This is the deletion family charged by the fixed-center pair-node graphs. -/
noncomputable def fixedCenterPairNodeDeletion
    (F Q : Family α) (V : Edge α) (x : α) :
    Family α :=
  F.filter fun E => ∃ P R : fixedCenterPairNodes Q V x,
    Disjoint P.1 R.1 ∧ P.1 ∪ R.1 = E

omit [Fintype α] in
/-- The fixed-center represented-edge deletion is an actual subfamily. -/
theorem fixedCenterPairNodeDeletion_subset
    (F Q : Family α) (V : Edge α) (x : α) :
    fixedCenterPairNodeDeletion F Q V x ⊆ F := by
  intro E hE
  exact (Finset.mem_filter.mp hE).1

end JSP523.Rank4
