import JSP523.Rank4.GraphCompletionData
import JSP523.Rank3.IncidenceDoubleCount
import JSP523.Rank4.PreprocessReciprocalDeletion

/-!
# Local attachment analysis for reciprocal triangles

The actual completion data turns an attachment to a reciprocal triangle
into a monochromatic or rainbow completion triangle.  The second theorem
isolates the two cleanup consequences needed to rule out these attachments:
uniqueness of reciprocal witnesses in the monochromatic case and the
parent-label separation consequence in the rainbow case.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual triple system of the fixed parent pair labels. -/
def reciprocalParentLabelTriples
    (D : FiniteCompletionCliqueData α) (V : Edge α) : Family α :=
  (V.product V).image fun xy =>
    insert (D.label xy.1 xy.2) ({xy.1, xy.2} : Edge α)

omit [Fintype α] in
theorem mem_reciprocalParentLabelTriples
    (D : FiniteCompletionCliqueData α) (V : Edge α)
    (x y : α) (hx : x ∈ V) (hy : y ∈ V) :
    insert (D.label x y) ({x, y} : Edge α) ∈
      reciprocalParentLabelTriples D V := by
  apply Finset.mem_image.mpr
  exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

/-- Parent-label separation: for each surviving four-edge, the completion
sets of distinct pair roots in its six pairs are disjoint. -/
def ReciprocalParentPairSeparation
    (D : FiniteCompletionCliqueData α) : Prop :=
  ∀ E ∈ D.K, ∀ R ∈ E.powersetCard 2, ∀ S ∈ E.powersetCard 2,
    R ≠ S →
      Disjoint
        (JSP523.Rank3.completionVertices
          (reciprocalParentLabelTriples D D.ground) D.ground R)
        (JSP523.Rank3.completionVertices
          (reciprocalParentLabelTriples D D.ground) D.ground S)

omit [Fintype α] in
/-- An attachment at `a` to the actual pair-link triangle `a,b,w` makes
the completion triangle `b,w,t` at facet `a ∪ P` monochromatic or rainbow.
The pair labels are those of the fixed finite parent completion data. -/
theorem reciprocal_triangle_attachment_is_mono_or_rainbow
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w t : α)
    [DecidableRel (completionPairLinkGraph D P).Adj]
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground)
    (hab : b ≠ w) (hat : b ≠ t) (hwt : w ≠ t)
    (hAB : (completionPairLinkGraph D P).Adj a b)
    (hAW : (completionPairLinkGraph D P).Adj a w)
    (hAT : (completionPairLinkGraph D P).Adj a t)
    (hBWlabel : D.label b w = a) :
    (D.label b t = a ∧ D.label w t = a) ∨
      (D.label b t ≠ a ∧ D.label w t ≠ a ∧
        D.label b t ≠ D.label w t) := by
  classical
  let T := insert a P
  have hAB' := hAB
  have hAW' := hAW
  have hAT' := hAT
  change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
  change a ∉ P ∧ w ∉ P ∧ a ∈ D.ground ∧ w ∈ D.ground ∧
    a ≠ w ∧ insert a (insert w P) ∈ D.K at hAW'
  change a ∉ P ∧ t ∉ P ∧ a ∈ D.ground ∧ t ∈ D.ground ∧
    a ≠ t ∧ insert a (insert t P) ∈ D.K at hAT'
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hAB'.1, hPcard]
  have hTground : T ⊆ D.ground := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hxP
    · exact hxa ▸ hAB'.2.2.1
    · exact hPground hxP
  have hbComp : b ∈ graphFacetCompletions D.K D.ground T := by
    apply Finset.mem_filter.mpr
    refine ⟨hAB'.2.2.2.1, ?_⟩
    simpa [T, Finset.insert_comm] using hAB'.2.2.2.2.2
  have hwComp : w ∈ graphFacetCompletions D.K D.ground T := by
    apply Finset.mem_filter.mpr
    refine ⟨hAW'.2.2.2.1, ?_⟩
    simpa [T, Finset.insert_comm] using hAW'.2.2.2.2.2
  have htComp : t ∈ graphFacetCompletions D.K D.ground T := by
    apply Finset.mem_filter.mpr
    refine ⟨hAT'.2.2.2.1, ?_⟩
    simpa [T, Finset.insert_comm] using hAT'.2.2.2.2.2
  rcases completion_triangle_mono_or_rainbow D T b w t
      hbComp hwComp htComp hab hat hwt with hMono | hRainbow
  · rcases hMono with ⟨hBWbt, hBWwt⟩
    rw [hBWlabel] at hBWbt hBWwt
    exact Or.inl ⟨hBWbt.symm, hBWwt.symm⟩
  · rcases hRainbow with ⟨hBWbt, hBWwt, hbtwt⟩
    rw [hBWlabel] at hBWbt hBWwt
    exact Or.inr ⟨hBWbt.symm, hBWwt.symm, hbtwt⟩

omit [Fintype α] in
/-- Under the surviving-reciprocal uniqueness condition and the rainbow
separation condition, a reciprocal triangle has no attachment at `a` in
its actual pair-link graph.  The separation premise is stated on the
actual labels lying in the parent pair `P`; it is the exact consequence
that the bounded-label cleanup must provide. -/
theorem reciprocal_triangle_has_no_attachment_at_a
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel (completionPairLinkGraph D P).Adj]
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground)
    (hbw : b ≠ w)
    (hAB : (completionPairLinkGraph D P).Adj a b)
    (hAW : (completionPairLinkGraph D P).Adj a w)
    (_hBW : (completionPairLinkGraph D P).Adj b w)
    (hAWlabel : D.label a w = b)
    (hBWlabel : D.label b w = a)
    (hNoSecond : ∀ t : α,
      t ≠ b → t ≠ w →
      (completionPairLinkGraph D P).Adj a t →
      D.label a w = b → D.label b t = a → w = t)
    (hNoSeparatedRainbow : ∀ t : α,
      t ≠ b → t ≠ w →
      (completionPairLinkGraph D P).Adj a t →
      D.label b t ∈ P → D.label w t ∈ P →
      D.label b t ≠ D.label w t → False) :
    ∀ t : α, t ≠ b → t ≠ w →
      ¬ (completionPairLinkGraph D P).Adj a t := by
  intro t htb htw hAttach
  rcases reciprocal_triangle_attachment_is_mono_or_rainbow
      D P a b w t hPcard hPground hbw htb.symm htw.symm
      hAB hAW hAttach hBWlabel with hMono | hRainbow
  · rcases hMono with ⟨hBT, _⟩
    have hEq := hNoSecond t htb htw hAttach hAWlabel hBT
    exact htw hEq.symm
  · rcases hRainbow with ⟨hBT, hWT, hBTW⟩
    let T := insert a P
    have hAB' := hAB
    have hAW' := hAW
    have hAT' := hAttach
    change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
      a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
    change a ∉ P ∧ w ∉ P ∧ a ∈ D.ground ∧ w ∈ D.ground ∧
      a ≠ w ∧ insert a (insert w P) ∈ D.K at hAW'
    change a ∉ P ∧ t ∉ P ∧ a ∈ D.ground ∧ t ∈ D.ground ∧
      a ≠ t ∧ insert a (insert t P) ∈ D.K at hAT'
    have hTcard : T.card = 3 := by
      dsimp [T]
      rw [Finset.card_insert_of_notMem hAB'.1, hPcard]
    have hTground : T ⊆ D.ground := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxP
      · exact hxa ▸ hAB'.2.2.1
      · exact hPground hxP
    have hbComp : b ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      refine ⟨hAB'.2.2.2.1, ?_⟩
      simpa [T, Finset.insert_comm] using hAB'.2.2.2.2.2
    have htComp : t ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      refine ⟨hAT'.2.2.2.1, ?_⟩
      simpa [T, Finset.insert_comm] using hAT'.2.2.2.2.2
    have hwComp : w ∈ graphFacetCompletions D.K D.ground T := by
      apply Finset.mem_filter.mpr
      refine ⟨hAW'.2.2.2.1, ?_⟩
      simpa [T, Finset.insert_comm] using hAW'.2.2.2.2.2
    have hBTin : D.label b t ∈ T :=
      completion_pair_label_mem_facet D T hTcard hTground b t hbComp htComp htb.symm
    have hWTin : D.label w t ∈ T :=
      completion_pair_label_mem_facet D T hTcard hTground w t hwComp htComp htw.symm
    have hBTinP : D.label b t ∈ P := by
      rcases Finset.mem_insert.mp hBTin with h | h
      · exact (hBT h).elim
      · exact h
    have hWTinP : D.label w t ∈ P := by
      rcases Finset.mem_insert.mp hWTin with h | h
      · exact (hWT h).elim
      · exact h
    exact hNoSeparatedRainbow t htb htw hAttach hBTinP hWTinP hBTW

omit [Fintype α] in
/-- The two cleanup conditions isolate all three vertices of an actual
reciprocal triangle in its pair-link graph.  Hence no other pair-link edge
can leave any triangle vertex. -/
theorem reciprocal_triangle_has_no_external_neighbors
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel (completionPairLinkGraph D P).Adj]
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (hAB : (completionPairLinkGraph D P).Adj a b)
    (hAW : (completionPairLinkGraph D P).Adj a w)
    (hBW : (completionPairLinkGraph D P).Adj b w)
    (hABlabel : D.label a b = w)
    (hAWlabel : D.label a w = b)
    (hBWlabel : D.label b w = a)
    (hNoSecond : ∀ x y r s : α,
      (completionPairLinkGraph D P).Adj x y →
      (completionPairLinkGraph D P).Adj y r →
      (completionPairLinkGraph D P).Adj x s →
      x ≠ y → x ≠ r → x ≠ s → y ≠ r → y ≠ s → r ≠ s →
      D.label x r = y → D.label y s = x → r = s)
    (hNoSeparatedAtA : ∀ t : α,
      t ≠ b → t ≠ w →
      (completionPairLinkGraph D P).Adj a t →
      D.label b t ∈ P → D.label w t ∈ P →
      D.label b t ≠ D.label w t → False)
    (hNoSeparatedAtB : ∀ t : α,
      t ≠ a → t ≠ w →
      (completionPairLinkGraph D P).Adj b t →
      D.label a t ∈ P → D.label w t ∈ P →
      D.label a t ≠ D.label w t → False)
    (hNoSeparatedAtW : ∀ t : α,
      t ≠ a → t ≠ b →
      (completionPairLinkGraph D P).Adj w t →
      D.label a t ∈ P → D.label b t ∈ P →
      D.label a t ≠ D.label b t → False) :
    ∀ x ∈ ({a, b, w} : Edge α), ∀ t : α,
      t ∉ ({a, b, w} : Edge α) →
      ¬ (completionPairLinkGraph D P).Adj x t := by
  have hNoA := reciprocal_triangle_has_no_attachment_at_a
    D P a b w hPcard hPground hbw hAB hAW hBW
    hAWlabel hBWlabel
    (fun (t : α) (htb : t ≠ b) (htw : t ≠ w)
        (hAttach : (completionPairLinkGraph D P).Adj a t)
        (hLabelX : D.label a w = b) (hLabelY : D.label b t = a) => by
      have hAt : a ≠ t := by
        change a ∉ P ∧ t ∉ P ∧ a ∈ D.ground ∧ t ∈ D.ground ∧
          a ≠ t ∧ insert a (insert t P) ∈ D.K at hAttach
        exact hAttach.2.2.2.2.1
      exact hNoSecond a b w t hAB hBW hAttach hab haw hAt
        hbw htb.symm htw.symm hLabelX hLabelY)
    hNoSeparatedAtA
  have hNoB := reciprocal_triangle_has_no_attachment_at_a
    D P b a w hPcard hPground haw hAB.symm hBW hAW
    hBWlabel hAWlabel
    (fun (t : α) (hta : t ≠ a) (htw : t ≠ w)
        (hAttach : (completionPairLinkGraph D P).Adj b t)
        (hLabelX : D.label b w = a) (hLabelY : D.label a t = b) => by
      have hBt : b ≠ t := by
        change b ∉ P ∧ t ∉ P ∧ b ∈ D.ground ∧ t ∈ D.ground ∧
          b ≠ t ∧ insert b (insert t P) ∈ D.K at hAttach
        exact hAttach.2.2.2.2.1
      exact hNoSecond b a w t hAB.symm hAW hAttach hab.symm hbw hBt
        haw hta.symm htw.symm hLabelX hLabelY)
    hNoSeparatedAtB
  have hWb : D.label w b = a := by
    simpa [D.label_symm] using hBWlabel
  have hAb : D.label a b = w := hABlabel
  have hNoW := reciprocal_triangle_has_no_attachment_at_a
    D P w a b hPcard hPground hab hAW.symm hBW.symm hAB
    hWb hAb
    (fun (t : α) (hta : t ≠ a) (htb : t ≠ b)
        (hAttach : (completionPairLinkGraph D P).Adj w t)
        (hLabelX : D.label w b = a) (hLabelY : D.label a t = w) => by
      have hWt : w ≠ t := by
        change w ∉ P ∧ t ∉ P ∧ w ∈ D.ground ∧ t ∈ D.ground ∧
          w ≠ t ∧ insert w (insert t P) ∈ D.K at hAttach
        exact hAttach.2.2.2.2.1
      exact hNoSecond w a b t hAW.symm hAB hAttach haw.symm hbw.symm hWt
        hab hta.symm htb.symm hLabelX hLabelY)
    hNoSeparatedAtW
  intro x hx t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxa | hxb | hxw
  · subst x
    have htb : t ≠ b := by
      intro h
      exact ht (by simp [h])
    have htw : t ≠ w := by
      intro h
      exact ht (by simp [h])
    exact hNoA t htb htw
  · subst x
    have hta : t ≠ a := by
      intro h
      exact ht (by simp [h])
    have htw : t ≠ w := by
      intro h
      exact ht (by simp [h])
    exact hNoB t hta htw
  · subst x
    have hta : t ≠ a := by
      intro h
      exact ht (by simp [h])
    have htb : t ≠ b := by
      intro h
      exact ht (by simp [h])
    exact hNoW t hta htb

omit [Fintype α] in
/-- In a rainbow attachment, the two other labels give disjoint pair roots
inside the reciprocal four-edge, while the attachment vertex belongs to
both parent-label completion sets. Parent-label separation rules this out. -/
theorem reciprocal_triangle_rainbow_attachment_forbidden
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel (completionPairLinkGraph D P).Adj]
    (hPground : P ⊆ D.ground)
    (hBW : (completionPairLinkGraph D P).Adj b w)
    (hSeparated : ReciprocalParentPairSeparation D) :
    ∀ t : α,
      t ≠ b → t ≠ w →
      (completionPairLinkGraph D P).Adj a t →
      D.label b t ∈ P → D.label w t ∈ P →
      D.label b t ≠ D.label w t → False := by
  classical
  intro t hNotB hNotW hAT hBTinP hWTinP hDiff
  have hBW' := hBW
  have hAT' := hAT
  change b ∉ P ∧ w ∉ P ∧ b ∈ D.ground ∧ w ∈ D.ground ∧
    b ≠ w ∧ insert b (insert w P) ∈ D.K at hBW'
  change a ∉ P ∧ t ∉ P ∧ a ∈ D.ground ∧ t ∈ D.ground ∧
    a ≠ t ∧ insert a (insert t P) ∈ D.K at hAT'
  let x := D.label b t
  let y := D.label w t
  let R : Edge α := {b, x}
  let S : Edge α := {w, y}
  let E : Edge α := insert b (insert w P)
  have htNotP : t ∉ P := hAT'.2.1
  have htGround : t ∈ D.ground := hAT'.2.2.2.1
  have hxGround : x ∈ D.ground := hPground hBTinP
  have hyGround : y ∈ D.ground := hPground hWTinP
  have hbx : b ≠ x := by
    intro h
    exact hBW'.1 (h ▸ hBTinP)
  have hwy : w ≠ y := by
    intro h
    exact hBW'.2.1 (h ▸ hWTinP)
  have hRcard : R.card = 2 := by
    dsimp [R, x]
    exact Finset.card_pair hbx
  have hScard : S.card = 2 := by
    dsimp [S, y]
    exact Finset.card_pair hwy
  have hRsub : R ⊆ E := by
    intro z hz
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzb | hzx
    · subst z
      simp [E]
    · have hzP : z ∈ P := hzx ▸ hBTinP
      simp [E, hzP]
  have hSsub : S ⊆ E := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzw | hzy
    · subst z
      simp [E]
    · have hzP : z ∈ P := hzy ▸ hWTinP
      simp [E, hzP]
  have hRmem : R ∈ E.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hRsub, hRcard⟩
  have hSmem : S ∈ E.powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hSsub, hScard⟩
  have hDisj : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro z hzR hzS
    simp only [R, S, Finset.mem_insert, Finset.mem_singleton] at hzR hzS
    rcases hzR with hzb | hzx
    · rcases hzS with hzw | hzy
      · exact hBW'.2.2.2.2.1 (hzb.symm.trans hzw)
      · have hby : b = y := hzb.symm.trans hzy
        change y ∈ P at hWTinP
        exact hBW'.1 (hby ▸ hWTinP)
    · rcases hzS with hzw | hzy
      · have hxw : x = w := hzx.symm.trans hzw
        change x ∈ P at hBTinP
        exact hBW'.2.1 (hxw ▸ hBTinP)
      · exact hDiff (hzx.symm.trans hzy)
  have hE : E ∈ D.K := by
    dsimp [E]
    exact hBW'.2.2.2.2.2
  have hTripleX :
      insert x ({b, t} : Edge α) ∈
        reciprocalParentLabelTriples D D.ground := by
    dsimp [x]
    exact mem_reciprocalParentLabelTriples D D.ground b t
      hBW'.2.2.1 htGround
  have hTripleY :
      insert y ({w, t} : Edge α) ∈
        reciprocalParentLabelTriples D D.ground := by
    dsimp [y]
    exact mem_reciprocalParentLabelTriples D D.ground w t
      hBW'.2.2.2.1 htGround
  have hRset : R ∪ {t} = insert x ({b, t} : Edge α) := by
    ext z
    simp only [R, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hSset : S ∪ {t} = insert y ({w, t} : Edge α) := by
    ext z
    simp only [S, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hRcompletion :
      t ∈ JSP523.Rank3.completionVertices
        (reciprocalParentLabelTriples D D.ground) D.ground R := by
    simp only [JSP523.Rank3.completionVertices, Finset.mem_filter]
    refine ⟨htGround, ?_, ?_⟩
    · intro htR
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at htR
      rcases htR with hEqB | hEqX
      · exact hNotB hEqB
      · exact htNotP (hEqX.symm ▸ hBTinP)
    · rw [hRset]
      exact hTripleX
  have hScompletion :
      t ∈ JSP523.Rank3.completionVertices
        (reciprocalParentLabelTriples D D.ground) D.ground S := by
    simp only [JSP523.Rank3.completionVertices, Finset.mem_filter]
    refine ⟨htGround, ?_, ?_⟩
    · intro htS
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at htS
      rcases htS with hEqW | hEqY
      · exact hNotW hEqW
      · exact htNotP (hEqY.symm ▸ hWTinP)
    · rw [hSset]
      exact hTripleY
  have hSeparatedRS := hSeparated E hE R hRmem S hSmem (by
    intro hEq
    have hbR : b ∈ R := by simp [R]
    have hbS : b ∈ S := hEq ▸ hbR
    exact (Finset.disjoint_left.mp hDisj) hbR hbS)
  exact (Finset.disjoint_left.mp hSeparatedRS) hRcompletion hScompletion

omit [Fintype α] in
/-- Parent-label separation discharges each rainbow attachment condition.
Together with uniqueness of the surviving reciprocal witness, it isolates
all three vertices of the reciprocal triangle in the actual pair-link. -/
theorem reciprocal_triangle_isolated_of_parent_separation
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel (completionPairLinkGraph D P).Adj]
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (hAB : (completionPairLinkGraph D P).Adj a b)
    (hAW : (completionPairLinkGraph D P).Adj a w)
    (hBW : (completionPairLinkGraph D P).Adj b w)
    (hABlabel : D.label a b = w)
    (hAWlabel : D.label a w = b)
    (hBWlabel : D.label b w = a)
    (hNoSecond : ∀ x y r s : α,
      (completionPairLinkGraph D P).Adj x y →
      (completionPairLinkGraph D P).Adj y r →
      (completionPairLinkGraph D P).Adj x s →
      x ≠ y → x ≠ r → x ≠ s → y ≠ r → y ≠ s → r ≠ s →
      D.label x r = y → D.label y s = x → r = s)
    (hSeparated : ReciprocalParentPairSeparation D) :
    ∀ x ∈ ({a, b, w} : Edge α), ∀ t : α,
      t ∉ ({a, b, w} : Edge α) →
      ¬ (completionPairLinkGraph D P).Adj x t := by
  have hNoSepA := reciprocal_triangle_rainbow_attachment_forbidden
    D P a b w hPground hBW hSeparated
  have hNoSepB := reciprocal_triangle_rainbow_attachment_forbidden
    D P b a w hPground hAW hSeparated
  have hNoSepW := reciprocal_triangle_rainbow_attachment_forbidden
    D P w a b hPground hAB hSeparated
  exact reciprocal_triangle_has_no_external_neighbors
    D P a b w hPcard hPground hab haw hbw hAB hAW hBW
    hABlabel hAWlabel hBWlabel hNoSecond
    hNoSepA hNoSepB hNoSepW

/-- After the explicit finite distinct-witness deletion, parent-label pair
separation suffices to isolate every surviving reciprocal triangle. -/
theorem reciprocal_triangle_isolated_after_reciprocal_cleanup
    (D : FiniteCompletionCliqueData α) (P : Edge α)
    (a b w : α)
    [DecidableRel
      (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj]
    (hPcard : P.card = 2) (hPground : P ⊆ D.ground)
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (hAB : (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj a b)
    (hAW : (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj a w)
    (hBW : (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj b w)
    (hABlabel : (clearReciprocalDifferentWitnesses D).label a b = w)
    (hAWlabel : (clearReciprocalDifferentWitnesses D).label a w = b)
    (hBWlabel : (clearReciprocalDifferentWitnesses D).label b w = a)
    (hSeparated : ReciprocalParentPairSeparation
      (clearReciprocalDifferentWitnesses D)) :
    ∀ x ∈ ({a, b, w} : Edge α), ∀ t : α,
      t ∉ ({a, b, w} : Edge α) →
      ¬ (completionPairLinkGraph (clearReciprocalDifferentWitnesses D) P).Adj x t := by
  exact reciprocal_triangle_isolated_of_parent_separation
    (clearReciprocalDifferentWitnesses D) P a b w hPcard hPground
    hab haw hbw hAB hAW hBW hABlabel hAWlabel hBWlabel
    (clearReciprocalDifferentWitnesses_no_second D P hPcard hPground)
    hSeparated

end JSP523.Rank4
