import JSP523.Rank4.PreprocessStarLayers
import JSP523.Rank3.PairGraphClassification

/-!
# Cross moments for rank-four star layers

For two distinct star centers and two distinct completion vertices, the pair
roots that support both links form an intersecting graph.  This is the
finite structural input to the distinct-completion part of (III.A.18).
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The triple link at a star center, restricted to the ground set `V`. -/
def rankFourStarLink (H : Family α) (V : Edge α) (c : α) : Family α :=
  (V.powersetCard 3).filter fun T => insert c T ∈ H

/-- Pair roots with both specified completions present in the two star links. -/
def crossCompletionPairGraph (H : Family α) (V : Edge α)
    (c d x y : α) : Family α :=
  (V.powersetCard 2).filter fun P =>
    insert x P ∈ rankFourStarLink H V c ∧
      insert y P ∈ rankFourStarLink H V d

/-- The lifted rank-four edge at center `c`, pair root `P`, and completion `x`. -/
def liftedStarFacet (c x : α) (P : Edge α) : Edge α :=
  insert c (insert x P)

/-- Completion vertices of a link over a fixed pair root. -/
def starLinkCompletions (L : Family α) (V P : Edge α) : Edge α :=
  V.filter fun x => insert x P ∈ L

/-- The cross pair graph for two arbitrary triple links. -/
def linkCrossCompletionPairGraph (L M : Family α) (V : Edge α)
    (x y : α) : Family α :=
  (V.powersetCard 2).filter fun P =>
    insert x P ∈ L ∧ insert y P ∈ M

/-- Pair degree of a link at a pair root. -/
def linkPairDegree (L : Family α) (P : Edge α) : ℕ :=
  ((L).filter fun T => P ⊆ T).card

/-- Pair degree is exactly the number of actual completion vertices.  The
cardinality hypotheses make the representation `T = insert x P` unique. -/
theorem starLinkPairDegree_eq_completion_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Family α) (i : ι) (V P : Edge α)
    (hP : P ∈ V.powersetCard 2)
    (hGround : ∀ T ∈ L i, T ∈ V.powersetCard 3) :
    starLinkPairDegree L i P = (starLinkCompletions (L i) V P).card := by
  classical
  let C := starLinkCompletions (L i) V P
  let D := (L i).filter fun T => P ⊆ T
  have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
  have hMem (x : α) (hx : x ∈ C) : insert x P ∈ D := by
    have hx' := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hx'.2, ?_⟩
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hInj (x : α) (hx : x ∈ C) (y : α) (hy : y ∈ C)
      (hxy : insert x P = insert y P) : x = y := by
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxNot : x ∉ P := by
      intro hxP
      have hEq : insert x P = P := Finset.insert_eq_of_mem hxP
      have hTriple := (Finset.mem_powersetCard.mp (hGround (insert x P) hx'.2)).2
      rw [hEq] at hTriple
      have hTwo := hPcard
      omega
    exact (Finset.insert_inj hxNot).mp hxy
  have hSurj (T : Edge α) (hT : T ∈ D) :
      ∃ x, ∃ _ : x ∈ C, insert x P = T := by
    have hT' := Finset.mem_filter.mp hT
    have hTground := Finset.mem_powersetCard.mp (hGround T hT'.1)
    have hDiff : (T \ P).card = 1 := by
      rw [Finset.card_sdiff_of_subset hT'.2]
      rw [hTground.2, hPcard]
    obtain ⟨x, hSingleton⟩ := Finset.card_eq_one.mp hDiff
    have hUnion : T \ P ∪ P = T := Finset.sdiff_union_of_subset hT'.2
    have hEq : insert x P = T := by
      rw [hSingleton] at hUnion
      simpa [Finset.singleton_union] using hUnion
    have hxV : x ∈ V := by
      have hxT : x ∈ T := by
        have hxDiff : x ∈ T \ P := by simp [hSingleton]
        exact (Finset.mem_sdiff.mp hxDiff).1
      exact hTground.1 hxT
    have hxC : x ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨hxV, ?_⟩
      rw [hEq]
      exact hT'.1
    exact ⟨x, hxC, hEq⟩
  change D.card = C.card
  symm
  exact Finset.card_bij (fun x _ => insert x P) hMem hInj hSurj

/-- The sum of pair-degree products is the number of pair-root/completion
incidences, reindexed by the two completion vertices. -/
theorem link_cross_moment_reindex
    (L M : Family α) (V : Edge α) :
    (∑ P ∈ V.powersetCard 2,
      (starLinkCompletions L V P).card *
        (starLinkCompletions M V P).card) =
      (∑ x ∈ V, ∑ y ∈ V,
        (linkCrossCompletionPairGraph L M V x y).card) := by
  classical
  let I : Finset (Σ P : Edge α, α × α) :=
    (V.powersetCard 2).sigma fun P =>
      (starLinkCompletions L V P).product
        (starLinkCompletions M V P)
  let K : Finset (Σ x : α, Σ y : α, Edge α) :=
    V.sigma fun x => V.sigma fun y =>
      linkCrossCompletionPairGraph L M V x y
  have hMem (p : Σ P : Edge α, α × α) (hp : p ∈ I) :
      (⟨p.2.1, ⟨p.2.2, p.1⟩⟩ : Σ x : α, Σ y : α, Edge α) ∈ K := by
    obtain ⟨hP, hxy⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    apply Finset.mem_sigma.mpr
    refine ⟨hx'.1, ?_⟩
    apply Finset.mem_sigma.mpr
    refine ⟨hy'.1, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨hP, hx'.2, hy'.2⟩
  have hInj (p : Σ P : Edge α, α × α) (_hp : p ∈ I)
      (q : Σ P : Edge α, α × α) (_hq : q ∈ I)
      (heq : (⟨p.2.1, ⟨p.2.2, p.1⟩⟩ : Σ x : α, Σ y : α, Edge α) =
        ⟨q.2.1, ⟨q.2.2, q.1⟩⟩) : p = q := by
    cases p with
    | mk P xy =>
      cases xy with
      | mk x y =>
        cases q with
        | mk Q uv =>
          cases uv with
          | mk u v =>
            simp_all
  have hSurj (q : Σ x : α, Σ y : α, Edge α) (hq : q ∈ K) :
      ∃ p, ∃ _ : p ∈ I,
        (⟨p.2.1, ⟨p.2.2, p.1⟩⟩ : Σ x : α, Σ y : α, Edge α) = q := by
    obtain ⟨hx, hq'⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hy, hP⟩ := Finset.mem_sigma.mp hq'
    have hG := Finset.mem_filter.mp hP
    have hL : q.1 ∈ starLinkCompletions L V q.2.2 := by
      exact Finset.mem_filter.mpr ⟨hx, hG.2.1⟩
    have hM : q.2.1 ∈ starLinkCompletions M V q.2.2 := by
      exact Finset.mem_filter.mpr ⟨hy, hG.2.2⟩
    have hp : (⟨q.2.2, (q.1, q.2.1)⟩ : Σ P : Edge α, α × α) ∈ I := by
      apply Finset.mem_sigma.mpr
      exact ⟨hG.1, Finset.mem_product.mpr ⟨hL, hM⟩⟩
    exact ⟨⟨q.2.2, (q.1, q.2.1)⟩, hp, by cases q; rfl⟩
  have hCard : I.card = K.card :=
    Finset.card_bij (fun p _ =>
      (⟨p.2.1, ⟨p.2.2, p.1⟩⟩ : Σ x : α, Σ y : α, Edge α))
      hMem hInj hSurj
  have hIcard : I.card =
      ∑ P ∈ V.powersetCard 2,
        (starLinkCompletions L V P).card *
          (starLinkCompletions M V P).card := by
    dsimp [I]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro P hP
    exact Finset.card_product _ _
  have hKcard : K.card =
      ∑ x ∈ V, ∑ y ∈ V,
        (linkCrossCompletionPairGraph L M V x y).card := by
    dsimp [K]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x hx
    exact Finset.card_sigma V fun y =>
      linkCrossCompletionPairGraph L M V x y
  calc
    (∑ P ∈ V.powersetCard 2,
      (starLinkCompletions L V P).card *
        (starLinkCompletions M V P).card) = I.card := hIcard.symm
    _ = K.card := hCard
    _ = ∑ x ∈ V, ∑ y ∈ V,
        (linkCrossCompletionPairGraph L M V x y).card := hKcard

/-- Convert the completion count back to the actual pair degree. -/
theorem linkPairDegree_eq_completion_card
    (L : Family α) (V P : Edge α) (hP : P ∈ V.powersetCard 2)
    (hGround : ∀ T ∈ L, T ∈ V.powersetCard 3) :
    linkPairDegree L P = (starLinkCompletions L V P).card := by
  classical
  let L' : Unit → Family α := fun _ => L
  have h := starLinkPairDegree_eq_completion_card L' () V P hP (by
    intro T hT
    exact hGround T hT)
  simpa [linkPairDegree, starLinkPairDegree, L'] using h

/-- The pair-root/completion incidence count of a triple family is exactly
three times its size. This is the diagonal contribution in (III.A.18). -/
theorem triple_pair_completion_incidence_card
    (V : Edge α) (J : Family α)
    (hGround : ∀ T ∈ J, T ∈ V.powersetCard 3) :
    (((V.powersetCard 2).product V).filter fun q =>
      insert q.2 q.1 ∈ J).card = 3 * J.card := by
  classical
  let I : Finset (Σ T : Edge α, Edge α) := J.sigma fun T => T.powersetCard 2
  let C : Finset (Edge α × α) :=
    ((V.powersetCard 2).product V).filter fun q => insert q.2 q.1 ∈ J
  have hMem (q : Edge α × α) (hq : q ∈ C) :
      (⟨insert q.2 q.1, q.1⟩ : Σ T : Edge α, Edge α) ∈ I := by
    have hq' := Finset.mem_filter.mp hq
    have hp := Finset.mem_product.mp hq'.1
    have hP := Finset.mem_powersetCard.mp hp.1
    apply Finset.mem_sigma.mpr
    refine ⟨hq'.2, ?_⟩
    apply Finset.mem_powersetCard.mpr
    exact ⟨by intro z hz; exact Finset.mem_insert_of_mem hz,
      hP.2⟩
  have hInj (q : Edge α × α) (hq : q ∈ C)
      (r : Edge α × α) (_hr : r ∈ C)
      (heq : (⟨insert q.2 q.1, q.1⟩ : Σ T : Edge α, Edge α) =
        ⟨insert r.2 r.1, r.1⟩) : q = r := by
    have hP : q.1 = r.1 := congrArg Sigma.snd heq
    have hT : insert q.2 q.1 = insert r.2 r.1 := congrArg Sigma.fst heq
    have hq' := Finset.mem_filter.mp hq
    have hqT := Finset.mem_powersetCard.mp
      (hGround _ hq'.2)
    have hqNot : q.2 ∉ q.1 := by
      intro hx
      have hEq : insert q.2 q.1 = q.1 := Finset.insert_eq_of_mem hx
      have hCard := hqT.2
      have hPCard := (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp hq'.1).1).2
      rw [hEq] at hCard
      omega
    have hxy : q.2 = r.2 := by
      rw [← hP] at hT
      exact (Finset.insert_inj hqNot).mp hT
    exact Prod.ext hP hxy
  have hSurj (p : Σ T : Edge α, Edge α) (hp : p ∈ I) :
      ∃ q, ∃ _ : q ∈ C,
        (⟨insert q.2 q.1, q.1⟩ : Σ T : Edge α, Edge α) = p := by
    obtain ⟨hT, hP⟩ := Finset.mem_sigma.mp hp
    have hP' := Finset.mem_powersetCard.mp hP
    have hT' := Finset.mem_powersetCard.mp (hGround _ hT)
    have hDiff : (p.1 \ p.2).card = 1 := by
      rw [Finset.card_sdiff_of_subset hP'.1, hT'.2, hP'.2]
    obtain ⟨x, hSingleton⟩ := Finset.card_eq_one.mp hDiff
    have hUnion := Finset.sdiff_union_of_subset hP'.1
    have hEq : insert x p.2 = p.1 := by
      rw [hSingleton] at hUnion
      simpa [Finset.singleton_union] using hUnion
    have hxV : x ∈ V := hT'.1 ((Finset.mem_sdiff.mp (by simp [hSingleton] :
      x ∈ p.1 \ p.2)).1)
    have hPsubV : p.2 ⊆ V := hP'.1.trans hT'.1
    have hPairV : p.2 ∈ V.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨hPsubV, hP'.2⟩
    have hq : (p.2, x) ∈ C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hPairV, hxV⟩, hEq ▸ hT⟩
    refine ⟨(p.2, x), hq, ?_⟩
    cases p with
    | mk T P =>
      exact congrArg (fun U : Edge α => (⟨U, P⟩ :
        Σ _ : Edge α, Edge α)) hEq
  have hCard : C.card = I.card :=
    Finset.card_bij (fun q _ => (⟨insert q.2 q.1, q.1⟩ :
      Σ T : Edge α, Edge α)) hMem hInj hSurj
  have hIcard : I.card = 3 * J.card := by
    dsimp [I]
    rw [Finset.card_sigma]
    calc
      (∑ T ∈ J, (T.powersetCard 2).card) =
          ∑ T ∈ J, 3 := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.card_powersetCard, (Finset.mem_powersetCard.mp
          (hGround T hT)).2]
        norm_num
      _ = 3 * J.card := by simp [Finset.sum_const, mul_comm]
  change C.card = 3 * J.card
  rw [hCard]
  exact hIcard

/-- Reindex the same incidence set by its completion vertex. -/
theorem triple_pair_completion_incidence_sum
    (V : Edge α) (J : Family α)
    (hGround : ∀ T ∈ J, T ∈ V.powersetCard 3) :
    (∑ x ∈ V,
      ((V.powersetCard 2).filter fun P => insert x P ∈ J).card) =
        3 * J.card := by
  classical
  let I : Finset (Σ x : α, Edge α) := V.sigma fun x =>
    (V.powersetCard 2).filter fun P => insert x P ∈ J
  let C : Finset (Edge α × α) :=
    ((V.powersetCard 2).product V).filter fun q => insert q.2 q.1 ∈ J
  have hMem (q : Edge α × α) (hq : q ∈ C) :
      (⟨q.2, q.1⟩ : Σ x : α, Edge α) ∈ I := by
    have hq' := Finset.mem_filter.mp hq
    have hp := Finset.mem_product.mp hq'.1
    exact Finset.mem_sigma.mpr ⟨hp.2,
      Finset.mem_filter.mpr ⟨hp.1, hq'.2⟩⟩
  have hInj (q : Edge α × α) (hq : q ∈ C)
      (r : Edge α × α) (hr : r ∈ C)
      (heq : (⟨q.2, q.1⟩ : Σ x : α, Edge α) = ⟨r.2, r.1⟩) : q = r := by
    have hx : q.2 = r.2 := congrArg Sigma.fst heq
    have hP : q.1 = r.1 := congrArg Sigma.snd heq
    exact Prod.ext hP hx
  have hSurj (p : Σ x : α, Edge α) (hp : p ∈ I) :
      ∃ q, ∃ _ : q ∈ C, (⟨q.2, q.1⟩ : Σ x : α, Edge α) = p := by
    obtain ⟨hx, hP⟩ := Finset.mem_sigma.mp hp
    have hP' := Finset.mem_filter.mp hP
    have hq : (p.2, p.1) ∈ C := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hP'.1, hx⟩, hP'.2⟩
    exact ⟨(p.2, p.1), hq, by cases p; rfl⟩
  have hCard : C.card = I.card :=
    Finset.card_bij (fun q _ => (⟨q.2, q.1⟩ : Σ x : α, Edge α))
      hMem hInj hSurj
  have hIcard : I.card =
      ∑ x ∈ V, ((V.powersetCard 2).filter fun P => insert x P ∈ J).card := by
    exact Finset.card_sigma V
      (fun x => (V.powersetCard 2).filter fun P => insert x P ∈ J)
  have hCcard := triple_pair_completion_incidence_card V J hGround
  calc
    (∑ x ∈ V, ((V.powersetCard 2).filter fun P => insert x P ∈ J).card)
        = I.card := hIcard.symm
    _ = C.card := hCard.symm
    _ = 3 * J.card := hCcard

/-- Exact finite double counting for two triple links. The diagonal
completions count common triples three times; all other terms have distinct
completion vertices. -/
theorem link_cross_moment_exact
    (L M : Family α) (V : Edge α)
    (hL : ∀ T ∈ L, T ∈ V.powersetCard 3)
    (hM : ∀ T ∈ M, T ∈ V.powersetCard 3) :
    (∑ P ∈ V.powersetCard 2,
      linkPairDegree L P * linkPairDegree M P) =
      3 * (L ∩ M).card +
        ∑ x ∈ V, ∑ y ∈ V.erase x,
          (linkCrossCompletionPairGraph L M V x y).card := by
  classical
  let J := L ∩ M
  have hJ : ∀ T ∈ J, T ∈ V.powersetCard 3 := by
    intro T hT
    exact hL T (Finset.mem_inter.mp hT).1
  have hDiag (x : α) :
      linkCrossCompletionPairGraph L M V x x =
        (V.powersetCard 2).filter fun P => insert x P ∈ J := by
    ext P
    simp [linkCrossCompletionPairGraph, J]
  have hDiagSum :
      (∑ x ∈ V,
        (linkCrossCompletionPairGraph L M V x x).card) = 3 * J.card := by
    calc
      _ = ∑ x ∈ V,
          ((V.powersetCard 2).filter fun P => insert x P ∈ J).card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hDiag]
      _ = 3 * J.card := triple_pair_completion_incidence_sum V J hJ
  have hReindex :
      (∑ P ∈ V.powersetCard 2,
        linkPairDegree L P * linkPairDegree M P) =
      (∑ x ∈ V, ∑ y ∈ V,
        (linkCrossCompletionPairGraph L M V x y).card) := by
    calc
      _ = ∑ P ∈ V.powersetCard 2,
          (starLinkCompletions L V P).card *
            (starLinkCompletions M V P).card := by
              apply Finset.sum_congr rfl
              intro P hP
              rw [linkPairDegree_eq_completion_card L V P hP hL,
                linkPairDegree_eq_completion_card M V P hP hM]
      _ = _ := link_cross_moment_reindex L M V
  calc
    _ = ∑ x ∈ V, ∑ y ∈ V,
        (linkCrossCompletionPairGraph L M V x y).card := hReindex
    _ = (∑ x ∈ V,
          (linkCrossCompletionPairGraph L M V x x).card) +
        ∑ x ∈ V, ∑ y ∈ V.erase x,
          (linkCrossCompletionPairGraph L M V x y).card := by
            symm
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            exact Finset.add_sum_erase V
              (fun y => (linkCrossCompletionPairGraph L M V x y).card) hx
    _ = 3 * J.card +
        ∑ x ∈ V, ∑ y ∈ V.erase x,
          (linkCrossCompletionPairGraph L M V x y).card := by
            rw [hDiagSum]
    _ = 3 * (L ∩ M).card +
        ∑ x ∈ V, ∑ y ∈ V.erase x,
          (linkCrossCompletionPairGraph L M V x y).card := by rfl

/-- The diagonal of the actual cross-completion graphs contributes exactly
three incidences for each triple in the common link. -/
theorem sum_diagonal_cross_completion_graphs
    {H : Family α} {V : Edge α} {c d : α} :
    (∑ x ∈ V,
      (crossCompletionPairGraph H V c d x x).card) =
        3 * (rankFourStarLink H V c ∩ rankFourStarLink H V d).card := by
  classical
  let J := rankFourStarLink H V c ∩ rankFourStarLink H V d
  have hGround : ∀ T ∈ J, T ∈ V.powersetCard 3 := by
    intro T hT
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hT).1).1
  have hGraph (x : α) :
      crossCompletionPairGraph H V c d x x =
        (V.powersetCard 2).filter fun P => insert x P ∈ J := by
    ext P
    simp [crossCompletionPairGraph, J, rankFourStarLink]
  calc
    (∑ x ∈ V, (crossCompletionPairGraph H V c d x x).card)
        = ∑ x ∈ V, ((V.powersetCard 2).filter
            fun P => insert x P ∈ J).card := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hGraph]
    _ = 3 * J.card := triple_pair_completion_incidence_sum V J hGround
    _ = 3 * (rankFourStarLink H V c ∩ rankFourStarLink H V d).card := by
          rfl

/-- The exact cross moment for two actual star links in an admissible
rank-four family. -/
theorem rank_four_star_cross_moment_exact
    {H : Family α} {V : Edge α} {c d : α} :
    (∑ P ∈ V.powersetCard 2,
      linkPairDegree (rankFourStarLink H V c) P *
        linkPairDegree (rankFourStarLink H V d) P) =
      3 * (rankFourStarLink H V c ∩ rankFourStarLink H V d).card +
        ∑ x ∈ V, ∑ y ∈ V.erase x,
          (crossCompletionPairGraph H V c d x y).card := by
  have hLc : ∀ T ∈ rankFourStarLink H V c,
      T ∈ V.powersetCard 3 := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hLd : ∀ T ∈ rankFourStarLink H V d,
      T ∈ V.powersetCard 3 := by
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have hExact := link_cross_moment_exact
    (rankFourStarLink H V c) (rankFourStarLink H V d) V hLc hLd
  simpa [linkCrossCompletionPairGraph, crossCompletionPairGraph,
    rankFourStarLink] using hExact

omit [DecidableEq α] in
private theorem pair_roots_ne_of_disjoint
    {P Q : Edge α} (hPQ : Disjoint P Q) (hP : P.Nonempty) : P ≠ Q := by
  intro hEq
  obtain ⟨z, hz⟩ := hP
  exact (Finset.disjoint_left.mp hPQ) hz (hEq ▸ hz)

private theorem lifted_facets_same_center_ne
    {c x : α} {P Q V : Edge α}
    (hPsub : P ⊆ V) (hQsub : Q ⊆ V) (hcV : c ∉ V)
    (hxV : x ∈ V) (hxP : x ∉ P) (hxQ : x ∉ Q) (hPQ : P ≠ Q) :
    liftedStarFacet c x P ≠ liftedStarFacet c x Q := by
  intro hEq
  have hcP : c ∉ insert x P := by
    simp only [Finset.mem_insert]
    intro h
    rcases h with hcx | hcP
    · exact hcV (hcx ▸ hxV)
    · exact hcV (hPsub hcP)
  have hcQ : c ∉ insert x Q := by
    simp only [Finset.mem_insert]
    intro h
    rcases h with hcx | hcQ
    · exact hcV (hcx ▸ hxV)
    · exact hcV (hQsub hcQ)
  have hErase := congrArg (fun E : Edge α => E.erase c) hEq
  have hT : insert x P = insert x Q := by
    simpa [liftedStarFacet, Finset.erase_insert hcP,
      Finset.erase_insert hcQ] using hErase
  have hPQ' : P = Q := by
    have hEraseX := congrArg (fun T : Edge α => T.erase x) hT
    simpa [Finset.erase_insert hxP, Finset.erase_insert hxQ] using hEraseX
  exact hPQ hPQ'

private theorem lifted_facets_disjoint
    {c d x y : α} {P Q V : Edge α}
    (hPQ : Disjoint P Q) (hPsub : P ⊆ V) (hQsub : Q ⊆ V)
    (hxV : x ∈ V) (hyV : y ∈ V)
    (hxQ : x ∉ Q) (hyP : y ∉ P) (hxy : x ≠ y)
    (hcV : c ∉ V) (hdV : d ∉ V) (hcd : c ≠ d) :
    Disjoint (liftedStarFacet c x P) (liftedStarFacet d y Q) := by
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  simp only [liftedStarFacet, Finset.mem_insert] at hzA hzB
  rcases hzA with hzc | hzx | hzP
  · rcases hzB with hzd | hzy | hzQ
    · exact hcd (hzc.symm.trans hzd)
    · exact hcV (hzc.symm.trans hzy ▸ hyV)
    · exact hcV (hzc ▸ hQsub hzQ)
  · rcases hzB with hzd | hzy | hzQ
    · exact hdV (hzd.symm.trans hzx ▸ hxV)
    · exact hxy (hzx.symm.trans hzy)
    · exact hxQ (hzx.symm ▸ hzQ)
  · rcases hzB with hzd | hzy | hzQ
    · exact hdV (hzd ▸ hPsub hzP)
    · exact hyP (hzy.symm ▸ hzP)
    · exact (Finset.disjoint_left.mp hPQ) hzP hzQ

/-- For distinct star centers and distinct completions, the pair-root graph
is intersecting in every admissible parent. -/
theorem cross_completion_pair_graph_intersecting
    {H : Family α} {V : Edge α} {c d x y : α}
    (hH : Admissible H) (hcd : c ≠ d)
    (hcV : c ∉ V) (hdV : d ∉ V)
    (hxV : x ∈ V) (hyV : y ∈ V) (hxy : x ≠ y) :
    PairwiseIntersecting (crossCompletionPairGraph H V c d x y) := by
  classical
  intro P Q hP hQ hPQne
  by_contra hMeet
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro z hzP hzQ
    apply hMeet
    exact ⟨z, Finset.mem_inter.mpr ⟨hzP, hzQ⟩⟩
  have hPspec := Finset.mem_filter.mp hP
  have hQspec := Finset.mem_filter.mp hQ
  have hPcard := (Finset.mem_powersetCard.mp hPspec.1).2
  have hQcard := (Finset.mem_powersetCard.mp hQspec.1).2
  have hPsub := (Finset.mem_powersetCard.mp hPspec.1).1
  have hQsub := (Finset.mem_powersetCard.mp hQspec.1).1
  have hPLx := Finset.mem_filter.mp hPspec.2.1
  have hPLy := Finset.mem_filter.mp hPspec.2.2
  have hQLx := Finset.mem_filter.mp hQspec.2.1
  have hQLy := Finset.mem_filter.mp hQspec.2.2
  have hxP : x ∉ P := by
    intro hmem
    simp [Finset.insert_eq_of_mem hmem] at hPLx
    omega
  have hyP : y ∉ P := by
    intro hmem
    simp [Finset.insert_eq_of_mem hmem] at hPLy
    omega
  have hxQ : x ∉ Q := by
    intro hmem
    simp [Finset.insert_eq_of_mem hmem] at hQLx
    omega
  have hyQ : y ∉ Q := by
    intro hmem
    simp [Finset.insert_eq_of_mem hmem] at hQLy
    omega
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hPneQ : P ≠ Q := pair_roots_ne_of_disjoint hPQ hPne
  have hQneP : Q ≠ P := pair_roots_ne_of_disjoint hPQ.symm hQne
  let A := liftedStarFacet c x P
  let B := liftedStarFacet d y Q
  let C := liftedStarFacet c x Q
  let D := liftedStarFacet d y P
  have hA : A ∈ H := by
    simpa [A, liftedStarFacet] using hPLx.2
  have hB : B ∈ H := by
    simpa [B, liftedStarFacet] using hQLy.2
  have hC : C ∈ H := by
    simpa [C, liftedStarFacet] using hQLx.2
  have hD : D ∈ H := by
    simpa [D, liftedStarFacet] using hPLy.2
  have hAB : Disjoint A B :=
    lifted_facets_disjoint hPQ hPsub hQsub hxV hyV hxQ hyP hxy hcV hdV hcd
  have hCD : Disjoint C D :=
    lifted_facets_disjoint hPQ.symm hQsub hPsub hxV hyV hxP hyQ hxy
      hcV hdV hcd
  have hAC : A ≠ C := by
    exact lifted_facets_same_center_ne hPsub hQsub hcV hxV hxP hxQ hPneQ
  have hBD : B ≠ D := by
    exact lifted_facets_same_center_ne hQsub hPsub hdV hyV hyQ hyP hQneP
  have hCross (E F : Edge α) (hEc : c ∈ E) (hFc : c ∉ F) : E ≠ F := by
    intro hEq
    exact hFc (hEq ▸ hEc)
  have hCrossD (E F : Edge α) (hEd : d ∈ E) (hFd : d ∉ F) : E ≠ F := by
    intro hEq
    exact hFd (hEq ▸ hEd)
  have hcA : c ∈ A := by simp [A, liftedStarFacet]
  have hcB : c ∉ B := by
    have hSupport : c ∉ insert y Q := by
      intro h
      rcases Finset.mem_insert.mp h with hcy | hcQ
      · exact hcV (hcy ▸ hyV)
      · exact hcV (hQsub hcQ)
    simp only [B, liftedStarFacet, Finset.mem_insert]
    intro h
    rcases h with hcd' | hSupport'
    · exact hcd hcd'
    · rcases hSupport' with hcy | hcQ
      · exact hcV (hcy ▸ hyV)
      · exact hcV (hQsub hcQ)
  have hcD : c ∉ D := by
    have hSupport : c ∉ insert y P := by
      intro h
      rcases Finset.mem_insert.mp h with hcy | hcP
      · exact hcV (hcy ▸ hyV)
      · exact hcV (hPsub hcP)
    simp only [D, liftedStarFacet, Finset.mem_insert]
    intro h
    rcases h with hcd' | hSupport'
    · exact hcd hcd'
    · rcases hSupport' with hcy | hcP
      · exact hcV (hcy ▸ hyV)
      · exact hcV (hPsub hcP)
  have hcC : c ∈ C := by simp [C, liftedStarFacet]
  have hdB : d ∈ B := by simp [B, liftedStarFacet]
  have hdC : d ∉ C := by
    have hSupport : d ∉ insert x Q := by
      intro h
      rcases Finset.mem_insert.mp h with hdx | hdQ
      · exact hdV (hdx ▸ hxV)
      · exact hdV (hQsub hdQ)
    simp only [C, liftedStarFacet, Finset.mem_insert]
    intro h
    rcases h with hdc' | hSupport'
    · exact hcd.symm hdc'
    · rcases hSupport' with hdx | hdQ
      · exact hdV (hdx ▸ hxV)
      · exact hdV (hQsub hdQ)
  have hdD : d ∈ D := by simp [D, liftedStarFacet]
  have hDistinct : FourDistinct A B C D := by
    refine ⟨hCross A B hcA hcB, hAC, hCross A D hcA hcD,
      hCrossD B C hdB hdC, hBD, hCross C D hcC hcD⟩
  have hUnion : A ∪ B = C ∪ D := by
    ext z
    simp [A, B, C, D, liftedStarFacet, or_left_comm, or_comm]
  exact hH hA hB hC hD ⟨hDistinct, hAB, hCD, hUnion⟩

/-- The Rank-three finite pair-graph classification applies to the actual
cross-completion graph: it is a star, or it has at most three roots. -/
theorem cross_completion_pair_graph_star_or_small
    {H : Family α} {V : Edge α} {c d x y : α}
    (hH : Admissible H) (hcd : c ≠ d)
    (hcV : c ∉ V) (hdV : d ∉ V)
    (hxV : x ∈ V) (hyV : y ∈ V) (hxy : x ≠ y) :
    (∃ z : α, ∀ P ∈ crossCompletionPairGraph H V c d x y, z ∈ P) ∨
      (crossCompletionPairGraph H V c d x y).card ≤ 3 := by
  have hIntersect := cross_completion_pair_graph_intersecting
    hH hcd hcV hdV hxV hyV hxy
  have hMeet : ∀ P ∈ crossCompletionPairGraph H V c d x y,
      ∀ Q ∈ crossCompletionPairGraph H V c d x y, ¬ Disjoint P Q := by
    intro P hP Q hQ hDisj
    by_cases hEq : P = Q
    · subst Q
      have hpos : 0 < P.card := by
        have hcard := (Finset.mem_powersetCard.mp
          (Finset.mem_filter.mp hP).1).2
        omega
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
      exact (Finset.disjoint_left.mp hDisj) hz hz
    · obtain ⟨z, hz⟩ := hIntersect hP hQ hEq
      exact (Finset.disjoint_left.mp hDisj)
        (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2
  apply JSP523.Rank3.intersecting_pair_graph_star_or_small
    (crossCompletionPairGraph H V c d x y)
  · intro P hP
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  · exact hMeet

private theorem pair_eq_pair_containing_vertex
    {P : Edge α} {z : α} (hP : P.card = 2) (hz : z ∈ P) :
    ∃ w : α, w ≠ z ∧ P = ({z, w} : Edge α) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hza | hzb
  · subst a
    exact ⟨b, hab.symm, rfl⟩
  · subst b
    exact ⟨a, hab, Finset.pair_comm a z⟩

/-- The classification bounds each distinct-completion root graph linearly
in the ground set size: a star has at most `|V|` roots, and the triangle
alternative has at most three. -/
theorem cross_completion_pair_graph_card_le
    {H : Family α} {V : Edge α} {c d x y : α}
    (hH : Admissible H) (hcd : c ≠ d)
    (hcV : c ∉ V) (hdV : d ∉ V)
    (hxV : x ∈ V) (hyV : y ∈ V) (hxy : x ≠ y)
    (hVcard : 3 ≤ V.card) :
    (crossCompletionPairGraph H V c d x y).card ≤ V.card := by
  classical
  rcases cross_completion_pair_graph_star_or_small
      hH hcd hcV hdV hxV hyV hxy with hStar | hSmall
  · obtain ⟨z, hStar⟩ := hStar
    by_cases hGraph : (crossCompletionPairGraph H V c d x y).Nonempty
    · obtain ⟨P, hP⟩ := hGraph
      have hPspec := Finset.mem_filter.mp hP
      have hPsub := (Finset.mem_powersetCard.mp hPspec.1).1
      have hzV : z ∈ V := hPsub (hStar P hP)
      let S := (V.erase z).image fun w => ({z, w} : Edge α)
      have hSub : crossCompletionPairGraph H V c d x y ⊆ S := by
        intro Q hQ
        have hQspec := Finset.mem_filter.mp hQ
        have hQcard := (Finset.mem_powersetCard.mp hQspec.1).2
        have hQsub := (Finset.mem_powersetCard.mp hQspec.1).1
        obtain ⟨w, hwz, hEq⟩ := pair_eq_pair_containing_vertex hQcard (hStar Q hQ)
        have hwV : w ∈ V := by
          have hwQ : w ∈ Q := by rw [hEq]; simp
          exact hQsub hwQ
        have hwErase : w ∈ V.erase z := Finset.mem_erase.mpr ⟨hwz, hwV⟩
        change Q ∈ (V.erase z).image fun w => ({z, w} : Edge α)
        exact Finset.mem_image.mpr ⟨w, hwErase, hEq.symm⟩
      calc
        _ ≤ S.card := Finset.card_le_card hSub
        _ ≤ (V.erase z).card := Finset.card_image_le
        _ ≤ V.card := Finset.card_erase_le
    · have hEmpty : crossCompletionPairGraph H V c d x y = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hGraph
      simp [hEmpty]
  · omega

/-- Summing the pair-root graphs over all ordered distinct completion pairs
gives a cubic finite bound.  This is the distinct-completion contribution
needed in the cross-moment estimate. -/
theorem sum_distinct_cross_completion_graphs_card_le_cube
    {H : Family α} {V : Edge α} {c d : α}
    (hH : Admissible H) (hcd : c ≠ d)
    (hcV : c ∉ V) (hdV : d ∉ V)
    (hVcard : 6 ≤ V.card) :
    (∑ x ∈ V, ∑ y ∈ V.erase x,
      (crossCompletionPairGraph H V c d x y).card) ≤ V.card ^ 3 := by
  calc
    (∑ x ∈ V, ∑ y ∈ V.erase x,
        (crossCompletionPairGraph H V c d x y).card) ≤
      ∑ x ∈ V, ∑ y ∈ V.erase x, V.card := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        apply cross_completion_pair_graph_card_le hH hcd hcV hdV hx
        · exact (Finset.mem_erase.mp hy).2
        · exact Ne.symm (Finset.mem_erase.mp hy).1
        · omega
    _ ≤ ∑ x ∈ V, V.card * V.card := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [Finset.sum_const]
      change (V.erase x).card * V.card ≤ V.card * V.card
      exact Nat.mul_le_mul_right V.card
        (Finset.card_erase_le (s := V) (a := x))
    _ = V.card ^ 3 := by
      simp [Finset.sum_const, Nat.pow_succ, Nat.mul_assoc]

/-- An explicit finite form of (III.A.18): the equal-completion term is at
most three times the number of ground triples, and the distinct-completion
term is at most `|V|^3`. -/
theorem rank_four_star_cross_moment_le
    {H : Family α} {V : Edge α} {c d : α}
    (hH : Admissible H) (hcd : c ≠ d)
    (hcV : c ∉ V) (hdV : d ∉ V)
    (hVcard : 6 ≤ V.card) :
    (∑ P ∈ V.powersetCard 2,
      linkPairDegree (rankFourStarLink H V c) P *
        linkPairDegree (rankFourStarLink H V d) P) ≤
      V.card ^ 3 + 3 * V.card.choose 3 := by
  let J := rankFourStarLink H V c ∩ rankFourStarLink H V d
  have hJsub : J ⊆ V.powersetCard 3 := by
    intro T hT
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hT).1).1
  have hJcard : J.card ≤ V.card.choose 3 := by
    calc
      J.card ≤ (V.powersetCard 3).card := Finset.card_le_card hJsub
      _ = V.card.choose 3 := by simp
  have hDistinct := sum_distinct_cross_completion_graphs_card_le_cube
    hH hcd hcV hdV hVcard
  rw [rank_four_star_cross_moment_exact]
  calc
    3 * J.card +
        ∑ x ∈ V, ∑ y ∈ V.erase x,
          (crossCompletionPairGraph H V c d x y).card
        ≤ 3 * V.card.choose 3 + V.card ^ 3 :=
          Nat.add_le_add (Nat.mul_le_mul_left 3 hJcard) hDistinct
    _ = V.card ^ 3 + 3 * V.card.choose 3 := Nat.add_comm _ _

/-- Finite owner-cleaning consequence of (III.A.18). For `h` distinct star
centres outside `V`, the square of the total number of deleted link triples
is at most `|∂₂V| h(h−1) (u^3 + 3 choose(u,3))`. This is the finite
`O(h u^(5/2))` estimate before taking square roots. -/
theorem rank_four_star_owner_cleaning_loss_sq_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {H : Family α} {V : Edge α} (centers : ι → α)
    (hH : Admissible H)
    (hInjective : Function.Injective centers)
    (hOutside : ∀ i, centers i ∉ V)
    (hVcard : 6 ≤ V.card) :
    (∑ i : ι,
      (rankFourStarLink H V (centers i) \ pairOwnerCleanedLink
        (fun j => rankFourStarLink H V (centers j))
        (maximumDegreePairOwner (fun j => rankFourStarLink H V (centers j))) i).card) ^ 2 ≤
      (V.powersetCard 2).card *
        ((Fintype.card ι * (Fintype.card ι - 1)) *
          (V.card ^ 3 + 3 * V.card.choose 3)) := by
  let L : ι → Family α := fun i => rankFourStarLink H V (centers i)
  have hGround : ∀ i T, T ∈ L i → T ∈ V.powersetCard 3 := by
    intro i T hT
    exact (Finset.mem_filter.mp hT).1
  have hOwnerMax : ∀ P ∈ V.powersetCard 2, ∀ i,
      starLinkPairDegree L i P ≤ starLinkPairDegree L (maximumDegreePairOwner L P) P := by
    intro P hP i
    exact maximumDegreePairOwner_spec L P i
  have hMoment : ∀ i j, i ≠ j →
      (∑ P ∈ V.powersetCard 2,
        starLinkPairDegree L i P * starLinkPairDegree L j P) ≤
          V.card ^ 3 + 3 * V.card.choose 3 := by
    intro i j hij
    have hcd : centers i ≠ centers j := by
      intro heq
      exact hij (hInjective heq)
    have h := rank_four_star_cross_moment_le hH hcd
      (hOutside i) (hOutside j) hVcard
    simpa [L, linkPairDegree, starLinkPairDegree] using h
  have hBound := maximum_pair_owner_cleaning_loss_sq_le_uniform_pair_moment
    L (maximumDegreePairOwner L) V hGround hOwnerMax
      (V.card ^ 3 + 3 * V.card.choose 3) hMoment
  simpa [L] using hBound

end JSP523.Rank4
