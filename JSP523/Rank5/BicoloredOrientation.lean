import JSP523.Rank5.ColorCleanSamples

/-! # Orienting a bicolored support at its repeated-color vertex -/

namespace JSP523.Rank5

variable {α κ : Type*} [DecidableEq α] [DecidableEq κ]

theorem bicolored_support_has_repeated_orientation
    (edgeColor : Finset α → Option κ) {T : Finset α} (hTc : T.card = 3)
    (hBi : IsBicoloredTriangleSupport edgeColor T) :
    ∃ x y z : α, ∃ c d : κ,
      T = {x,y,z} ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ c ≠ d ∧
      edgeColor {x,y} = some c ∧ edgeColor {x,z} = some c ∧ edgeColor {y,z} = some d := by
  obtain ⟨x,y,z,hxy,hxz,hyz,hT⟩ := Finset.card_eq_three.mp hTc
  obtain ⟨c,d,hcd,⟨eC,heC,hC⟩,⟨eD,heD,hD⟩,hColors⟩ := hBi
  have hEdges : triangleEdgeSupports T = {{x,y},{x,z},{y,z}} := by
    rw [hT]
    exact triangle_pair_supports hxy hxz hyz
  have hNotMono : ∀ k : κ, ¬ (edgeColor {x,y} = some k ∧
      edgeColor {x,z} = some k ∧ edgeColor {y,z} = some k) := by
    intro k h
    have hAll : ∀ e ∈ triangleEdgeSupports T, edgeColor e = some k := by
      intro e he
      rw [hEdges] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    have hkc : k = c := Option.some.inj ((hAll eC heC).symm.trans hC)
    have hkd : k = d := Option.some.inj ((hAll eD heD).symm.trans hD)
    exact hcd (hkc.symm.trans hkd)
  have hXY := hColors {x,y} (by rw [hEdges]; simp)
  have hXZ := hColors {x,z} (by rw [hEdges]; simp)
  have hYZ := hColors {y,z} (by rw [hEdges]; simp)
  have hTy : T = {y,x,z} := by rw [hT, Finset.insert_comm]
  have hTz : T = {z,x,y} := by
    rw [hT]
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rcases hXY with hXY | hXY <;> rcases hXZ with hXZ | hXZ <;> rcases hYZ with hYZ | hYZ
  · exact False.elim (hNotMono c ⟨hXY,hXZ,hYZ⟩)
  · exact ⟨x,y,z,c,d,hT,hxy,hxz,hyz,hcd,hXY,hXZ,hYZ⟩
  · exact ⟨y,x,z,c,d,hTy,hxy.symm,hyz,hxz,hcd,
      by rw [Finset.pair_comm]; exact hXY, hYZ,hXZ⟩
  · exact ⟨z,x,y,d,c,hTz,hxz.symm,hyz.symm,hxy,hcd.symm,
      by rw [Finset.pair_comm]; exact hXZ,
      by rw [Finset.pair_comm]; exact hYZ, hXY⟩
  · exact ⟨z,x,y,c,d,hTz,hxz.symm,hyz.symm,hxy,hcd,
      by rw [Finset.pair_comm]; exact hXZ,
      by rw [Finset.pair_comm]; exact hYZ, hXY⟩
  · exact ⟨y,x,z,d,c,hTy,hxy.symm,hyz,hxz,hcd.symm,
      by rw [Finset.pair_comm]; exact hXY, hYZ,hXZ⟩
  · exact ⟨x,y,z,d,c,hT,hxy,hxz,hyz,hcd.symm,hXY,hXZ,hYZ⟩
  · exact False.elim (hNotMono d ⟨hXY,hXZ,hYZ⟩)

end JSP523.Rank5
