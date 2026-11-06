import Cycle12.TerminalInductiveTemplates
import Cycle12.TerminalLocalMoves
import Cycle12.SixCycleIndependentClassification

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem triple_template_adjacency : ∀ i j : Fin 6,
    (TerminalCert.graph TerminalTemplates.edges1).Adj i j ↔
      (i.val < 3 ∧ 3 ≤ j.val) ∨ (3 ≤ i.val ∧ j.val < 3) := by decide +kernel

/-- Three vertices with the same three-element full neighborhood are
removed by one six-cycle and three single edges. The integer budget is exact. -/
theorem terminal_induction_three_spokes (G : SimpleGraph V)
    (ih : TerminalProperInduction G) (g : Fin 3 ↪ V) {x y z : V}
    (hx : ∀ i, x≠g i) (hy : ∀ i, y≠g i) (hz : ∀ i, z≠g i)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hX : ∀ v, G.Adj x v ↔ v=g 0 ∨ v=g 1 ∨ v=g 2)
    (hY : ∀ v, G.Adj y v ↔ v=g 0 ∨ v=g 1 ∨ v=g 2)
    (hZ : ∀ v, G.Adj z v ↔ v=g 0 ∨ v=g 1 ∨ v=g 2) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let f : Fin 6 ↪ V := ⟨![g 0,g 1,g 2,x,y,z],by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [g.injective.eq_iff,hx,hy,hz,hxy,hxz,hyz,eq_comm] at hij ⊢⟩
  apply terminal_neighborhood_induction G ih TerminalTemplates.edges1 TerminalTemplates.words1
    terminalRemoved1 (by decide +kernel) 0 (by decide +kernel) f TerminalTemplates.valid1
    (by decide +kernel) (by decide +kernel)
  intro i hi v
  fin_cases i <;> norm_num [terminalRemoved1] at hi
  · change G.Adj x v ↔ _
    rw [hX v]
    simp [triple_template_adjacency,Fin.exists_fin_succ,f,eq_comm] <;> rfl
  · change G.Adj y v ↔ _
    rw [hY v]
    simp [triple_template_adjacency,Fin.exists_fin_succ,f,eq_comm] <;> rfl
  · change G.Adj z v ↔ _
    rw [hZ v]
    simp [triple_template_adjacency,Fin.exists_fin_succ,f,eq_comm] <;> rfl

/-- Specialize the generic deletion to either alternating triple of the
six-cycle, with full neighborhoods supplied by the classification theorem. -/
theorem terminal_induction_three_alternating_spokes (G : SimpleGraph V)
    (ih : TerminalProperInduction G) (f : Fin 6 ↪ V) {i : Fin 11} (hi : 9 ≤ i.val)
    {x y z : V} (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hX : SixAttachmentVertex G f i x) (hY : SixAttachmentVertex G f i y)
    (hZ : SixAttachmentVertex G f i z) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have htriple : ∃ a b c : Fin 6, [a,b,c].Nodup ∧ sixAttachment i={a,b,c} := by
    have hh : ∀ i : Fin 11, 9 ≤ i.val →
        ∃ a b c : Fin 6, [a,b,c].Nodup ∧ sixAttachment i={a,b,c} := by decide +kernel
    exact hh i hi
  obtain ⟨a,b,c,hn,hset⟩ := htriple
  have hab : a≠b := by intro he; exact (List.nodup_cons.mp hn).1 (by simp [he])
  have hac : a≠c := by intro he; exact (List.nodup_cons.mp hn).1 (by simp [he])
  have hbc : b≠c := by intro he; exact (List.nodup_cons.mp hn.of_cons).1 (by simp [he])
  let g : Fin 3 ↪ V := ⟨![f a,f b,f c],by
    intro j k he
    fin_cases j <;> fin_cases k <;> simp [f.injective.eq_iff,hab,hac,hbc,eq_comm] at he ⊢⟩
  have hout : ∀ {v}, (∀ j, v≠f j) → ∀ j, v≠g j := by
    intro v hv j
    fin_cases j <;> first | exact hv a | exact hv b | exact hv c
  have hnear : ∀ {v}, SixAttachmentVertex G f i v →
      ∀ w, G.Adj v w ↔ w=g 0 ∨ w=g 1 ∨ w=g 2 := by
    intro v hv w
    rw [hv.2,hset]
    simp only [mem_insert,mem_singleton]
    change (∃ k, (k=a ∨ k=b ∨ k=c) ∧ f k=w) ↔ w=f a ∨ w=f b ∨ w=f c
    constructor
    · rintro ⟨k,(rfl | rfl | rfl),he⟩
      · exact Or.inl he.symm
      · exact Or.inr (Or.inl he.symm)
      · exact Or.inr (Or.inr he.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨a,Or.inl rfl,rfl⟩
      · exact ⟨b,Or.inr (Or.inl rfl),rfl⟩
      · exact ⟨c,Or.inr (Or.inr rfl),rfl⟩
  exact terminal_induction_three_spokes G ih g (hout hX.1) (hout hY.1) (hout hZ.1)
    hxy hxz hyz (hnear hX) (hnear hY) (hnear hZ)

end
end Cycle12
