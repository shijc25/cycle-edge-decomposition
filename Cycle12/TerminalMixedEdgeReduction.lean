import Cycle12.TerminalMixedEdgeTemplates
import Cycle12.SixCycleMatchingClassification

namespace Cycle12
open SimpleGraph Finset
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem terminal_induction_mixed_pair_neighborhoods (G : SimpleGraph V)
    (ih : TerminalProperInduction G) (f : Fin 6 ↪ V)
    (h20 : G.Adj (f 2) (f 0)) (h31 : G.Adj (f 3) (f 1))
    (h40 : G.Adj (f 4) (f 0)) (h51 : G.Adj (f 5) (f 1))
    (h2 : ∀ v, G.Adj (f 2) v ↔ v=f 3 ∨
      (v=f 0 ∧ G.Adj (f 2) (f 0)) ∨ (v=f 1 ∧ G.Adj (f 2) (f 1)))
    (h3 : ∀ v, G.Adj (f 3) v ↔ v=f 2 ∨
      (v=f 0 ∧ G.Adj (f 3) (f 0)) ∨ (v=f 1 ∧ G.Adj (f 3) (f 1)))
    (h4 : ∀ v, G.Adj (f 4) v ↔ v=f 5 ∨
      (v=f 0 ∧ G.Adj (f 4) (f 0)) ∨ (v=f 1 ∧ G.Adj (f 4) (f 1)))
    (h5 : ∀ v, G.Adj (f 5) v ↔ v=f 4 ∨
      (v=f 0 ∧ G.Adj (f 5) (f 0)) ∨ (v=f 1 ∧ G.Adj (f 5) (f 1))) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let S : Finset (Fin 4) := univ.filter
    (fun i => ![G.Adj (f 1) (f 2),G.Adj (f 0) (f 3),G.Adj (f 1) (f 4),G.Adj (f 0) (f 5)] i)
  apply terminal_induction_mixed_pair G ih S f
  intro i hi v
  fin_cases i <;> norm_num [mixedPairRemoved] at hi
  all_goals first
    | (change G.Adj (f 2) v ↔ _; rw [h2 v])
    | (change G.Adj (f 3) v ↔ _; rw [h3 v])
    | (change G.Adj (f 4) v ↔ _; rw [h4 v])
    | (change G.Adj (f 5) v ↔ _; rw [h5 v])
  all_goals
    simp [mixedPairEdges,mixedPairBase,mixedPairOptional,S,TerminalCert.graph,
      SimpleGraph.fromEdgeSet_adj,Finset.mem_image,Fin.exists_fin_succ,Sym2.eq_iff,
      h20,h31,h40,h51,G.adj_comm,eq_comm] <;> tauto

theorem six_edge_component_symm {G : SimpleGraph V} {f : Fin 6 ↪ V} {x y : V}
    (h : SixEdgeComponent G f x y) : SixEdgeComponent G f y x := by
  refine ⟨h.2.1,h.1,h.2.2.1.symm,?_,h.2.2.2.2.2,h.2.2.2.2.1⟩
  rcases h.2.2.2.1 with h | h
  · exact Or.inr h.symm
  · exact Or.inl h.symm

theorem terminal_induction_oriented_edge_pair (G : SimpleGraph V)
    (ih : TerminalProperInduction G) (g : Fin 6 ↪ V) {x y z w : V}
    (hxy : SixEdgeComponent G g x y) (hzw : SixEdgeComponent G g z w)
    (hn : [x,y,z,w].Nodup)
    (hx0 : G.Adj x (g 0)) (hy3 : G.Adj y (g 3))
    (hz0 : G.Adj z (g 0)) (hw3 : G.Adj w (g 3)) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hx := hxy.1
  have hy := hxy.2.1
  have hz := hzw.1
  have hw := hzw.2.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true,or_false] at hn
  obtain ⟨⟨hxy',hxz,hxw⟩,⟨hyz,hyw⟩,hzw'⟩ := hn
  let f : Fin 6 ↪ V := ⟨![g 0,g 3,x,y,z,w],by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [g.injective.eq_iff,hx,hy,hz,hw,hxy',hxz,hxw,hyz,hyw,hzw',eq_comm] at hij ⊢⟩
  exact terminal_induction_mixed_pair_neighborhoods G ih f hx0 hy3 hz0 hw3
    hxy.2.2.2.2.1 hxy.2.2.2.2.2 hzw.2.2.2.2.1 hzw.2.2.2.2.2

/-- Any two exterior edge components with common hubs can be deleted
together, even when their types and orientations differ. -/
theorem terminal_induction_two_edge_components (G : SimpleGraph V)
    (ih : TerminalProperInduction G) (g : Fin 6 ↪ V) {x y z w : V}
    (hxy : SixEdgeComponent G g x y) (hzw : SixEdgeComponent G g z w)
    (hn : [x,y,z,w].Nodup) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hn₁ : [x,y,w,z].Nodup :=
    (List.Perm.cons x (List.Perm.cons y (List.Perm.swap w z []))).nodup_iff.mp hn
  have hn₂ : [y,x,z,w].Nodup := (List.Perm.swap y x [z,w]).nodup_iff.mp hn
  have hn₃ : [y,x,w,z].Nodup := (List.Perm.swap y x [w,z]).nodup_iff.mp hn₁
  rcases hxy.2.2.2.1 with ⟨hx0,hy3⟩ | ⟨hx3,hy0⟩
  · rcases hzw.2.2.2.1 with ⟨hz0,hw3⟩ | ⟨hz3,hw0⟩
    · exact terminal_induction_oriented_edge_pair G ih g hxy hzw hn hx0 hy3 hz0 hw3
    · exact terminal_induction_oriented_edge_pair G ih g hxy (six_edge_component_symm hzw)
        hn₁ hx0 hy3 hw0 hz3
  · rcases hzw.2.2.2.1 with ⟨hz0,hw3⟩ | ⟨hz3,hw0⟩
    · exact terminal_induction_oriented_edge_pair G ih g (six_edge_component_symm hxy) hzw
        hn₂ hy0 hx3 hz0 hw3
    · exact terminal_induction_oriented_edge_pair G ih g (six_edge_component_symm hxy)
        (six_edge_component_symm hzw) hn₃ hy0 hx3 hw0 hz3

end
end Cycle12
