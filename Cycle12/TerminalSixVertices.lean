import Cycle12.SixCoreTable
import Cycle12.SixCycleFrame
import Cycle12.TerminalNoSixCycle

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every graph on these six labels containing the cyclic base is one of
the 512 chord choices already checked in a single uniform certificate. -/
theorem terminal_six_labeled_cycle (G : SimpleGraph (Fin 6))
    (hcycle : ∀ i, G.Adj i (i+1)) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(6-1)+6*G.edgeSet.ncard := by
  let S : Finset (Fin 9) := univ.filter (fun i => sixCoreChord i∈G.edgeSet)
  have h01 := hcycle 0
  have h12 := hcycle 1
  have h23 := hcycle 2
  have h34 := hcycle 3
  have h45 := hcycle 4
  have h50 := hcycle 5
  have hmodel : G=TerminalCert.graph (sixCoreEdges S) := by
    have hspan : ∀ e : Sym2 (Fin 6), ¬e.IsDiag →
        e∈sixCoreBase ∨ ∃ i, sixCoreChord i=e := by decide +kernel
    have hbase : ∀ e∈sixCoreBase, e∈G.edgeSet := by
      intro e he
      simp only [sixCoreBase,mem_insert,mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h01
      · exact h50.symm
      · exact h12
      · exact h23
      · exact h34
      · exact h45
    apply SimpleGraph.edgeSet_injective
    rw [TerminalCert.edgeSet_graph _ (six_core_no_diagonal S)]
    ext e
    constructor
    · intro he
      have hndiag : ¬e.IsDiag := by
        induction e using Sym2.ind with
        | _ i j => exact (show G.Adj i j from he).ne
      rcases hspan e hndiag with hh | ⟨i,rfl⟩
      · exact Finset.mem_union.mpr (Or.inl hh)
      · apply Finset.mem_union.mpr ∘ Or.inr
        exact Finset.mem_image.mpr ⟨i,by simpa only [S,mem_filter,mem_univ,true_and] using he,rfl⟩
    · intro he
      rcases Finset.mem_union.mp he with hh | hh
      · exact hbase e hh
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hh
        exact (mem_filter.mp hi).2
  rw [hmodel]
  exact terminal_six_core_model S

/-- Closed affine terminal theorem for all graphs with at most six vertices. -/
theorem terminal_affine_card_le_six {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hn : Fintype.card V≤6) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  by_cases hshort : Cycle13.NoCycleAtLeast G 6
  · exact terminal_affine_no_six_cycle G hshort
  obtain ⟨u,c,hc,hlen⟩ : ∃ u, ∃ c : G.Walk u u, c.IsCycle ∧ c.length=6 := by
    by_contra hh
    apply hshort
    intro u c hc
    have hl := Cycle13.cycle_length_le_order hc
    have hne : c.length≠6 := fun he => hh ⟨u,c,hc,he⟩
    omega
  obtain ⟨f,hcycle,_⟩ := six_cycle_frame hc hlen
  have hsurj : Function.Surjective f := by
    by_contra hh
    have hcard := Fintype.card_lt_of_injective_not_surjective f f.injective hh
    simp only [Fintype.card_fin] at hcard
    omega
  apply terminal_affine_of_labeling G f hsurj
  simpa only [Fintype.card_fin] using terminal_six_labeled_cycle (G.comap f) hcycle

end
end Cycle12
