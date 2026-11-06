import Cycle12.FourCycleClassification
import Cycle12.TerminalFourVertices
import Cycle12.TerminalTwoHubs

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Closed terminal theorem for circumference at most four, including all
orders and all vertex separators. The block classification is proved here. -/
theorem terminal_affine_no_five_cycle {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 5) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_blocks (threshold:=5) _ G hshort
  intro W _ _ H horder hconn hrobust hshort
  letI : Nonempty W := hconn.nonempty
  by_cases hsmall : Fintype.card W ≤ 4
  · exact terminal_affine_card_le_four H hsmall
  · obtain ⟨a,b,hab,hshape⟩ :=
      vertex_robust_no_five_cycle_two_hubs H hconn hrobust hshort (by omega)
    exact terminal_affine_two_hubs H a b hab hshape

/-- Exact rank form of the closed no-five-cycle terminal theorem. Empty
graphs, isolated vertices and arbitrary disconnected graphs are included. -/
theorem terminal_rank_no_five_cycle {V : Type} [Fintype V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 5) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-Cycle13.componentCount G)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_components G
  intro c
  have : Nonempty c := c.connected_toSimpleGraph.nonempty
  have hc : Cycle13.NoCycleAtLeast c.toSimpleGraph 5 := by
    intro v p hp
    have hh := hshort v.val (p.map c.toSimpleGraph_hom) (hp.map Subtype.val_injective)
    erw [Walk.length_map] at hh
    exact hh
  exact terminal_affine_no_five_cycle c.toSimpleGraph hc

end
end Cycle12
