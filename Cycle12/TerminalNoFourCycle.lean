import Cycle12.TerminalBlockReduction
import Cycle12.SmallCircumferenceBlocks

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A closed special case of the terminal theorem: no cycle of length
four or more. The proof includes every order and every vertex separator. -/
theorem terminal_affine_no_four_cycle {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 4) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_blocks (threshold:=4) _ G hshort
  intro W _ _ H horder hconn hrobust hshort
  have hh := vertex_robust_no_four_cycle_order H hconn hrobust hshort
  omega

end
end Cycle12
