import Cycle12.CoverInduction
import Cycle12.RationalRoutedCase

namespace Cycle12
open SimpleGraph Real Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable

theorem irreducible_cover_of_rectangle
    (h : (⟨0,17/250,1,none⟩ : RatCoverRectangle).Sound) : IrreducibleCoverTheorem := by
  intro V _ _ G hn hm hx hI hdegree
  have hsize := twice_graph_edges_le_order_sq G
  have hm' : (0:ℝ) < Fintype.card G.edgeSet := by simpa only [Set.fintypeCard_eq_ncard] using hm
  have hs := sOf_ge_one hm' hsize
  refine h G hm' ?_ ?_ ?_ ?_ ?_ hI
  · simpa only [Rat.cast_zero] using (cover_graph_x_pos hn hm').le
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Set.fintypeCard_eq_ncard] using hx
  · simpa only [Rat.cast_one] using hs
  · intro u hu
    cases hu
  · simpa only [Set.fintypeCard_eq_ncard] using hdegree

end
end Cycle12
