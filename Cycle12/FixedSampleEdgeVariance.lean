import Cycle12.FixedChooseMoments
import Cycle12.DeCaenDegree

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The missing-edge factor is retained: the bound is zero for complete
graphs. The random variable is the actual retained edge count. -/
theorem fixed_sample_edge_variance_bound (G : SimpleGraph V)
    (hn : 4≤Fintype.card V) {k : ℕ} (hk : k≤Fintype.card V) :
    (fixedSizeLaw (univ:Finset V) k).expect
      (fun S => ((sampledFinsetEdgeCount G S:ℝ)-
        (Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2)^2) ≤
      fixedEdgeVarianceCap (Fintype.card V) k (Fintype.card G.edgeSet) := by
  rw [fixed_sample_edge_variance_identity G hk,← fixed_variance_cap_algebra _ k hn]
  have hd := de_caen_degree_square_bound G (by omega)
  have hm := mul_le_mul_of_nonneg_right hd
    (sub_nonneg.mpr (fixed_choose_ratio_three_ge_four (Fintype.card V) k hn hk))
  linarith

theorem fixed_sample_edge_variance_cap_nonneg (G : SimpleGraph V)
    (hn : 4≤Fintype.card V) {k : ℕ} (hk : k≤Fintype.card V) :
    0≤fixedEdgeVarianceCap (Fintype.card V) k (Fintype.card G.edgeSet) :=
  (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)).trans
    (fixed_sample_edge_variance_bound G hn hk)

end
end Cycle12
