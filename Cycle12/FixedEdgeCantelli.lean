import Cycle12.FixedIncidentVariance

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_sample_edge_cantelli (G : SimpleGraph V) (hn : 4≤Fintype.card V)
    {k : ℕ} (hk : k≤Fintype.card V) (a : ℝ)
    (ha : a<(Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2) :
    (fixedSizeLaw (univ:Finset V) k).prob (fun S => (sampledFinsetEdgeCount G S:ℝ)≤a) ≤
      fixedEdgeVarianceCap (Fintype.card V) k (Fintype.card G.edgeSet)/
        (fixedEdgeVarianceCap (Fintype.card V) k (Fintype.card G.edgeSet)+
          ((Fintype.card G.edgeSet:ℝ)*fixedChooseRatio (Fintype.card V) k 2-a)^2) := by
  have hh := (fixedSizeLaw (univ:Finset V) k).cantelli_lower
    (fun S => (sampledFinsetEdgeCount G S:ℝ)) (fixed_sample_edge_mean G hk)
    (fixed_sample_edge_variance_bound G hn hk) (sub_pos.mpr ha)
  simpa only [sub_sub_cancel] using hh

theorem fixed_sample_incident_cantelli (G : SimpleGraph V) (hn : 4≤Fintype.card V)
    {k : ℕ} (hk : k≤Fintype.card V) (a : ℝ)
    (ha : a<(Fintype.card G.edgeSet:ℝ)*
      (1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2)) :
    (fixedSizeLaw (univ:Finset V) k).prob (fun S => (incidentEdgeCount G S:ℝ)≤a) ≤
      fixedEdgeVarianceCap (Fintype.card V) (Fintype.card V-k:ℕ) (Fintype.card G.edgeSet)/
        (fixedEdgeVarianceCap (Fintype.card V) (Fintype.card V-k:ℕ) (Fintype.card G.edgeSet)+
          ((Fintype.card G.edgeSet:ℝ)*(1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2)-a)^2) := by
  have hh := (fixedSizeLaw (univ:Finset V) k).cantelli_lower
    (fun S => (incidentEdgeCount G S:ℝ)) (fixed_sample_incident_edge_mean G hk)
    (fixed_sample_incident_variance_bound G hn hk) (sub_pos.mpr ha)
  simpa only [sub_sub_cancel] using hh

end
end Cycle12
