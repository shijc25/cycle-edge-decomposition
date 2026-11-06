import Cycle12.FixedSampleEdgeVariance
import Cycle12.FixedSampleComplement

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem incident_plus_complement_edges (G : SimpleGraph V) (S : Finset V) :
    incidentEdgeCount G S+sampledFinsetEdgeCount G (univ\S)=Fintype.card G.edgeSet := by
  let R : Finset G.edgeSet := univ.filter (fun e => edgeVertexSet G e⊆univ\S)
  have he : incidentSampleEdges G S=Rᶜ := by
    ext e
    simp only [incidentSampleEdges,R,mem_filter,mem_univ,true_and,mem_compl]
    constructor
    · rintro ⟨v,hvS,hve⟩ hsub
      exact (mem_sdiff.mp (hsub (by simpa [edgeVertexSet] using hve))).2 hvS
    · intro hsub
      obtain ⟨v,hve,hvnot⟩ := not_subset.mp hsub
      have hvS : v∈S := by simpa only [mem_sdiff,mem_univ,true_and,not_not] using hvnot
      exact ⟨v,hvS,by simpa [edgeVertexSet] using hve⟩
  change (incidentSampleEdges G S).card+R.card=Fintype.card G.edgeSet
  rw [he]
  exact card_compl_add_card R

theorem incident_complement_edges_real (G : SimpleGraph V) (S : Finset V) :
    (incidentEdgeCount G S:ℝ)=(Fintype.card G.edgeSet:ℝ)-(sampledFinsetEdgeCount G (univ\S):ℝ) := by
  have hh : (incidentEdgeCount G S:ℝ)+(sampledFinsetEdgeCount G (univ\S):ℝ)=
      (Fintype.card G.edgeSet:ℝ) := by exact_mod_cast incident_plus_complement_edges G S
  linarith

theorem fixed_sample_incident_edge_mean (G : SimpleGraph V) {k : ℕ} (hk : k≤Fintype.card V) :
    (fixedSizeLaw (univ:Finset V) k).expect (fun S => (incidentEdgeCount G S:ℝ))=
      (Fintype.card G.edgeSet:ℝ)*(1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2) := by
  simp_rw [incident_complement_edges_real]
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_const,
    fixed_size_complement_expect (univ:Finset V) (by simpa using hk)
      (fun S => (sampledFinsetEdgeCount G S:ℝ))]
  simp only [card_univ]
  rw [fixed_sample_edge_mean G (Nat.sub_le _ _)]
  ring

theorem fixed_sample_incident_variance_bound (G : SimpleGraph V)
    (hn : 4≤Fintype.card V) {k : ℕ} (hk : k≤Fintype.card V) :
    (fixedSizeLaw (univ:Finset V) k).expect
      (fun S => ((incidentEdgeCount G S:ℝ)-(Fintype.card G.edgeSet:ℝ)*
        (1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2))^2) ≤
      fixedEdgeVarianceCap (Fintype.card V) (Fintype.card V-k:ℕ) (Fintype.card G.edgeSet) := by
  have hh := fixed_sample_edge_variance_bound G hn (Nat.sub_le (Fintype.card V) k)
  have hc := fixed_size_complement_expect (univ:Finset V) (by simpa using hk)
    (fun S => ((sampledFinsetEdgeCount G S:ℝ)-(Fintype.card G.edgeSet:ℝ)*
      fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2)^2)
  simp only [card_univ] at hc
  rw [← hc] at hh
  convert hh using 1
  apply congrArg (FiniteLaw.expect _)
  funext S
  rw [incident_complement_edges_real]
  ring

end
end Cycle12
