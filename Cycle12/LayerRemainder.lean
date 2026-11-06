import Cycle12.VariableScaleLayers

namespace Cycle12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem assigned_union_degree (L : List (AssignedPiece V)) {D : ℝ}
    (h : ∀ P∈L, 2*(edgeCount P.graph:ℝ)≤D*P.vertices.card) :
    2*(edgeCount (graphUnion (L.map AssignedPiece.graph)):ℝ)≤D*vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    have hp := h P (by simp)
    have ht := ih (fun Q hQ => h Q (by simp [hQ]))
    have he : (edgeCount (P.graph ⊔ graphUnion (L.map AssignedPiece.graph)):ℝ) ≤
        edgeCount P.graph+edgeCount (graphUnion (L.map AssignedPiece.graph)) := by
      exact_mod_cast edgeCount_sup_le P.graph (graphUnion (L.map AssignedPiece.graph))
    simp only [List.map_cons,graphUnion_cons,vertexMass_cons]
    nlinarith only [hp,ht,he]

theorem partition_merge_remainder {G : SimpleGraph V} {C L : List (SimpleGraph V)}
    (hp : GraphPartition G (C++L)) : GraphPartition G (C++[graphUnion L]) := by
  have hle : ∀ x y, edgeOccurrences L x y≤1 := by
    intro x y
    have hh := hp x y
    rw [edgeOccurrences_append] at hh
    split_ifs at hh <;> omega
  have hL := graphPartition_of_le_one L hle
  intro x y
  have hh := hp x y
  simp only [edgeOccurrences_append,edgeOccurrences_cons,edgeOccurrences_nil,Nat.add_zero]
  rw [edgeOccurrences_append,hL x y] at hh
  exact hh

/-- The terminal remainder is the entire frontier at a chosen earlier
stage. Its degree bound is taken from that frontier's actual edge set. -/
theorem stopped_layer_partition (s : SplitSystem V) (j k : ℕ) (P : AssignedPiece V) :
    GraphPartition P.graph
      (pastCycles s j k [P] ++ (pastPieces s j k [P]).map AssignedPiece.graph ++
        [graphUnion ((advance s j k [P]).map AssignedPiece.graph)]) :=
  partition_merge_remainder (past_partition s j k P)

theorem stopped_remainder_degree (s : SplitSystem V) (j k : ℕ) (P : AssignedPiece V)
    {D M : ℝ} (hD : 0≤D)
    (hdeg : ∀ Q∈advance s j k [P], 2*(edgeCount Q.graph:ℝ)≤D*Q.vertices.card)
    (hmass : vertexMass (advance s j k [P])≤M*P.vertices.card) :
    2*(edgeCount (graphUnion ((advance s j k [P]).map AssignedPiece.graph)):ℝ)≤
      (D*M)*P.vertices.card := by
  have hh := assigned_union_degree (advance s j k [P]) hdeg
  have hm := mul_le_mul_of_nonneg_left hmass hD
  nlinarith only [hh,hm]

end
end Cycle12
