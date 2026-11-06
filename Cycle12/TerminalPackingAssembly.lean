import Cycle12.AssignedPackingAssembly
import Cycle12.TerminalLayerBounds12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Assemble the retained long cycles, the completed core pieces, and the
entire stopped remainder. All costs are for actual edge-disjoint packings. -/
theorem terminal_packing_assembly {G H : SimpleGraph V}
    (C : List (SimpleGraph V)) (R : List (AssignedPiece V))
    (hp : GraphPartition G (C++R.map AssignedPiece.graph++[H]))
    (hC : ∀ K∈C, IsCycleGraph K) {K T : ℝ}
    (hR : ∀ P∈R, ∃ Q : CyclePacking P.graph, Q.weight≤K*P.vertices.card)
    (PH : CyclePacking H) (hH : PH.weight≤T) :
    ∃ Q : CyclePacking G, Q.weight≤(C.length:ℝ)+K*vertexMass R+T := by
  have hpC : GraphPartition (graphUnion C) C := partition_segment (A:=[])
    (C:=R.map AssignedPiece.graph++[H]) (by simpa only [List.nil_append,List.append_assoc] using hp)
  have hpR : GraphPartition (graphUnion (R.map AssignedPiece.graph)) (R.map AssignedPiece.graph) :=
    partition_segment hp
  obtain ⟨PC,hPC⟩ := partition_packing_bound hpC (fun _ => (1:ℝ)) (by
    intro J hJ
    obtain ⟨PJ,hPJ⟩ := cycle_graph_packing (hC J hJ)
    exact ⟨PJ,hPJ.le⟩)
  have hPC' : PC.weight≤(C.length:ℝ) := by simpa using hPC
  obtain ⟨PR,hPR⟩ := assigned_partition_packing_bound R hpR hR
  have hthree : GraphPartition G [graphUnion C,graphUnion (R.map AssignedPiece.graph),H] := by
    simpa only [graphUnion_cons,graphUnion_nil,sup_bot_eq] using partition_three_groups hp
  obtain ⟨Q,hQ⟩ := three_packing_bound hthree PC PR PH
  refine ⟨Q,?_⟩
  rw [hQ]
  linarith only [hPC',hPR,hH]

end
end Cycle12

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ScaleLayers12.terminal_packing {G : SimpleGraph V} (L : ScaleLayers12 G)
    {K T : ℝ}
    (hR : ∀ P∈pastPieces L.splitter 0 (L.stopIndex+1) [originalPiece G],
      ∃ Q : CyclePacking P.graph, Q.weight≤K*P.vertices.card)
    (PH : CyclePacking (stoppedRemainder L)) (hH : PH.weight≤T) :
    ∃ Q : CyclePacking G, Q.weight≤
      ((pastCycles L.splitter 0 (L.stopIndex+1) [originalPiece G]).length:ℝ)+
      K*vertexMass (pastPieces L.splitter 0 (L.stopIndex+1) [originalPiece G])+T := by
  exact terminal_packing_assembly _ _ (L.stopped_partition (L.stopIndex+1))
    (pastCycles_good L.splitter 0 (L.stopIndex+1) [originalPiece G]) hR PH hH

end
end Cycle12.Global12
