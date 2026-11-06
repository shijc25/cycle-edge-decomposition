import Cycle12.SupportedParityForest12
import Cycle12.PartitionParityTransfer12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def parityPiece (F : AssignedPiece V → SimpleGraph V) (P : AssignedPiece V) : AssignedPiece V :=
  ⟨P.vertices,P.graph\F P,fun _ _ h => P.supported h.1⟩

/-- The same boxes and cycles, with every correction graph transferred
into the box remainder before constructing its children. -/
def transferStage {P : AssignedPiece V} (s : StageSplit P)
    (F : AssignedPiece V → SimpleGraph V) (hF : ∀ R, F R≤R.graph) : StageSplit P where
  cycles := s.cycles
  boxes := s.boxes
  pieces := fun B => (s.pieces B).map (parityPiece F)
  remainder := fun B => s.remainder B⊔graphUnion ((s.pieces B).map F)
  cycles_good := s.cycles_good
  box_subset := s.box_subset
  box_nonempty := s.box_nonempty
  box_cover := s.box_cover
  piece_subset := by
    intro B hB R hR
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
    exact s.piece_subset B hB Q hQ
  piece_disjoint := fun B hB => List.pairwise_map.mpr (s.piece_disjoint B hB)
  remainder_supported := by
    intro B hB
    apply transferred_remainder_supported _ _ _ _ (s.remainder_supported B hB)
    intro R hR x y hxy
    have hh := R.supported (hF R hxy)
    exact ⟨s.piece_subset B hB R hR hh.1,s.piece_subset B hB R hR hh.2⟩
  box_partition := by
    intro B hB
    have hh := partition_transfer_subgraphs (s.pieces B) AssignedPiece.graph F B.graph
      (s.remainder B) (fun R _ => hF R) (s.box_partition B hB)
    simpa only [List.map_map,Function.comp_def,parityPiece] using hh
  partition := s.partition

def EvenEntropyStageBounds {P : AssignedPiece V} (t : StageSplit P)
    (D ell L h : ℝ) : Prop :=
  (t.cycles.length:ℝ)*ell ≤ D*P.vertices.card/2 ∧
  vertexMass t.boxes ≤ (1+2*ell/(L-ell-2))*P.vertices.card ∧
  (∀ B∈t.boxes, (B.vertices.card:ℝ)≤L) ∧
  (∀ B∈t.boxes, ∀ R∈t.pieces B,
    h<(R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ)≤L ∧
      CutExpansionOn R.graph R.vertices ((1023/1024)*h) ∧
      (∀ v, Even (R.graph.degree v))) ∧
  (∀ B∈t.boxes, 2*(edgeCount (t.remainder B):ℝ) ≤
    h*((1001/1000:ℝ)+log (L/h)/log 2)*B.vertices.card)

/-- Actual Eulerian cores and an exact edge partition, including the
cost of moving all parity forests into the next layer. -/
theorem exists_even_entropy_stage_split (P : AssignedPiece V) {D ell L h : ℝ}
    (hell : 1≤ell) (hL : ell+2<L) (hh : 4096<h) (hhL : h≤L)
    (hsquare : 2048*L<h^2)
    (hdeg : 2*(edgeCount P.graph:ℝ)≤D*P.vertices.card) :
    ∃ t : StageSplit P, EvenEntropyStageBounds t D ell L h := by
  obtain ⟨s,hs⟩ := exists_entropy_stage_split P hell hL (by linarith) hhL hdeg
  have hex (R : AssignedPiece V) : ∃ F : SimpleGraph V,
      F≤R.graph ∧ edgeCount F≤R.vertices.card ∧
      ((h<(R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ)≤L ∧
          CutExpansionOn R.graph R.vertices h) →
        (∀ v, Even ((R.graph\F).degree v)) ∧
          CutExpansionOn (R.graph\F) R.vertices ((1023/1024)*h)) := by
    by_cases hR : h<(R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ)≤L ∧
        CutExpansionOn R.graph R.vertices h
    · obtain ⟨F,hFG,hFs,hFc,hFe,hFx⟩ := supported_parity_correction R hh hR.1
        (by linarith only [hR.2.1,hsquare]) hR.2.2
      exact ⟨F,hFG,hFc,fun _ => ⟨hFe,hFx⟩⟩
    · refine ⟨⊥,bot_le,?_,fun h => False.elim (hR h)⟩
      simp only [edgeCount,SimpleGraph.edgeFinset,←Set.ncard_eq_toFinset_card']
      change (⊥ : SimpleGraph V).edgeSet.ncard≤R.vertices.card
      simp
  choose F hF using hex
  let t := transferStage s F (fun R => (hF R).1)
  refine ⟨t,hs.1,hs.2.1,hs.2.2.1,?_,?_⟩
  · intro B hB R hR
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
    have hQb := hs.2.2.2.1 B hB Q hQ
    have hpar := (hF Q).2.2 hQb
    refine ⟨hQb.1,hQb.2.1,hpar.2,?_⟩
    intro v
    dsimp only [parityPiece]
    convert hpar.1 v using 1
    congr 1
    exact Subsingleton.elim _ _
  · intro B hB
    have hc := transferred_remainder_edge_count (s.pieces B) F (s.remainder B) B.vertices
      (s.piece_disjoint B hB) (s.piece_subset B hB) (fun Q _ => (hF Q).2.1)
    have hcR : (edgeCount (s.remainder B⊔graphUnion ((s.pieces B).map F)):ℝ)≤
        edgeCount (s.remainder B)+B.vertices.card := by exact_mod_cast hc
    exact parity_remainder_cost (by linarith) (Nat.cast_nonneg _) (hs.2.2.2.2 B hB) hcR

end
end Cycle12
