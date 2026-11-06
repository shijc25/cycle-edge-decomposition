import Cycle12.ActualRouteCover12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 500000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

abbrev GlobalRouteIndex (hi : i≤L.stopIndex) := Σ z : L.FoldBoxIndex i,(F.ActualJointFamily P Q D hi z).Index

def globalRouteEdges (hi : i≤L.stopIndex) (t : F.GlobalRouteIndex P Q D hi) : Set (Sym2 V) :=
  (F.boxRoute P Q D hi t.1 t.2).edgeSet

theorem globalRouteEdges_disjoint (hi : i≤L.stopIndex) : Pairwise (fun t u : F.GlobalRouteIndex P Q D hi =>
    Disjoint (F.globalRouteEdges P Q D hi t) (F.globalRouteEdges P Q D hi u)) := by
  rintro ⟨z,j⟩ ⟨t,k⟩ hne
  by_cases hzt : z=t
  · subst t
    exact F.boxRoute_edges_disjoint P Q D hi z (fun h => hne (congrArg (Sigma.mk z) h))
  · exact F.actualRoutes_cross_disjoint P Q D hi (fun h => hzt (congrArg Sigma.fst h)) _ _

def globalRouteKind (hi : i≤L.stopIndex) (t : F.GlobalRouteIndex P Q D hi) : ℕ :=
  match t.2 with
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def globalMatchingClass (hi : i≤L.stopIndex) (t : F.GlobalRouteIndex P Q D hi) : Option F.MatchingClassIndex :=
  match t.2 with
  | .inr (.inl k) => some ⟨⟨t.1,k.1⟩,k.2.1⟩
  | _ => none

def globalQuotientBatch (hi : i≤L.stopIndex) (t : F.GlobalRouteIndex P Q D hi) : Option F.BatchIndex :=
  match t.2 with
  | .inr (.inr k) => some ⟨t.1,k.1⟩
  | _ => none

end ActualFoldStage12
end
end Cycle12.Even12
