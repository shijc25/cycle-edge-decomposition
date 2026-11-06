import Cycle12.Foundations.SeedTargets
import Cycle12.Foundations.StarDegrees

/-! Actual retained demands after deleting three hubs. Every old
interior edge remains, the exact extra degree is the target multiplicity,
and a retained resolution pulls back while avoiding the protection graph. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

namespace SeedEdgeData
variable {a b : I → V} {w : Fin 3 ↪ V} (D : SeedEdgeData a b w)

abbrev residualLeft (_D : SeedEdgeData a b w) (target : SeedStar a b w ↪ SeedInterior w) :
    SeedKeep a b w ⊕ SeedStar a b w → SeedInterior w := Sum.elim (seedKeepLeft a b w) target
abbrev residualRight : SeedKeep a b w ⊕ SeedStar a b w → SeedInterior w :=
  Sum.elim (seedKeepRight a b w) D.otherVertex

theorem residual_degree (target : SeedStar a b w ↪ SeedInterior w) (v : SeedInterior w) :
    Suppression.incidenceDegree (D.residualLeft target) D.residualRight v=
      Suppression.incidenceDegree a b v.val+(univ.filter (fun i => target i=v)).card := by
  have hh := star_residual_degree (seedInteriorEmbedding w) (w ∘ D.group)
    (fun i u => (u.property (D.group i)).symm) (seedKeepLeft a b w) (seedKeepRight a b w)
    D.otherVertex target v
  rw [D.split_degree] at hh
  exact hh

theorem residual_degree_le (target : SeedStar a b w ↪ SeedInterior w) (v : SeedInterior w) :
    Suppression.incidenceDegree (D.residualLeft target) D.residualRight v ≤
      Suppression.incidenceDegree a b v.val+1 := by
  have hh := star_residual_degree_le (seedInteriorEmbedding w) (w ∘ D.group)
    (fun i u => (u.property (D.group i)).symm) (seedKeepLeft a b w) (seedKeepRight a b w)
    D.otherVertex target v
  rw [D.split_degree] at hh
  exact hh

theorem residual_protected_degree (target : SeedStar a b w ↪ SeedInterior w)
    (v : SeedInterior w) (hv : ∀ i, target i≠v) :
    Suppression.incidenceDegree (D.residualLeft target) D.residualRight v=
      Suppression.incidenceDegree a b v.val := by
  have hh := star_residual_protected_degree (seedInteriorEmbedding w) (w ∘ D.group)
    (fun i u => (u.property (D.group i)).symm) (seedKeepLeft a b w) (seedKeepRight a b w)
    D.otherVertex target v hv
  rw [D.split_degree] at hh
  exact hh

def pullbackResidual (target : SeedStar a b w ↪ SeedInterior w)
    (R : DemandRouting (completeGraph (SeedInterior w)) (D.residualLeft target) D.residualRight) :
    DemandRouting (completeGraph V) a b :=
  (starDemandPullback (seedInteriorEmbedding w) (w ∘ D.group)
    (fun i u => (u.property (D.group i)).symm) (seedKeepLeft a b w) (seedKeepRight a b w)
    D.otherVertex target R).relabel (seedSplitEquiv a b w) D.split_endpoints

theorem pullbackResidual_avoids (target : SeedStar a b w ↪ SeedInterior w)
    (R : DemandRouting (completeGraph (SeedInterior w)) (D.residualLeft target) D.residualRight)
    (B : SimpleGraph V) (hB : ∀ u v : SeedInterior w, ¬B.Adj u.val v.val)
    (hstar : ∀ i, ¬B.Adj (w (D.group i)) (target i).val) :
    ∀ i, Disjoint ((D.pullbackResidual target R).route i).edgeSet B.edgeSet := by
  intro i
  rw [pullbackResidual,DemandRouting.relabel_edgeSet]
  exact starDemandPullback_avoids (seedInteriorEmbedding w) (w ∘ D.group)
    (fun i u => (u.property (D.group i)).symm) (seedKeepLeft a b w) (seedKeepRight a b w)
    D.otherVertex target R B hB hstar _

theorem residual_preserves_independent (target : SeedStar a b w ↪ SeedInterior w)
    (B : Set V) (ht : ∀ i, (target i).val∉B) (hB : ∀ i, ¬(a i∈B ∧ b i∈B)) :
    ∀ j, ¬((D.residualLeft target j).val∈B ∧ (D.residualRight j).val∈B) := by
  rintro (j | i) hj
  · exact hB j.val hj
  · exact ht i hj.1

end SeedEdgeData
end
end Cycle13
