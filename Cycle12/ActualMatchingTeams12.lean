import Cycle12.RequestTeams12
import Cycle12.ActualMatchingFamily12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V]

namespace MatchingRequestData12
variable {H : SimpleGraph V} {U T : Finset V} {M : (⊤ : SimpleGraph H.edgeSet).Subgraph} {Q : ℕ}

def sideTeams (D : MatchingRequestData12 H U T M Q) (hQ : 0<Q)
    (a : H.edgeSet → V) : RequestTeams12 M.edgeSet V Q where
  Team := Fin (Fintype.card M.edgeSet/Q+1)
  finite := inferInstance
  team := demandGroup Q
  hard := fun j => groupPorts (demandGroup Q) (fun e : M.edgeSet => a e.val.out.1)
    (fun e => a e.val.out.2) (demandGroup Q j)
  capacity := by intro t; simpa only [teamLoad,Fintype.card_subtype] using D.team_capacity hQ t
  hard_capacity := fun j => (groupPorts_card _ _ _ _).trans
    (Nat.mul_le_mul_left 2 (D.team_capacity hQ _))

def teams (D : MatchingRequestData12 H U T M Q) (hQ : 0<Q) : RequestTeams12 D.Index V Q :=
  (D.sideTeams hQ D.a).sum (D.sideTeams hQ D.b)

end MatchingRequestData12

variable [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}
  {e : Sym2 (Option I)} {H : SimpleGraph V}

/-- Teams and both forbidden port sets come from the very matching
orientation and pairing used to construct the actual endpoint family. -/
def PreparedClassLedger12.matchingTeams (D : PreparedClassLedger12 G A Q e H)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) (hQ : 0<Q) :
    RequestTeams12 (D.matchingFamily hd).Index V Q := by
  cases D with
  | crossing r t hrt he P hh =>
    have hcross : ∀ {x y},(edgeLabelGraph G (blockLabel A) e).Adj x y →
        (x∈A r ∧ y∈A t) ∨ (x∈A t ∧ y∈A r) := by
      intro x y hxy
      rw [he] at hxy
      exact ((block_cross_graph G A hd r t x y).mp hxy).2
    let R := Classical.choice (P.request_data hcross)
    exact R.teams hQ
  | internal r he hh => exact RequestTeams12.empty
  | external he hh => exact RequestTeams12.empty
  | outside r he P hh => exact RequestTeams12.empty

def PreparedBlockBatch12.matchingTeams (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) (hQ : 0<Q) :
    RequestTeams12 (P.matchingFamily hd).Index V Q :=
  RequestTeams12.sigma (fun e => (P.classes e).ledger.matchingTeams hd hQ)

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

def ambientMatchingTeams (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    RequestTeams12 (F.ambientMatchingFamily P t).Index V
      (routingTeamSize (logScale (originalLog V) L.stopIndex i)) :=
  ((P t).matchingTeams (F.batchActive_disjoint t)
    (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1).mapVertices
      (Function.Embedding.subtype _)

def boxMatchingTeams (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i) :
    RequestTeams12 (F.boxMatchingFamily P z).Index V
      (routingTeamSize (logScale (originalLog V) L.stopIndex i)) :=
  RequestTeams12.sigma (fun t => F.ambientMatchingTeams P hi ⟨z,t⟩)

end ActualFoldStage12
end
end Cycle12.Even12
