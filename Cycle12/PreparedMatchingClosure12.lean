import Cycle12.MatchingRoutedClosure12

namespace Cycle12.PreparedClassLedger12
open Cycle12 Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {V W I : Type} [Fintype V] [Fintype W] [Fintype I]
  [DecidableEq V] [DecidableEq W] [DecidableEq I]
variable {G : SimpleGraph V} {H : SimpleGraph W} {A : I → Finset V} {Q : ℕ}
  {label : Sym2 (Option I)} {R : SimpleGraph V}

def matchingGroupCount (D : PreparedClassLedger12 G A Q label R) : ℕ :=
  match D with
  | .crossing _ _ _ _ P _ => Fintype.card P.matching.edgeSet/Q+1
  | _ => 0

/-- Every prepared label class closes its matching edges with its exact
stored orientation. Empty and noncrossing classes cost no cycles. -/
theorem close_matching (D : PreparedClassLedger12 G A Q label R)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) (hQ : 0<Q)
    (e : V ↪ W) (B : I → Finset W) (hB : Pairwise (fun r t => Disjoint (B r) (B t)))
    (hA : ∀ r v,v∈A r → e v∈B r)
    (hGH : ∀ {x y},G.Adj x y → H.Adj (e x) (e y))
    (route : ∀ j : (D.matchingFamily hd).Index,
      H.Walk (e ((D.matchingFamily hd).left j)) (e ((D.matchingFamily hd).right j)))
    (hpath : ∀ j,(route j).IsPath)
    (hsupport : ∀ j v,v∈(route j).support → v∈B ((D.matchingFamily hd).owner j))
    (hhard : ∀ j,Disjoint (routeInterior (route j)) (((D.matchingTeams hd hQ).hard j).map e))
    (hteam : ∀ j k,j≠k → (D.matchingTeams hd hQ).team j=(D.matchingTeams hd hQ).team k →
      Disjoint (routeInterior (route j)) (routeInterior (route k)))
    (hedges : Pairwise (fun j k => Disjoint (route j).edgeSet (route k).edgeSet))
    (horiginal : ∀ j,Disjoint (Sym2.map e '' G.edgeSet) (route j).edgeSet) :
    ∃ P : CyclePacking H,P.used=Sym2.map e '' D.matchingEdges∪(⋃ j,(route j).edgeSet) ∧
      P.count≤D.matchingGroupCount := by
  cases D with
  | crossing r t hrt he P hh =>
    have hcross : ∀ {x y},(edgeLabelGraph G (blockLabel A) label).Adj x y →
        (x∈A r ∧ y∈A t) ∨ (x∈A t ∧ y∈A r) := by
      intro x y hxy
      rw [he] at hxy
      exact ((block_cross_graph G A hd r t x y).mp hxy).2
    let data := Classical.choice (P.request_data hcross)
    have ho : ∀ j : data.Index,Disjoint (Sym2.map e '' P.second.residue.edgeSet) (route j).edgeSet := by
      intro j
      exact (horiginal j).mono (Set.image_mono (edgeSet_mono (fun {_ _} h => h.1.1.1))) subset_rfl
    obtain ⟨T,hT,hcount⟩ := data.close_embedded e P.isMatching hQ (B r) (B t) (hB hrt)
      (fun j => hA r _ (data.ports j).1) (fun j => hA t _ (data.ports j).2.1)
      (fun {_ _} h => hGH h.1.1.1) route hpath (fun j => hsupport (.inl j))
      (fun j => hsupport (.inr j)) hhard hteam hedges ho
    refine ⟨T,?_,?_⟩
    · change T.used=(Sym2.map e '' (⋃ t,matchingOriginalGroup P.second.residue P.matching Q t))∪_
      rw [matchingOriginalGroups_union _ _ P.isMatching Q]
      exact hT
    · simpa only [matchingGroupCount,Fintype.card_fin] using hcount
  | internal r he hh =>
    refine ⟨CyclePacking.empty H,?_,by simp [CyclePacking.empty,matchingGroupCount]⟩
    simp [CyclePacking.used,CyclePacking.empty,matchingEdges,matchingFamily,OwnedEndpointFamily12.empty]
  | external he hh =>
    refine ⟨CyclePacking.empty H,?_,by simp [CyclePacking.empty,matchingGroupCount]⟩
    simp [CyclePacking.used,CyclePacking.empty,matchingEdges,matchingFamily,OwnedEndpointFamily12.empty]
  | outside r he P hh =>
    refine ⟨CyclePacking.empty H,?_,by simp [CyclePacking.empty,matchingGroupCount]⟩
    simp [CyclePacking.used,CyclePacking.empty,matchingEdges,matchingFamily,OwnedEndpointFamily12.empty]

end
end Cycle12.PreparedClassLedger12
