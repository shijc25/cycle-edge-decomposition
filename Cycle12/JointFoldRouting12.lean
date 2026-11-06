import Cycle12.FoldDemandCertificates12
import Cycle12.OriginalIncidenceRouting12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I T : Type} [Fintype V] [Fintype W] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq I]

/-- Use the combined original-edge certificate for one simultaneous
routing call in the core. Hard ports, soft costs and common-team interior
constraints are all enforced on this same family of routes. -/
theorem certificate_routing_at_scale (F : SimpleGraph V) (core H : SimpleGraph W)
    (e : W ↪ V) {w : ℝ} (hw : wA ≤ w) (hn : 2 ≤ Fintype.card W)
    (horder : (Fintype.card W:ℝ) ≤ (2:ℝ)^(rho*w))
    (hcore : OAI.ErdosGallai.CutExpansion core ((1023/1024)*(2:ℝ)^(s*w)))
    (hH : CutExpands H (routingExpansion w))
    (a b : I → W) (team : I → T) (hard : I → Finset W) (weight : I → W → ℝ)
    (S : Set (Sym2 V))
    (P : OriginalEndpointCertificate F (fun i => e (a i)) (fun i => e (b i)) S)
    (hgood : ∀ k : I × Bool,(F.degree (e (if k.2 then b k.1 else a k.1)):ℝ) ≤ routingAllowance w)
    (hteam : ∀ t,teamLoad team t ≤ routingTeamSize w)
    (hhard : ∀ i,(hard i).card ≤ 2*routingTeamSize w)
    (hweight : ∀ i v,0 ≤ weight i v) :
    ∃ p : ∀ i,H.Walk (a i) (b i),
      (∀ i,(p i).IsPath ∧ (p i).length ≤ globalRoutingLength (Fintype.card W) w ∧
        Disjoint (routeInterior (p i)) (hard i) ∧
        (∑ v∈routeInterior (p i),weight i v) ≤
          (gamma/(routingTeamSize w:ℝ))*∑ v,weight i v) ∧
      (∀ i j,i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j,i ≠ j → team i=team j → Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  have he (k : I × Bool) :
      (if k.2 then e (b k.1) else e (a k.1))=e (if k.2 then b k.1 else a k.1) := by
    cases k.2 <;> rfl
  apply original_incidence_routing_at_scale F core H e hw hn horder hcore hH a b team hard weight
    P.neighbor
  · intro k
    rw [←he]
    exact P.adj k
  · simpa only [he] using P.injective
  · exact hgood
  · exact hteam
  · exact hhard
  · exact hweight

end
end Cycle12.Even12
