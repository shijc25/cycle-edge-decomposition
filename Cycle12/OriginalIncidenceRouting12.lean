import Cycle12.MixedEndpointIncidence12
import Cycle12.EvenRoutingBanks12
import Cycle12.RouteEmbedding12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I T : Type} [Fintype V] [Fintype W] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq I]

/-- The actual router can be applied once to any mixed family with a
joint original-incidence injection. Only vertices used as endpoints need
be good in the whole original descendant graph. -/
theorem original_incidence_routing_at_scale (F : SimpleGraph V) (core H : SimpleGraph W)
    (e : W ↪ V) {w : ℝ} (hw : wA ≤ w) (hn : 2 ≤ Fintype.card W)
    (horder : (Fintype.card W:ℝ) ≤ (2:ℝ)^(rho*w))
    (hcore : OAI.ErdosGallai.CutExpansion core ((1023/1024)*(2:ℝ)^(s*w)))
    (hH : CutExpands H (routingExpansion w))
    (a b : I → W) (team : I → T) (hard : I → Finset W) (weight : I → W → ℝ)
    (neighbor : I × Bool → V)
    (hadj : ∀ k,F.Adj (e (if k.2 then b k.1 else a k.1)) (neighbor k))
    (hinj : Function.Injective (fun k : I × Bool =>
      (e (if k.2 then b k.1 else a k.1),neighbor k)))
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
  have hload (v : W) : (endpointLoad a b v:ℝ) ≤ routingAllowance w := by
    have hp (k : I × Bool) :
        (if k.2 then e (b k.1) else e (a k.1))=e (if k.2 then b k.1 else a k.1) := by
      cases k.2 <;> rfl
    have hi : Function.Injective (fun k : I × Bool =>
        ((if k.2 then e (b k.1) else e (a k.1)),neighbor k)) := by
      simpa only [hp] using hinj
    have hh := endpointLoad_from_incidence_injection F (fun i => e (a i)) (fun i => e (b i))
      neighbor (by intro k; rw [hp]; exact hadj k) hi (e v)
    rw [endpointLoad_map_embedding] at hh
    by_cases hport : ∃ k : I × Bool,(if k.2 then b k.1 else a k.1)=v
    · obtain ⟨k,hk⟩ := hport
      have hg := hgood k
      rw [hk] at hg
      exact (by exact_mod_cast hh : (endpointLoad a b v:ℝ) ≤ F.degree (e v)).trans hg
    · have ha (i : I) : a i ≠ v := fun h => hport ⟨(i,false),h⟩
      have hb (i : I) : b i ≠ v := fun h => hport ⟨(i,true),h⟩
      have hz : endpointLoad a b v=0 := by simp [endpointLoad,ha,hb]
      rw [hz,Nat.cast_zero]
      exact (routingAllowance_pos w).le
  exact bank_routing_at_scale core H hw hn horder (by convert hcore using 1) hH a b team hard weight
    hload hteam hhard hweight

end
end Cycle12.Even12
