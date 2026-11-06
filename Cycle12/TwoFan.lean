import Cycle12.FanOriginal
import Cycle12.FirstHitPath

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem trim_fan_path (G : SimpleGraph V) (S : Finset V) {x : V}
    (p : (fanApex G S).Walk (some x) none) (hp : p.IsPath) :
    ∃ a∈S, ∃ r : G.Walk x a, r.IsPath ∧
      (∀ z∈r.support, some z∈p.support) ∧
      (∀ z∈r.support, z≠a → z∉S) := by
  obtain ⟨b,hb,hbp⟩ := fan_apex_path_hits G S p
  obtain ⟨w,hw,hwS,hfirst⟩ := first_hit_takeUntil p (some '' (S:Set V))
    ⟨some b,hbp,b,hb,rfl⟩
  obtain ⟨a,ha,rfl⟩ := hwS
  have hprefix := hp.takeUntil hw
  have hnone := Walk.endpoint_notMem_support_takeUntil hp hw (by simp : (none:Option V)≠some a)
  obtain ⟨r,hr,hs,_⟩ := fan_path_remove_apex G S (p.takeUntil (some a) hw) hprefix hnone
  refine ⟨a,ha,r,hr,?_,?_⟩
  · intro z hz
    exact p.support_takeUntil_subset_support hw ((hs z).mp hz)
  · intro z hz hza hzS
    exact hfirst (some z) ((hs z).mp hz) (fun he => hza (Option.some.inj he)) ⟨z,hzS,rfl⟩

/-- The two-fan lemma, with actual simple paths ending at distinct
vertices of S and meeting S only at those endpoints. -/
theorem two_fan_to_set (G : SimpleGraph V) (S : Finset V) (hS : 2 ≤ S.card)
    (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (x : V) (hx : x∉S) :
    ∃ a∈S, ∃ b∈S, a≠b ∧ ∃ p : G.Walk x a, ∃ q : G.Walk x b,
      p.IsPath ∧ q.IsPath ∧
      (∀ z∈p.support, z≠a → z∉S) ∧
      (∀ z∈q.support, z≠b → z∉S) ∧
      (∀ z∈p.support, z∈q.support → z=x) := by
  obtain ⟨P,Q,hP,hQ,hdisjoint⟩ := fan_apex_two_paths G S hS hconn hrobust x hx
  obtain ⟨a,ha,p,hp,hpP,hpS⟩ := trim_fan_path G S P hP
  obtain ⟨b,hb,q,hq,hqQ,hqS⟩ := trim_fan_path G S Q hQ
  have hcommon : ∀ z∈p.support, z∈q.support → z=x := by
    intro z hzp hzq
    rcases hdisjoint (some z) (hpP z hzp) (hqQ z hzq) with hz | hz
    · exact Option.some.inj hz
    · cases hz
  have hab : a≠b := by
    intro he
    have haQ : a∈q.support := he ▸ q.end_mem_support
    have hax := hcommon a p.end_mem_support haQ
    exact hx (hax ▸ ha)
  exact ⟨a,ha,b,hb,hab,p,q,hp,hq,hpS,hqS,hcommon⟩

end
end Cycle12
