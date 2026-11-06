import Cycle12.GroupedRouting
import Cycle12.LegacyExpansion

namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V ι τ : Type} [Fintype V] [Fintype ι] [Fintype τ]

/-- The exact parameters accepted for coefficient 12, instantiated in the
proved graph routing theorem, not just in a numerical certificate. -/
theorem accepted_grouped_weighted_routing (G : SimpleGraph V)
    (source target : ι → V) (team : ι → τ) (hard : ι → Finset V)
    (w : ι → V → ℝ) {h B k : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk₀ : 0 ≤ k)
    (hexp : CutExpands G h) (hnh : 4096 ≤ (Fintype.card V:ℝ)/h)
    (hk : k ≤ Parameters.q*B)
    (hcube : Parameters.R^2*Parameters.L^2*B^2*Fintype.card V ≤ h^3)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k)
    (hteam : ∀ c, (teamLoad team c:ℝ) ≤ B)
    (hhard : ∀ i, ((hard i).card:ℝ) ≤ h/128) (hw : ∀ i v, 0 ≤ w i v) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ routingLength (Fintype.card V) h Parameters.L ∧
        Disjoint (routeInterior (p i)) (hard i) ∧
        (∑ v ∈ routeInterior (p i), w i v) ≤ (Parameters.gamma/B)*∑ v,w i v) ∧
      (∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i=team j →
        Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  obtain ⟨hq,ha,ha1,hgap,hR,hγ,hr,hL,hcoef⟩ := Parameters.router_parameters_valid
  exact grouped_weighted_routing G source target team hard w hh hB hk₀ hq ha ha1 hgap hR
    (by linarith) hr hL hcoef hexp hnh hk hcube hend hteam hhard hw

/-- Small n/h uses the old, fully proved H128 theorem at the enlarged
capacity max(B,6k/5). The short-path constants retain their correct branch. -/
theorem small_ratio_weighted_routing (G : SimpleGraph V)
    (source target : ι → V) (team : ι → τ) (hard : ι → Finset V)
    (w : ι → V → ℝ) {h B k γ : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk₀ : 0 ≤ k) (hγ : 4/5 ≤ γ)
    (hexp : CutExpands G h)
    (hnh : 4 ≤ (Fintype.card V:ℝ)/h) (hnh' : (Fintype.card V:ℝ)/h ≤ 4096)
    (hlinear : 8192*max B ((6/5)*k) ≤ h)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k)
    (hteam : ∀ c, (teamLoad team c:ℝ) ≤ B)
    (hhard : ∀ i, ((hard i).card:ℝ) ≤ h/128) (hw : ∀ i v, 0 ≤ w i v) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ h128Length (Fintype.card V) h ∧
        Disjoint (routeInterior (p i)) (hard i) ∧
        (∑ v ∈ routeInterior (p i), w i v) ≤ (γ/B)*∑ v,w i v) ∧
      (∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i=team j →
        Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  let B' := max B ((6/5)*k)
  have hBB' : B ≤ B' := le_max_left _ _
  have hB' : 0 < B' := hB.trans_le hBB'
  have hk' : k ≤ (5/6)*B' := by
    have hb : (6/5)*k ≤ B' := le_max_right _ _
    linarith
  have hteam' : ∀ c, (teamLoad team c:ℝ) ≤ B' := fun c => (hteam c).trans hBB'
  have hcube : 16384*B'^2*Fintype.card V ≤ h^3 := by
    have hn := (div_le_iff₀ hh).mp hnh'
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 8192*B') hlinear
    have hm := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 16384*B'^2)
    have hh' := mul_le_mul_of_nonneg_right hsq hh.le
    nlinarith only [hm,hh']
  obtain ⟨p,hp,hedge,hsame⟩ := h128_weighted_routing G source target team hard w hh hB' hk₀
    ((cutExpands_iff_legacy G h).mp hexp) hnh hk' hcube hend hteam' hhard hw
  have hcap := h128_capacity hh hB'.le (Nat.cast_nonneg (α:=ℝ) (Fintype.card V)) hcube
  have hpay : 16*h128Length (Fintype.card V) h/h ≤ γ/B := by
    have hc : 20*B*h128Length (Fintype.card V) h ≤ h := by
      have hm := mul_le_mul_of_nonneg_right hBB'
        (by positivity : (0:ℝ) ≤ 20*h128Length (Fintype.card V) h)
      nlinarith only [hm,hcap]
    apply (div_le_div_iff₀ hh hB).mpr
    have hg := mul_le_mul_of_nonneg_right hγ hh.le
    nlinarith only [hc,hg]
  refine ⟨p,?_,hedge,hsame⟩
  intro i
  exact ⟨(hp i).1,(hp i).2.1,(hp i).2.2.1,
    (hp i).2.2.2.trans (mul_le_mul_of_nonneg_right hpay (Finset.sum_nonneg (fun v _ => hw i v)))⟩

end
end Cycle12
