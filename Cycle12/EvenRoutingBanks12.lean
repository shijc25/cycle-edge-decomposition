import Cycle12.GlobalBankRouting12
import Cycle12.GlobalBankPreparation12
import Cycle12.ComparisonRouting12
import Cycle12.Foundations.ExpanderOrderBound

namespace Cycle12.Even12
open Cycle12.Global12
open SimpleGraph Finset Real Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I T : Type} [Fintype V] [Fintype I] [Fintype T]

/-- The comparison-bank order ratio still holds after parity correction. -/
theorem even_routing_bank_order_ratio (G : SimpleGraph V) {h : ℝ}
    (hn : 2≤Fintype.card V) (hh : 4096<h)
    (hexp : OAI.ErdosGallai.CutExpansion G ((1023/1024)*h)) :
    4≤(Fintype.card V:ℝ)/(comparison_bank*h) := by
  have hb := cutExpansion_twice_le_order_add_one G hn hexp
  have hp : 0<comparison_bank*h := mul_pos (by norm_num [comparison_bank]) (by linarith)
  apply (le_div_iff₀ hp).mpr
  norm_num only [comparison_bank]
  linarith only [hb,hh]

/-- Split an already corrected core; no second parity correction is charged. -/
theorem prepare_even_banks_at_scale (G : SimpleGraph V) {w : ℝ}
    (hn : 2≤Fintype.card V) (hw : w0≤w)
    (horder : (Fintype.card V:ℝ)≤(2:ℝ)^(rho*w))
    (hexp : OAI.ErdosGallai.CutExpansion G ((1023/1024)*(2:ℝ)^(s*w))) :
    ∃ ω : Sym2 V → Bool,
      OAI.ErdosGallai.CutExpansion (splitBank G ω true) (router_bank*(2:ℝ)^(s*w)) ∧
      OAI.ErdosGallai.CutExpansion (splitBank G ω false) (completion_bank*(2:ℝ)^(s*w)) ∧
      Disjoint (splitBank G ω true) (splitBank G ω false) ∧
      splitBank G ω true⊔splitBank G ω false=G := by
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast (by omega : 0<Fintype.card V)
  obtain ⟨hlin,hquad,hlog⟩ := bank_preparation_scale_bounds hw hn0 horder
  obtain ⟨ω,ht,hf,hd,hu⟩ := biased_bank_split G hn
    (by positivity : (0:ℝ)<(1023/1024)*(2:ℝ)^(s*w)) hexp hlog
  refine ⟨ω,?_,?_,hd,hu⟩
  · convert ht using 1 <;> norm_num [router_bank] <;> ring
  · convert hf using 1 <;> norm_num [completion_bank] <;> ring

/-- All routing prerequisites are discharged at the current scale,
including integer team sizes and the comparison bank for dense graphs. -/
theorem bank_routing_at_scale (G H : SimpleGraph V) {w : ℝ}
    (hw : wA ≤ w) (hn : 2 ≤ Fintype.card V)
    (horder : (Fintype.card V:ℝ) ≤ (2:ℝ)^(rho*w))
    (hG : OAI.ErdosGallai.CutExpansion G ((1023/1024)*(2:ℝ)^(s*w)))
    (hH : CutExpands H (routingExpansion w))
    (source target : I → V) (team : I → T) (hard : I → Finset V) (weight : I → V → ℝ)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ routingAllowance w)
    (hteam : ∀ t, teamLoad team t ≤ routingTeamSize w)
    (hhard : ∀ i, (hard i).card ≤ 2*routingTeamSize w)
    (hweight : ∀ i v, 0 ≤ weight i v) :
    ∃ p : ∀ i, H.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ globalRoutingLength (Fintype.card V) w ∧
        Disjoint (routeInterior (p i)) (hard i) ∧
        (∑ v∈routeInterior (p i), weight i v) ≤
          (gamma/(routingTeamSize w:ℝ))*∑ v, weight i v) ∧
      (∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i=team j → Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  have hround := growing_rounding_bounds hw
  have hB : (0:ℝ) < routingTeamSize w := Nat.cast_pos.mpr hround.1
  have hK := routingAllowance_pos w
  have hteamR : ∀ t, (teamLoad team t:ℝ) ≤ routingTeamSize w := fun t => by exact_mod_cast hteam t
  have hhardC : ∀ i, ((hard i).card:ℝ) ≤ comparisonExpansion w/128 := by
    intro i
    have hi : ((hard i).card:ℝ) ≤ 2*(routingTeamSize w:ℝ) := by exact_mod_cast hhard i
    exact hi.trans (growing_hard_port_capacity hw)
  have hcomp : comparisonExpansion w ≤ routingExpansion w := by
    exact mul_le_mul_of_nonneg_right
      (show comparison_bank ≤ router_bank from routing_parameter_identities.2.2.2.2.2.1)
      (rpow_nonneg (by norm_num) _)
  by_cases hlarge : 4096 ≤ (Fintype.card V:ℝ)/routingExpansion w
  · have hk : routingAllowance w ≤ Parameters.q*(routingTeamSize w:ℝ) := by
      have hc : 0 < c := by norm_num [c]
      have hh : routingAllowance w ≤ (routingTeamSize w:ℝ)/c :=
        (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hround.2.1)
      simpa only [Parameters.q,Parameters.c,c,div_eq_mul_inv,mul_comm,one_mul] using hh
    have hcube : Parameters.R^2*Parameters.L^2*(routingTeamSize w:ℝ)^2*Fintype.card V ≤
        (routingExpansion w)^3 := by
      have hh := growing_cubic_capacity hw (Nat.cast_nonneg _) horder
      have he : router_constant=Parameters.R^2*Parameters.L^2 := by
        norm_num [router_constant,Parameters.R,Parameters.L]
      rwa [he] at hh
    have hhardR : ∀ i, ((hard i).card:ℝ) ≤ routingExpansion w/128 := fun i =>
      (hhardC i).trans (div_le_div_of_nonneg_right hcomp (by norm_num))
    obtain ⟨p,hp,he,ht⟩ := accepted_grouped_weighted_routing H source target team hard weight
      (routingExpansion_pos w) hB hK.le hH hlarge hk hcube hend hteamR hhardR hweight
    refine ⟨p,?_,he,ht⟩
    intro i
    simpa only [globalRoutingLength,if_pos hlarge,Parameters.L,router_length,
      Parameters.gamma,gamma] using hp i
  · have hHC : CutExpands H (comparisonExpansion w) := by
      intro S hS
      exact (mul_le_mul_of_nonneg_right hcomp (Nat.cast_nonneg _)).trans (hH S hS)
    have hw0 : w0 ≤ w := (show w0 ≤ wA by norm_num [w0,wA]).trans hw
    have hlin : 4096 < (2:ℝ)^(s*w) := by
      have hh := bank_linear_halfline hw0
      have hww : 1 ≤ w := (show (1:ℝ) ≤ w0 by norm_num [w0]).trans hw0
      linarith only [hh,hww]
    have hratio : 4 ≤ (Fintype.card V:ℝ)/comparisonExpansion w :=
      even_routing_bank_order_ratio G hn hlin hG
    have htwice : routingExpansion w ≤ 2*comparisonExpansion w := by
      have hh := mul_le_mul_of_nonneg_right
        (show router_bank ≤ 2*comparison_bank from routing_parameter_identities.2.2.2.2.2.2)
        (rpow_nonneg (by norm_num : (0:ℝ)≤2) (s*w))
      simpa only [routingExpansion,comparisonExpansion,mul_assoc] using hh
    have hratioUp : (Fintype.card V:ℝ)/comparisonExpansion w ≤ 8192 := by
      apply (div_le_iff₀ (comparisonExpansion_pos w)).mpr
      have hh := (div_lt_iff₀ (routingExpansion_pos w)).mp (lt_of_not_ge hlarge)
      linarith only [hh,htwice]
    obtain ⟨p,hp,he,ht⟩ := comparison_weighted_routing H source target team hard weight
      (comparisonExpansion_pos w) hB hK.le (show 4/5 ≤ gamma by norm_num [gamma])
      hHC hratio hratioUp (growing_comparison_capacity hw) hend hteamR hhardC hweight
    refine ⟨p,?_,he,ht⟩
    intro i
    simpa only [globalRoutingLength,if_neg hlarge] using hp i

end
end Cycle12.Even12
