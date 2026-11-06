import Cycle12.Foundations.RoutingCapacity

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem exists_integer_global_capacity {t : ℕ} {n T h d K : ℝ}
    (ht : 0 < t) (hteven : Even t) (hT : 3 ≤ T) (hn : 0 ≤ n)
    (htT : (t:ℝ) ≤ T) (hTt : T-3 ≤ (t:ℝ))
    (hh : 0 < h) (hd : 0 ≤ d) (hK : 0 ≤ K) (hKT : 1 ≤ K*T)
    (hbudget : K*T*(T+h) ≤ h*d)
    (hpair : n ≤ T^2/3-(22/3)*T) (hfan : n ≤ K*T^2-(3*K+1)*T) :
    ∃ c : ℕ, c ≤ 2*(t/6-2) ∧ n ≤ (c:ℝ)*t ∧ (c:ℝ)*((t:ℝ)+h) ≤ h*d := by
  obtain ⟨c,hc,hcap,hsmall,_⟩ := exists_integer_routing_capacity (H:=n+T) ht hteven hT
    htT hTt hh hd (by linarith) hK hKT hbudget hpair hfan (by linarith)
  exact ⟨c,hc,hcap,hsmall⟩

theorem cycles_of_local_capacity_bounds (G : SimpleGraph V) (U : Finset V)
    {δ β₀ β₁ η L lower upper edgeLower incidentUpper : ℝ}
    (hU : GoodVertexSample G U δ β₀ L lower upper edgeLower incidentUpper)
    (hlocal : LocalSampleCutExpansion G U β₁ η)
    {t : ℕ} {f d T K : ℝ} (B : SampleRoutingBank G U t f d)
    (ht : 0 < t) (hteven : Even t) (hT : 3 ≤ T)
    (htT : (t:ℝ) ≤ T) (hTt : T-3 ≤ (t:ℝ))
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f*L)
    (h₀ : 0 < f*β₀) (h₁ : 0 < f*β₁) (hη : 0 ≤ η) (hlower : 0 ≤ lower)
    (hd : 0 ≤ d) (hK : 0 ≤ K) (hKT : 1 ≤ K*T)
    (hbudget : K*T*(T+f*β₁) ≤ (f*β₁)*d)
    (hpair : (Fintype.card V:ℝ)-lower ≤ T^2/3-(22/3)*T)
    (hfan : (Fintype.card V:ℝ)-lower ≤ K*T^2-(3*K+1)*T)
    (hlarge : (Fintype.card V:ℝ)-lower ≤ (f*β₀)*(η*lower)-T) :
    ∃ C : CyclePacking G,
      (C.count:ℝ) ≤ ((Fintype.card V:ℝ)-lower)/2 ∧
      (C.singles:ℝ) ≤ incidentUpper+(Fintype.card V:ℝ)-lower := by
  obtain ⟨c,hc,hcap,hsmall,hbig⟩ := exists_integer_routing_capacity ht hteven hT htT hTt
    h₁ hd (mul_nonneg h₀.le (mul_nonneg hη hlower)) hK hKT hbudget hpair hfan hlarge
  exact cycles_of_sample_bank_real G U hU hlocal B c hc hcap hf₀ hf₁ hL h₀ h₁ hη hsmall hbig

theorem cycles_of_global_capacity_bounds (G : SimpleGraph V) (U : Finset V)
    {δ β L lower upper edgeLower incidentUpper : ℝ}
    (hU : GoodVertexSample G U δ β L lower upper edgeLower incidentUpper)
    {t : ℕ} {f d T K : ℝ} (B : SampleRoutingBank G U t f d)
    (ht : 0 < t) (hteven : Even t) (hT : 3 ≤ T)
    (htT : (t:ℝ) ≤ T) (hTt : T-3 ≤ (t:ℝ))
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f*L) (hh : 0 < f*β)
    (hd : 0 ≤ d) (hK : 0 ≤ K) (hKT : 1 ≤ K*T)
    (hbudget : K*T*(T+f*β) ≤ (f*β)*d)
    (hpair : (Fintype.card V:ℝ)-lower ≤ T^2/3-(22/3)*T)
    (hfan : (Fintype.card V:ℝ)-lower ≤ K*T^2-(3*K+1)*T) :
    ∃ C : CyclePacking G,
      (C.count:ℝ) ≤ ((Fintype.card V:ℝ)-lower)/2 ∧
      (C.singles:ℝ) ≤ incidentUpper+(Fintype.card V:ℝ)-lower := by
  have hnU : U.card ≤ Fintype.card V := card_le_univ U
  have hnUR : (U.card:ℝ) ≤ Fintype.card V := by exact_mod_cast hnU
  obtain ⟨c,hc,hcap,hsmall⟩ := exists_integer_global_capacity ht hteven hT
    (by linarith [hU.order_lower]) htT hTt hh hd hK hKT hbudget hpair hfan
  have hcapN : Fintype.card V-U.card ≤ c*t := by
    have hz : ((Fintype.card V-U.card:ℕ):ℝ) ≤ (c:ℝ)*t := by
      rw [Nat.cast_sub hnU]
      linarith [hU.order_lower]
    exact_mod_cast hz
  have hdegree : d ≤ (U.card:ℝ) := by
    have hz := (B.model.residue.degree_lt_card_verts (B.model.branch ⟨0,ht⟩)).le
    have hz' : (B.model.residue.degree (B.model.branch ⟨0,ht⟩):ℝ) ≤ U.card := by
      exact_mod_cast (by simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] using hz)
    exact (B.degrees ⟨0,ht⟩).trans hz'
  have hlarge : (t:ℝ)*c ≤ (f*β)*(1*U.card) := by
    have hm := mul_le_mul_of_nonneg_left hdegree hh.le
    have hcpos : 0 ≤ (c:ℝ)*(f*β) := mul_nonneg (Nat.cast_nonneg _) hh.le
    nlinarith
  have hlocal : LocalSampleCutExpansion G U β 1 := fun S hSU hS _ => hU.cuts S hSU hS
  obtain ⟨C,hcount,hsingles⟩ := cycles_of_sample_bank G U hU hlocal B c hc hcapN
    hf₀ hf₁ hL hh hh hsmall hlarge
  have hcountR : 2*(C.count:ℝ) ≤ (Fintype.card V:ℝ)-U.card := by exact_mod_cast hcount
  have hsinglesR : (C.singles:ℝ) ≤ (incidentEdgeCount G U:ℝ)+(Fintype.card V:ℝ)-U.card := by
    have hz := (Nat.cast_le (α:=ℝ)).mpr hsingles
    simpa only [Nat.cast_add,Nat.cast_sub hnU,add_sub_assoc] using hz
  exact ⟨C,by linarith [hU.order_lower],by linarith [hU.incident,hU.order_lower]⟩

end
end Cycle13
