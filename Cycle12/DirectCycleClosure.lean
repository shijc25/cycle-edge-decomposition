import Cycle12.DirectRouting324
import Cycle12.LegacyExpansion
import Cycle12.Foundations.SampledCyclePacking

set_option maxHeartbeats 2000000

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem paired_endpoint_load {I T : Type} [Fintype I] [DecidableEq T]
    (f : I × Bool → T) (r : T) :
    endpointLoad (fun i => f (i,false)) (fun i => f (i,true)) r=
      (univ.filter (fun k => f k=r)).card := by
  rw [← paired_endpoint_degree f r]
  unfold endpointLoad Suppression.incidenceDegree
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole,Nat.cast_id]

/-- Direct paired routes close the outside paths using a separate source bank. -/
theorem direct_cycles_from_two_banks (G : SimpleGraph V) (U : Finset V)
    {δ β L lower upper edgeLower incidentUpper f h : ℝ}
    (hU : GoodVertexSample G U δ β L lower upper edgeLower incidentUpper)
    (F J : SimpleGraph U) (hFG : F≤G.induce (U:Set V)) (hJG : J≤G.induce (U:Set V))
    (hFJ : Disjoint F.edgeSet J.edgeSet)
    (hretain : ∀ S : Finset U, f*cutSize (G.induce (U:Set V)) S ≤ (cutSize F S:ℝ))
    (hJ : CutExpands J h) (hh : 0 < h) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hL : 1 ≤ f*L)
    (c : ℕ) (hc0 : 0 < c) (hcap : Fintype.card V-U.card ≤ c*U.card)
    (hcbeta : (c:ℝ) ≤ f*β)
    (hnh : 4096 ≤ (U.card:ℝ)/h) (hcube : 324*(c:ℝ)^2*U.card ≤ h^3) :
    ∃ C : CyclePacking G, 2*C.count ≤ Fintype.card V-U.card ∧
      C.singles ≤ incidentEdgeCount G U+(Fintype.card V-U.card) := by
  classical
  letI : DecidableEq U := Classical.decEq U
  obtain ⟨P,hPU,hcount,hsingles⟩ := exists_external_path_packing G U
  let FL := reservoirLift U F
  have hFL : FL≤G := reservoirLift_le G U F hFG
  have hAU : Disjoint P.sources U := by
    apply Finset.disjoint_left.mpr
    intro v hv hvU
    obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_image.mp hv
    cases b
    · exact hPU i _ (P.paths i).walk.end_mem_support hvU
    · exact hPU i _ (P.paths i).walk.start_mem_support hvU
  have hretain' := reservoirLift_retains_cuts G U F hretain
  obtain ⟨R⟩ := ReservoirPorts.exists_routing_in_bank G FL P.sources U U c hFL hAU (Subset.refl _)
    (by rw [P.sources_card]; exact hcount.trans hcap) hf0 hf1 hL hretain'
    (by
      intro Y hY S hSU hS
      have hYU := hAU.mono_left hY
      simpa only [internal_cutSize G U S hSU,add_comm] using hU.anchoring Y S hYU hSU hS)
    (by
      intro S hSU hsmall
      have hb := mul_le_mul_of_nonneg_left (hU.cuts S hSU hsmall) hf0
      rw [← internal_cutSize G U S hSU] at hb
      have hh := (mul_le_mul_of_nonneg_right hcbeta (Nat.cast_nonneg (α:=ℝ) S.card)).trans
        (by simpa only [mul_assoc] using hb.trans (hretain' S hSU))
      have he : U∩S=S := inter_eq_right.mpr hSU
      rw [he]
      exact_mod_cast hh)
  let branch : Fin P.count × Bool → U := fun k => R.branch (P.sourceEmbedding k)
  have hslots : Function.Injective (fun k => (branch k,R.slot (P.sourceEmbedding k))) := by
    intro k l h
    exact P.sourceEmbedding.injective (R.slot_injective h)
  have hload : ∀ r : U, (endpointLoad (fun i => branch (i,false)) (fun i => branch (i,true)) r:ℝ) ≤ (c:ℝ) := by
    intro r
    rw [paired_endpoint_load]
    exact_mod_cast slot_injective_load branch (fun k => R.slot (P.sourceEmbedding k)) hslots r
  obtain ⟨Q,hQ,hQQ⟩ := direct_edge_routing_324 (k:=(c:ℝ)) J (fun i => branch (i,false)) (fun i => branch (i,true))
    hh (by exact_mod_cast hc0) hJ
    (by simpa only [Fintype.card_coe] using hnh)
    (by simpa only [Fintype.card_coe] using hcube) hload
  let inc : J →g G := ⟨Subtype.val,fun hxy => hJG hxy⟩
  let fan : ∀ k, G.Walk (P.endpoint k) (branch k).val := fun k =>
    (R.path (P.sourceEmbedding k)).mapLe (ReservoirPorts.routingGraph_le hFL P.sources U)
  have hfanEdge : ∀ k, (fan k).edgeSet=(R.path (P.sourceEmbedding k)).edgeSet :=
    fun k => Walk.edgeSet_mapLe_eq_edgeSet _ _
  have hfanSupport : ∀ k, (fan k).support=(R.path (P.sourceEmbedding k)).support :=
    fun k => Walk.support_mapLe_eq_support _ _
  have hdis : Disjoint (ReservoirPorts.routingGraph G FL P.sources U).edgeSet (reservoirLift U J).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he heJ
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj (reservoirEmbedding U) J x y).mp heJ
      change (FL.Adj a.val b.val ∧ a.val∈U ∧ b.val∈U) ∨
        (G.Adj a.val b.val ∧ (a.val∈P.sources ∧ b.val∈U ∨ a.val∈U ∧ b.val∈P.sources)) at he
      rcases he with he | he
      · have hf : F.Adj a b := by
          obtain ⟨a',b',hab',ha,hb⟩ := (SimpleGraph.map_adj (reservoirEmbedding U) F a.val b.val).mp he.1
          have ha' : a'=a := Subtype.ext ha
          have hb' : b'=b := Subtype.ext hb
          simpa only [ha',hb'] using hab'
        exact Set.disjoint_left.mp hFJ (show s(a,b)∈F.edgeSet from hf) (show s(a,b)∈J.edgeSet from hab)
      · rcases he.2 with he | he
        · exact Finset.disjoint_left.mp hAU he.1 a.property
        · exact Finset.disjoint_left.mp hAU he.2 b.property
  have hQsubset : ∀ i, ((Q i).map inc).edgeSet⊆(reservoirLift U J).edgeSet := by
    intro i e he
    rw [Walk.edgeSet_map] at he
    obtain ⟨e',he',rfl⟩ := he
    rw [reservoirLift,SimpleGraph.edgeSet_map]
    exact ⟨e',(Q i).edges_subset_edgeSet he',rfl⟩
  obtain ⟨C,hC,_,hres,_⟩ := close_paths_via_reservoir P (U:Set V) hPU (fun k => (branch k).val) fan
    (by intro k v hv; exact R.tail_inside (P.sourceEmbedding k) v (by simpa only [hfanSupport] using hv))
    (by intro k l hkl; simpa only [hfanEdge] using R.disjoint (P.sourceEmbedding.injective.ne hkl))
    (fun i => (Q i).map inc)
    (by
      intro i v hv
      rw [Walk.support_map] at hv
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp hv
      exact a.property)
    (by
      intro i j hij
      rw [Walk.edgeSet_map,Walk.edgeSet_map]
      apply Set.disjoint_left.mpr
      rintro e ⟨a,ha,hea⟩ ⟨b,hb,heb⟩
      have hab : a=b := Sym2.map.injective Subtype.val_injective (hea.trans heb.symm)
      subst b
      exact Finset.disjoint_left.mp (hQQ i j hij) (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb))
    (by
      intro k i
      rw [hfanEdge]
      exact hdis.mono (R.path (P.sourceEmbedding k)).edges_subset_edgeSet (hQsubset i))
  exact ⟨C,by simpa only [hC] using hcount,hres.trans hsingles⟩

end
end Cycle12
