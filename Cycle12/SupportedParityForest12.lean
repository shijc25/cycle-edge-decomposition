import Cycle12.SupportedEdges
import Cycle12.Foundations.ExpanderParityForest
import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutExpansionOn_induce {G : SimpleGraph V} {U : Finset V} {h : ℝ}
    (hexp : CutExpansionOn G U h) :
    OAI.ErdosGallai.CutExpansion (G.induce (U:Set V)) h := by
  apply ExpansionWithin.induce
  intro S hS hsmall
  have hc : S.card ≤ (U\S).card := by
    rw [Finset.card_sdiff_of_subset hS]
    omega
  have hh := hexp S hS
  rw [min_eq_left (by exact_mod_cast hc)] at hh
  exact hh

theorem cutExpansionOn_of_induce {G : SimpleGraph V} {U : Finset V} {h : ℝ}
    (hexp : OAI.ErdosGallai.CutExpansion (G.induce (U:Set V)) h) :
    CutExpansionOn G U h := by
  intro S hS
  let T := reservoirSide U S
  have hT : T.image Subtype.val=S := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_reservoirSide U S a).mp ha
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,hS hv⟩,(mem_reservoirSide U S _).mpr hv,rfl⟩
  have hc : T.card=S.card := reservoirSide_card U S hS
  have hc' : Tᶜ.card=(U\S).card := by
    rw [Finset.card_compl,Finset.card_sdiff_of_subset hS,hc]
    have he : Fintype.card (U:Set V)=U.card := Fintype.card_of_finset' U (fun _ => Iff.rfl)
    simp only [Fintype.card_coe]
  have hh : h*min (T.card:ℝ) (Tᶜ.card:ℝ) ≤ (cutSize (G.induce (U:Set V)) T:ℝ) := by
    rw [cutSize_eq_interedges]
    convert hexp T using 1
    congr 1
  rw [cutSize_induce,hT,hc,hc'] at hh
  exact hh

theorem reservoirLift_supported (U : Finset V) (F : SimpleGraph U) :
    SupportedOn (reservoirLift U F) U := by
  intro x y h
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj (reservoirEmbedding U) F x y).mp h
  exact ⟨a.property,b.property⟩

theorem induce_reservoirLift (U : Finset V) (F : SimpleGraph U) :
    (reservoirLift U F).induce (U:Set V)=F := by
  ext a b
  change (F.map (reservoirEmbedding U)).Adj a.val b.val ↔ F.Adj a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x,y,hxy,hx,hy⟩
    exact (Subtype.ext hx ▸ Subtype.ext hy ▸ hxy)
  · exact fun hab => ⟨a,b,hab,rfl,rfl⟩

theorem induce_sdiff_lift (G : SimpleGraph V) (U : Finset V) (F : SimpleGraph U) :
    (G\reservoirLift U F).induce (U:Set V)=G.induce (U:Set V)\F := by
  have hh := induce_reservoirLift U F
  ext a b
  change G.Adj a.val b.val ∧ ¬ (reservoirLift U F).Adj a.val b.val ↔ _
  have he : (reservoirLift U F).Adj a.val b.val ↔ F.Adj a b := by
    change ((reservoirLift U F).induce (U:Set V)).Adj a b ↔ F.Adj a b
    rw [hh]
  rw [he]
  rfl

theorem supported_induced_degree (G : SimpleGraph V) (U : Finset V)
    (hs : SupportedOn G U) (v : U) : (G.induce (U:Set V)).degree v=G.degree v.val := by
  have he := G.degree_induce_of_neighborSet_subset (v:=v)
    (fun w hw => (hs hw).2)
  simpa only [←SimpleGraph.ncard_neighborSet] using he

theorem supported_even_of_induced (G : SimpleGraph V) (U : Finset V)
    (hs : SupportedOn G U) (heven : ∀ v, Even ((G.induce (U:Set V)).degree v)) :
    ∀ v, Even (G.degree v) := by
  intro v
  by_cases hv : v∈U
  · have hh := heven ⟨v,hv⟩
    rwa [supported_induced_degree G U hs] at hh
  · have hz : G.degree v=0 := by
      apply (G.degree_eq_zero v).mpr
      intro w hw
      exact hv (hs hw).1
    rw [hz]
    exact ⟨0,rfl⟩

/-- Parity correction on the assigned vertices, with its true edge cost.
The removed graph is lifted back to the ambient vertex type. -/
theorem supported_parity_correction (P : AssignedPiece V) {h : ℝ}
    (hh : 4096<h) (horder : h<(P.vertices.card:ℝ))
    (hsquare : 2048*(P.vertices.card:ℝ)<h^2)
    (hexp : CutExpansionOn P.graph P.vertices h) :
    ∃ F : SimpleGraph V, F≤P.graph ∧ SupportedOn F P.vertices ∧
      edgeCount F≤P.vertices.card ∧
      (∀ v, Even ((P.graph\F).degree v)) ∧
      CutExpansionOn (P.graph\F) P.vertices ((1023/1024)*h) := by
  have hpos : 0<P.vertices.card := by exact_mod_cast (by linarith : (0:ℝ)<P.vertices.card)
  letI : Nonempty (P.vertices:Set V) := (Finset.card_pos.mp hpos).to_subtype
  have hc : Fintype.card (P.vertices:Set V)=P.vertices.card :=
    Fintype.card_of_finset' P.vertices (fun _ => Iff.rfl)
  obtain ⟨F,hF,hforest,hsize,hdegree,heven,hex⟩ :=
    expander_parity_forest_1023 (P.graph.induce (P.vertices:Set V)) hh
      (by simpa only [hc] using hsquare) (cutExpansionOn_induce hexp)
  let K := reservoirLift P.vertices F
  have hKG : K≤P.graph := reservoirLift_le P.graph P.vertices F hF
  have hs : SupportedOn (P.graph\K) P.vertices := fun _ _ hab => P.supported hab.1
  refine ⟨K,hKG,reservoirLift_supported _ _,?_,?_,?_⟩
  · have he : edgeCount K=F.edgeSet.ncard := by
      simp only [edgeCount,K,reservoirLift,SimpleGraph.edgeFinset,
        ←Set.ncard_eq_toFinset_card',SimpleGraph.edgeSet_map,
        Set.ncard_image_of_injective _ (reservoirEmbedding P.vertices).sym2Map.injective]
      rfl
    rw [he]
    exact hsize.trans ((Nat.sub_le _ _).trans_eq hc)
  · have he : ∀ v, Even (((P.graph\K).induce (P.vertices:Set V)).degree v) := by
      intro v
      simp only [←SimpleGraph.ncard_neighborSet] at heven ⊢
      simpa only [K,induce_sdiff_lift] using heven v
    have hh := supported_even_of_induced _ _ hs (by
      simpa only [←SimpleGraph.ncard_neighborSet] using he)
    simpa only [←SimpleGraph.ncard_neighborSet] using hh
  · apply cutExpansionOn_of_induce
    have hx : OAI.ErdosGallai.CutExpansion (P.graph.induce (P.vertices:Set V)\F) ((1023/1024)*h) := by
      convert hex using 1
    simpa only [K,induce_sdiff_lift] using hx

end
end Cycle12
