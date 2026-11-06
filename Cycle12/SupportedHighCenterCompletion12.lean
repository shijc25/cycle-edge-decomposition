import Cycle12.ActualBatchPotential12
import Cycle12.GlobalHighCenterCompletion12
import Cycle12.SupportedParityForest12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem verticesWithin_image (W U : Finset V) (hU : U⊆W) :
    (verticesWithin W U).image Subtype.val=U := by
  ext v
  simp only [mem_image,mem_verticesWithin]
  exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun hv => ⟨⟨v,hU hv⟩,hv,rfl⟩⟩

theorem verticesWithin_compl (W U : Finset V) :
    (verticesWithin W U)ᶜ=verticesWithin W Uᶜ := by
  ext v
  simp only [mem_compl,mem_verticesWithin]

/-- Passing to a support set preserves every relevant original neighbour. -/
theorem neighborsIn_induce_supported (G : SimpleGraph V) (W A : Finset V)
    (hs : SupportedOn G W) (v : W) :
    (neighborsIn (G.induce (W:Set V)) v (verticesWithin W A)).card=
      (neighborsIn G v.val A).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨(mem_verticesWithin W A x).mp (mem_filter.mp hx).1,
      (mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro x hx
    have h := mem_filter.mp hx
    refine ⟨⟨x,(hs h.2).2⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨(mem_verticesWithin W A _).mpr h.1,h.2⟩

theorem cutExpansionOn_graph_mono {G H : SimpleGraph V} {U : Finset V} {h : ℝ}
    (hexp : OAI.ErdosGallai.Scale.CutExpansionOn G U h) (hGH : G≤H) :
    OAI.ErdosGallai.Scale.CutExpansionOn H U h := by
  intro S hS
  apply (hexp S hS).trans
  apply Nat.cast_le.mpr
  apply card_le_card
  intro e he
  have hh := G.mem_interedges_iff.mp he
  exact H.mem_interedges_iff.mpr ⟨hh.1,hh.2.1,hGH hh.2.2⟩

/-- Core expansion is unchanged when isolated ambient vertices are discarded. -/
theorem cutExpansionOn_induce_within (G : SimpleGraph V) (W U : Finset V)
    (hU : U⊆W) {h : ℝ}
    (hexp : OAI.ErdosGallai.Scale.CutExpansionOn G U h) :
    OAI.ErdosGallai.Scale.CutExpansionOn (G.induce (W:Set V)) (verticesWithin W U) h := by
  intro S hS
  let f : W ↪ V := Function.Embedding.subtype _
  have hu : (verticesWithin W U).image f=U := verticesWithin_image W U hU
  have hs : S.image f⊆U := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    exact (mem_verticesWithin W U x).mp (hS hx)
  have hd : ((verticesWithin W U)\S).image f=U\S.image f := by
    rw [Finset.image_sdiff _ _ f.injective,hu]
  have hh := hexp (S.image f) hs
  rw [←hd,card_image_of_injective _ f.injective,
    card_image_of_injective _ f.injective] at hh
  change h*min (S.card:ℝ) (((verticesWithin W U)\S).card:ℝ) ≤
    (((G.comap f).interedges S ((verticesWithin W U)\S)).card:ℝ)
  rw [interedges_card_comap]
  exact hh

namespace Even12
open Global12

/-- Apply the genuine high-center construction on its actual support, then
lift all cycles and singleton costs. The IH remains strictly smaller-order. -/
theorem supported_high_center_completion (G : SimpleGraph V) (W U : Finset V)
    (hU : U⊆W) (hs : SupportedOn G W) {w d K : ℝ}
    (hw : wA≤w) (hn : 2≤W.card) (hK : 0≤K)
    (hrlo : (2:ℝ)^(s*w)≤(U.card:ℝ)) (hrhi : (U.card:ℝ)≤(2:ℝ)^(rho*w))
    (hexp : OAI.ErdosGallai.Scale.CutExpansionOn G U (completion_bank*(2:ℝ)^(s*w)))
    (hdeg : ∀ v∈W,v∉U → d≤((neighborsIn G v U).card:ℝ))
    (hload : ∀ v∈U,((neighborsIn G v Uᶜ).card:ℝ)≤(2:ℝ)^(alpha*w))
    (hd : sqrt (2*(2:ℝ)^(alpha*w)*U.card)≤d)
    (hdup : d ≤ sqrt (2*(2:ℝ)^(alpha*w)*U.card)+1)
    (heven : ∀ v∈W,v∉U → Even (G.degree v))
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H,Q.weight≤K*m) :
    ∃ P : CyclePacking G,P.weight+d/2+2*(2:ℝ)^(alpha*w)≤
      (1+23/42+K*eta+1/2048)*(U.card:ℝ) := by
  letI : Nonempty W := (Finset.card_pos.mp (show 0<W.card by omega)).to_subtype
  have hc : Fintype.card (W:Set V)=W.card :=
    Fintype.card_of_finset' W (fun _ => Iff.rfl)
  have hu : (verticesWithin W U).card=U.card := verticesWithin_card W U hU
  have hideg : ∀ v : W,v∉verticesWithin W U →
      d≤((neighborsIn (G.induce (W:Set V)) v (verticesWithin W U)).card:ℝ) := by
    intro v hv
    rw [neighborsIn_induce_supported G W U hs v]
    exact hdeg v.val v.property (fun h => hv ((mem_verticesWithin W U v).mpr h))
  have hiload : ∀ v∈verticesWithin W U,
      ((neighborsIn (G.induce (W:Set V)) v (verticesWithin W U)ᶜ).card:ℝ)≤(2:ℝ)^(alpha*w) := by
    intro v hv
    rw [verticesWithin_compl,neighborsIn_induce_supported G W Uᶜ hs v]
    exact hload v.val ((mem_verticesWithin W U v).mp hv)
  have hie : ∀ v : W,v∉verticesWithin W U → Even ((G.induce (W:Set V)).degree v) := by
    intro v hv
    rw [supported_induced_degree G W hs v]
    exact heven v.val v.property (fun h => hv ((mem_verticesWithin W U v).mpr h))
  obtain ⟨Q,hQ⟩ := high_center_completion_at_scale (G.induce (W:Set V))
    (verticesWithin W U) hw (by simpa only [hc] using hn) hK
    (by simpa only [hu] using hrlo) (by simpa only [hu] using hrhi)
    (cutExpansionOn_induce_within G W U hU hexp) hideg hiload
    (by simpa only [hu] using hd) (by simpa only [hu] using hdup) hie
    (fun m hm => ih m (hm.trans_le (by rw [hc]; exact card_le_univ W)))
  refine ⟨liftInducedPacking G W Q,?_⟩
  rw [liftInducedPacking_weight G W Q (fun _ _ h => hs h)]
  simpa only [hu] using hQ

end Even12
end
end Cycle12
