import Cycle12.Foundations.ReservoirLift
import Cycle12.Foundations.ExternalPathPacking
import Cycle12.Foundations.VertexSamplingCertificate

namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- An actual model and its unused-edge bank on the sampled vertex type. -/
structure SampleRoutingBank (G : SimpleGraph V) (U : Finset V) (t : ℕ) (f d : ℝ) where
  model : WeakCliqueImmersion t (G.induce (U:Set V))
  cuts : ∀ S : Finset U, f*cutSize (G.induce (U:Set V)) S ≤ (cutSize model.residue S:ℝ)
  degrees : ∀ i, d ≤ (model.residue.degree (model.branch i):ℝ)

theorem cycles_of_sample_bank (G : SimpleGraph V) (U : Finset V)
    {δ β₀ β₁ η L lower upper edgeLower incidentUpper : ℝ}
    (hU : GoodVertexSample G U δ β₀ L lower upper edgeLower incidentUpper)
    (hlocal : LocalSampleCutExpansion G U β₁ η)
    {t : ℕ} {f d : ℝ} (B : SampleRoutingBank G U t f d)
    (c : ℕ) (hc : c ≤ 2*(t/6-2)) (hcap : Fintype.card V-U.card ≤ c*t)
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f*L)
    (h₀ : 0 < f*β₀) (h₁ : 0 < f*β₁)
    (hsmall : (c:ℝ)*(t+f*β₁) ≤ (f*β₁)*d)
    (hlarge : (t:ℝ)*c ≤ (f*β₀)*(η*U.card)) :
    ∃ C : CyclePacking G, 2*C.count ≤ Fintype.card V-U.card ∧
      C.singles ≤ incidentEdgeCount G U+(Fintype.card V-U.card) := by
  obtain ⟨P,hPU,hcount,hsingles⟩ := exists_external_path_packing G U
  let M := B.model.mapCopy (SimpleGraph.Copy.induce G (U:Set V))
  let F := reservoirLift U B.model.residue
  have hb : ∀ i, M.branch i∈U := fun i => (B.model.branch i).property
  have hFG : F≤G := reservoirLift_le G U B.model.residue (SimpleGraph.deleteEdges_le _)
  have hdegree : ∀ i, d ≤ ((ReservoirPorts.internalGraph F U).degree (M.branch i):ℝ) := by
    intro i
    change d ≤ ((ReservoirPorts.internalGraph (reservoirLift U B.model.residue) U).degree
      (B.model.branch i).val:ℝ)
    rw [reservoirLift_internal,reservoirLift_degree]
    exact B.degrees i
  obtain ⟨C,hC,_,hres,_⟩ := close_paths_from_good_sample G U hU hlocal P hPU M hb
    (B.model.mapCopy_inside U) F hFG (B.model.reservoirLift_residue_disjoint U) c hc
    (hcount.trans hcap) hf₀ hf₁ hL h₀ h₁ (reservoirLift_retains_cuts G U B.model.residue B.cuts)
    hdegree hsmall hlarge
  exact ⟨C,by simpa only [hC] using hcount,hres.trans hsingles⟩

theorem cycles_of_sample_bank_real (G : SimpleGraph V) (U : Finset V)
    {δ β₀ β₁ η L lower upper edgeLower incidentUpper : ℝ}
    (hU : GoodVertexSample G U δ β₀ L lower upper edgeLower incidentUpper)
    (hlocal : LocalSampleCutExpansion G U β₁ η)
    {t : ℕ} {f d : ℝ} (B : SampleRoutingBank G U t f d)
    (c : ℕ) (hc : c ≤ 2*(t/6-2)) (hcap : (Fintype.card V:ℝ)-lower ≤ (c:ℝ)*t)
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f*L)
    (h₀ : 0 < f*β₀) (h₁ : 0 < f*β₁) (hη : 0 ≤ η)
    (hsmall : (c:ℝ)*(t+f*β₁) ≤ (f*β₁)*d)
    (hlarge : (t:ℝ)*c ≤ (f*β₀)*(η*lower)) :
    ∃ C : CyclePacking G,
      (C.count:ℝ) ≤ ((Fintype.card V:ℝ)-lower)/2 ∧
      (C.singles:ℝ) ≤ incidentUpper+(Fintype.card V:ℝ)-lower := by
  have hnU : U.card ≤ Fintype.card V := card_le_univ U
  have hcap' : Fintype.card V-U.card ≤ c*t := by
    have hh : ((Fintype.card V-U.card:ℕ):ℝ) ≤ (c:ℝ)*t := by
      rw [Nat.cast_sub hnU]
      linarith [hU.order_lower]
    exact_mod_cast hh
  have hlarge' : (t:ℝ)*c ≤ (f*β₀)*(η*U.card) := hlarge.trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU.order_lower hη) h₀.le)
  obtain ⟨C,hcount,hsingles⟩ := cycles_of_sample_bank G U hU hlocal B c hc hcap'
    hf₀ hf₁ hL h₀ h₁ hsmall hlarge'
  have hcountR : 2*(C.count:ℝ) ≤ (Fintype.card V:ℝ)-U.card := by
    exact_mod_cast (show 2*C.count ≤ Fintype.card V-U.card from hcount)
  have hsinglesR : (C.singles:ℝ) ≤ (incidentEdgeCount G U:ℝ)+(Fintype.card V:ℝ)-U.card := by
    have hh := (Nat.cast_le (α:=ℝ)).mpr hsingles
    simpa only [Nat.cast_add,Nat.cast_sub hnU,add_sub_assoc] using hh
  exact ⟨C,by linarith [hU.order_lower],by linarith [hU.incident,hU.order_lower]⟩

end
end Cycle13
