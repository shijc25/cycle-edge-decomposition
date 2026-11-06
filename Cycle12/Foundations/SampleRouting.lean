import Cycle12.Foundations.SampleSuccess
import Cycle12.Foundations.BankCycleClosure

/-! Transfer the properties of one actual vertex sample to the routing
cuts. The two-scale branch argument is restricted to the reservoir;
vertices outside it are never counted in its order. -/
namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem internal_cutSize (G : SimpleGraph V) (U S : Finset V) (hSU : S⊆U) :
    cutSize (ReservoirPorts.internalGraph G U) S=(G.interedges S (U\S)).card := by
  rw [cutSize_eq_interedges]
  congr 1
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff,mem_compl,mem_sdiff]
  change (x∈S ∧ y∉S ∧ G.Adj x y ∧ x∈U ∧ y∈U) ↔
    (x∈S ∧ (y∈U ∧ y∉S) ∧ G.Adj x y)
  constructor
  · rintro ⟨hx,hy,hxy,_,hyU⟩
    exact ⟨hx,⟨hyU,hy⟩,hxy⟩
  · rintro ⟨hx,⟨hyU,hy⟩,hxy⟩
    exact ⟨hx,hy,hxy,hSU hx,hyU⟩

theorem internal_degree (G : SimpleGraph V) (U : Finset V) {v : V} (hv : v∈U) :
    (ReservoirPorts.internalGraph G U).degree v=(neighborsIn G v U).card := by
  rw [← ncard_neighborSet]
  have he : (ReservoirPorts.internalGraph G U).neighborSet v=(neighborsIn G v U:Set V) := by
    ext w
    simp only [mem_neighborSet,ReservoirPorts.internalGraph,neighborsIn,mem_coe,mem_filter,hv,true_and]
    exact and_comm
  rw [he,Set.ncard_coe_finset]

theorem reservoir_two_scale_branch_cut (G F : SimpleGraph V) (U B : Finset V)
    {β₀ β₁ η f d c : ℝ} (hf : 0 ≤ f) (hc : 0 ≤ c)
    (h₀ : 0 < f*β₀) (h₁ : 0 < f*β₁)
    (hglobal : SampleCutExpansion G U β₀)
    (hlocal : LocalSampleCutExpansion G U β₁ η)
    (hretain : ∀ S⊆U, f*cutSize (ReservoirPorts.internalGraph G U) S ≤
      (cutSize (ReservoirPorts.internalGraph F U) S:ℝ))
    (hdegree : ∀ v∈B, d ≤ ((ReservoirPorts.internalGraph F U).degree v:ℝ))
    (hsmall : c*(B.card+f*β₁) ≤ (f*β₁)*d)
    (hlarge : B.card*c ≤ (f*β₀)*(η*U.card))
    (S : Finset V) (hSU : S⊆U) (hS : 2*S.card ≤ U.card) :
    c*(B∩S).card ≤ (cutSize (ReservoirPorts.internalGraph F U) S:ℝ) := by
  rw [inter_comm B S]
  apply two_scale_branch_cut (Nat.cast_nonneg _)
    (by exact_mod_cast card_le_card (inter_subset_right (s₁:=S) (s₂:=B))) hc h₀ h₁
    (branch_degree_cut _ S B hdegree) ?_ ?_ hsmall hlarge
  · have hh := mul_le_mul_of_nonneg_left (hglobal S hSU hS) hf
    rw [← internal_cutSize G U S hSU] at hh
    simpa only [mul_assoc] using hh.trans (hretain S hSU)
  · intro hsize
    have hh := mul_le_mul_of_nonneg_left (hlocal S hSU hS hsize) hf
    rw [← internal_cutSize G U S hSU] at hh
    simpa only [mul_assoc] using hh.trans (hretain S hSU)

theorem close_paths_from_good_sample (G : SimpleGraph V) (U : Finset V)
    {δ β₀ β₁ η L lower upper edgeLower incidentUpper : ℝ}
    (hU : GoodVertexSample G U δ β₀ L lower upper edgeLower incidentUpper)
    (hlocal : LocalSampleCutExpansion G U β₁ η)
    (P : EndpointPathPacking G) (hPU : ∀ i, ∀ v∈(P.paths i).walk.support, v∉U)
    {t : ℕ} (M : WeakCliqueImmersion t G) (hb : ∀ r, M.branch r∈U)
    (hM : ∀ q : CliquePair t, ∀ v∈(M.route q).val.support, v∈U)
    (F : SimpleGraph V) (hFG : F≤G) (hFM : Disjoint F.edgeSet M.used)
    (c : ℕ) (hc : c ≤ 2*(t/6-2)) (hcap : 2*P.count ≤ c*t) {f d : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f*L)
    (h₀ : 0 < f*β₀) (h₁ : 0 < f*β₁)
    (hretain : ∀ S⊆U, f*cutSize (ReservoirPorts.internalGraph G U) S ≤
      (cutSize (ReservoirPorts.internalGraph F U) S:ℝ))
    (hdegree : ∀ i, d ≤ ((ReservoirPorts.internalGraph F U).degree (M.branch i):ℝ))
    (hsmall : (c:ℝ)*(t+f*β₁) ≤ (f*β₁)*d)
    (hlarge : (t:ℝ)*c ≤ (f*β₀)*(η*U.card)) :
    ∃ C : CyclePacking G, C.count=P.count ∧ P.used⊆C.used ∧
      C.singles ≤ P.singles ∧ C.cost ≤ 42*P.count+23*P.singles := by
  apply close_paths_from_bank_cuts P U hPU M hb hM F hFG hFM c hc hcap hf₀ hf₁ hL hretain
  · intro Y hY S hSU hS
    have hYU : Disjoint Y U := by
      apply Finset.disjoint_left.mpr
      intro v hv hvU
      obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_image.mp (hY hv)
      cases b
      · exact hPU i _ (P.paths i).walk.end_mem_support hvU
      · exact hPU i _ (P.paths i).walk.start_mem_support hvU
    simpa only [internal_cutSize G U S hSU,add_comm] using hU.anchoring Y S hYU hSU hS
  · intro S hSU hS
    have hh := reservoir_two_scale_branch_cut G F U M.branchFinset hf₀ (Nat.cast_nonneg c)
      h₀ h₁ hU.cuts hlocal hretain (fun v hv => by
        obtain ⟨i,_,rfl⟩ := mem_image.mp hv
        exact hdegree i)
      (by simpa only [M.branchFinset_card] using hsmall)
      (by simpa only [M.branchFinset_card] using hlarge) S hSU hS
    exact_mod_cast hh

end
end Cycle13
