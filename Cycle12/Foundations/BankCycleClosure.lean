import Cycle12.Foundations.GMMReservoirClosure
import Cycle12.Foundations.ReservoirRouting

/-! From the actual routing bank and its proved cut conditions to actual
cycles. Endpoint and branch index sets are assembled here, and the GMM
capacity is checked against the injectively occupied routing slots. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

def EndpointPathPacking.sources (P : EndpointPathPacking G) : Finset V := univ.image P.endpoint

def EndpointPathPacking.sourceEmbedding (P : EndpointPathPacking G) : Fin P.count × Bool ↪ P.sources where
  toFun k := ⟨P.endpoint k,mem_image.mpr ⟨k,mem_univ _,rfl⟩⟩
  inj' := fun _ _ h => P.endpoint_injective (congrArg Subtype.val h)

theorem EndpointPathPacking.sources_card (P : EndpointPathPacking G) : P.sources.card=2*P.count := by
  rw [sources,card_image_of_injective _ (show Function.Injective P.endpoint from P.endpoint_injective),card_univ,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm]

def WeakCliqueImmersion.branchFinset (M : WeakCliqueImmersion t G) : Finset V := univ.image M.branch

theorem WeakCliqueImmersion.branchFinset_card (M : WeakCliqueImmersion t G) : M.branchFinset.card=t := by
  rw [branchFinset,card_image_of_injective _ M.branch.injective,card_univ,Fintype.card_fin]

def WeakCliqueImmersion.branchLabel (M : WeakCliqueImmersion t G) (v : M.branchFinset) : Fin t :=
  (mem_image.mp v.property).choose

theorem WeakCliqueImmersion.branchLabel_spec (M : WeakCliqueImmersion t G) (v : M.branchFinset) :
    M.branch (M.branchLabel v)=v.val := (mem_image.mp v.property).choose_spec.2

theorem slot_injective_load {I T : Type} [Fintype I] [DecidableEq T]
    (f : I → T) {c : ℕ} (slot : I → Fin c)
    (hi : Function.Injective (fun i => (f i,slot i))) (r : T) :
    (univ.filter (fun i => f i=r)).card ≤ c := by
  let A := univ.filter (fun i => f i=r)
  have hinj : Function.Injective (fun i : A => slot i.val) := by
    intro i j h
    apply Subtype.ext
    exact hi (Prod.ext ((mem_filter.mp i.property).2.trans (mem_filter.mp j.property).2.symm) h)
  have hh := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_coe,Fintype.card_fin,A] using hh

theorem routingGraph_avoids_model (M : WeakCliqueImmersion t G) (F : SimpleGraph V)
    (A U : Finset V) (hAU : Disjoint A U) (hFM : Disjoint F.edgeSet M.used)
    (hM : ∀ q : CliquePair t, ∀ v∈(M.route q).val.support, v∈U) :
    Disjoint (ReservoirPorts.routingGraph G F A U).edgeSet M.used := by
  apply Set.disjoint_left.mpr
  intro e he hm
  obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hm
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxU := hM q x ((M.route q).val.fst_mem_support_of_mem_edges hq)
    have hyU := hM q y ((M.route q).val.snd_mem_support_of_mem_edges hq)
    change (F.Adj x y ∧ x∈U ∧ y∈U) ∨
      (G.Adj x y ∧ (x∈A ∧ y∈U ∨ x∈U ∧ y∈A)) at he
    rcases he with he | he
    · exact Set.disjoint_left.mp hFM he.1 (Set.mem_iUnion.mpr ⟨q,hq⟩)
    · rcases he.2 with h | h
      · exact disjoint_left.mp hAU h.1 hxU
      · exact disjoint_left.mp hAU h.2 hyU

theorem close_paths_from_reservoir_routing (P : EndpointPathPacking G) (U : Finset V)
    (hPU : ∀ i, ∀ v∈(P.paths i).walk.support, v∉U)
    (M : WeakCliqueImmersion t G) (hb : ∀ r, M.branch r∈U)
    (hM : ∀ q : CliquePair t, ∀ v∈(M.route q).val.support, v∈U)
    (F : SimpleGraph V) (hFG : F≤G) (hFM : Disjoint F.edgeSet M.used)
    {c : ℕ} (hc : c ≤ 2*(t/6-2))
    (R : ReservoirPorts.Routing (ReservoirPorts.routingGraph G F P.sources U)
      P.sources U M.branchFinset c) :
    ∃ C : CyclePacking G, C.count=P.count ∧ P.used⊆C.used ∧
      C.singles ≤ P.singles ∧ C.cost ≤ 42*P.count+23*P.singles := by
  let source := P.sourceEmbedding
  let label := fun k => M.branchLabel (R.branch (source k))
  have hlabel : ∀ k, M.branch (label k)=(R.branch (source k)).val :=
    fun k => M.branchLabel_spec _
  let fan : ∀ k, G.Walk (P.endpoint k) (M.branch (label k)) := fun k =>
    ((R.path (source k)).mapLe (ReservoirPorts.routingGraph_le hFG P.sources U)).copy
      rfl (hlabel k).symm
  have hfanEdge : ∀ k, (fan k).edgeSet=(R.path (source k)).edgeSet := by
    intro k
    exact (Walk.edgeSet_copy _ rfl (hlabel k).symm).trans (Walk.edgeSet_mapLe_eq_edgeSet _ _)
  have hfanSupport : ∀ k, (fan k).support=(R.path (source k)).support := by
    intro k
    exact (Walk.support_copy _ rfl (hlabel k).symm).trans (Walk.support_mapLe_eq_support _ _)
  have hAU : Disjoint P.sources U := by
    apply Finset.disjoint_left.mpr
    intro v hv hvU
    obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_image.mp hv
    cases b
    · exact hPU i _ (P.paths i).walk.end_mem_support hvU
    · exact hPU i _ (P.paths i).walk.start_mem_support hvU
  have hdis := routingGraph_avoids_model M F P.sources U hAU hFM hM
  have hslots : Function.Injective (fun k => (label k,R.slot (source k))) := by
    intro k l he
    change (label k,R.slot (source k))=(label l,R.slot (source l)) at he
    have hfirst : label k=label l := congrArg Prod.fst he
    have hsecond : R.slot (source k)=R.slot (source l) := congrArg Prod.snd he
    apply source.injective
    apply R.slot_injective
    refine Prod.ext ?_ hsecond
    apply Subtype.ext
    rw [← hlabel k,← hlabel l,hfirst]
  apply close_paths_via_gmm P U hPU M hb hM label fan
  · intro k v hv
    exact R.tail_inside (source k) v (by simpa only [hfanSupport] using hv)
  · intro k l hkl
    simpa only [hfanEdge] using
      R.disjoint (source.injective.ne hkl)
  · intro k
    rw [hfanEdge]
    exact hdis.mono_left (R.path (source k)).edges_subset_edgeSet
  · intro r
    exact (slot_injective_load label (fun k => R.slot (source k)) hslots r).trans hc

theorem close_paths_from_bank_cuts (P : EndpointPathPacking G) (U : Finset V)
    (hPU : ∀ i, ∀ v∈(P.paths i).walk.support, v∉U)
    (M : WeakCliqueImmersion t G) (hb : ∀ r, M.branch r∈U)
    (hM : ∀ q : CliquePair t, ∀ v∈(M.route q).val.support, v∈U)
    (F : SimpleGraph V) (hFG : F≤G) (hFM : Disjoint F.edgeSet M.used)
    (c : ℕ) (hc : c ≤ 2*(t/6-2)) (hcap : 2*P.count ≤ c*t) {f L : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f*L)
    (hretain : ∀ S : Finset V, S⊆U →
      f*cutSize (ReservoirPorts.internalGraph G U) S ≤
        (cutSize (ReservoirPorts.internalGraph F U) S : ℝ))
    (hanchor : ∀ Y : Finset V, Y⊆P.sources → ∀ S : Finset V, S⊆U → 2*S.card ≤ U.card →
      L*Y.card ≤ (cutSize (ReservoirPorts.internalGraph G U) S : ℝ)+(G.interedges Y (U\S)).card)
    (hbranch : ∀ S : Finset V, S⊆U → 2*S.card ≤ U.card →
      c*(M.branchFinset∩S).card ≤ cutSize (ReservoirPorts.internalGraph F U) S) :
    ∃ C : CyclePacking G, C.count=P.count ∧ P.used⊆C.used ∧
      C.singles ≤ P.singles ∧ C.cost ≤ 42*P.count+23*P.singles := by
  have hAU : Disjoint P.sources U := by
    apply Finset.disjoint_left.mpr
    intro v hv hvU
    obtain ⟨⟨i,b⟩,_,rfl⟩ := mem_image.mp hv
    cases b
    · exact hPU i _ (P.paths i).walk.end_mem_support hvU
    · exact hPU i _ (P.paths i).walk.start_mem_support hvU
  have hBU : M.branchFinset⊆U := by
    intro v hv
    obtain ⟨r,_,rfl⟩ := mem_image.mp hv
    exact hb r
  obtain ⟨R⟩ := ReservoirPorts.exists_routing_in_bank G F P.sources U M.branchFinset c hFG hAU hBU
    (by rw [P.sources_card,M.branchFinset_card]; exact hcap) hf₀ hf₁ hL hretain hanchor hbranch
  exact close_paths_from_reservoir_routing P U hPU M hb hM F hFG hFM hc R

end
end Cycle13
