import Cycle12.ActualBoxRoutes12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sum_port_indicator (U A : Finset V) (S : Finset U) :
    (∑ x∈S,if x.val∈A then (1:ℝ) else 0)=((S.image Subtype.val∩A).card:ℝ) := by
  rw [Finset.sum_boole]
  have he : (S.filter (fun x => x.val∈A)).image Subtype.val=S.image Subtype.val∩A := by
    ext v
    simp only [mem_image,mem_filter,mem_inter]
    constructor
    · rintro ⟨x,⟨hx,ha⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,ha⟩
    · rintro ⟨⟨x,hx,rfl⟩,ha⟩
      exact ⟨x,⟨hx,ha⟩,rfl⟩
  rw [←he,card_image_of_injective _ Subtype.val_injective]

theorem subtype_univ_image (U : Finset V) : (univ : Finset U).image Subtype.val=U := by
  ext v
  simp

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def quotientRoutingCores (t : F.BatchIndex) (j : (F.active t.1).Index t.2) : Finset V :=
  ((L.foldCores i t.1).get ((F.active t.1).router t.2 j)).vertices

theorem quotientRoutingCores_disjoint (hi : i≤L.stopIndex) (t : F.BatchIndex) :
    Pairwise (fun j k => Disjoint (F.quotientRoutingCores t j) (F.quotientRoutingCores t k)) := by
  intro j k hjk
  exact L.fold_core_vertices_disjoint hi t.1 ((F.injective t.1 t.2).ne hjk)

theorem quotientRoutingCores_contain (t : F.BatchIndex) (j : (F.active t.1).Index t.2) :
    F.ambientBatchActive t j⊆F.quotientRoutingCores t j := (F.active t.1).subset_router t.2 j

def quotientRequest (hi : i≤L.stopIndex) (t : F.BatchIndex) (k : (D t).RequestIndex) :
    F.ActualCoreRequest P Q D hi ⟨t.1,F.quotientSwitchCore (D t) k.1 k.2⟩ :=
  ⟨Sum.inr (Sum.inr ⟨t.2,k⟩),rfl⟩

def actualQuotientRoute (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) (z : ((D t).outline j).Switch) :
    G.Walk (((D t).outline j).start z) (((D t).outline j).finish z) :=
  F.boxRoute P Q D hi t.1 (Sum.inr (Sum.inr ⟨t.2,⟨j,z⟩⟩))

theorem actualQuotientRoute_support (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) (z : ((D t).outline j).Switch) {v : V}
    (hv : v∈(F.actualQuotientRoute P Q D hi t j z).support) :
    v∈F.quotientRoutingCores t ((D t).ports j |>.switchOwner ((D t).isCycle j) z) :=
  F.boxRoute_support P Q D hi t.1 _ hv

theorem actualQuotientRoute_edges_disjoint (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) : Pairwise (fun z w : ((D t).outline j).Switch =>
      Disjoint (F.actualQuotientRoute P Q D hi t j z).edgeSet
        (F.actualQuotientRoute P Q D hi t j w).edgeSet) := by
  intro z w hzw
  apply F.boxRoute_edges_disjoint P Q D hi t.1
  intro he
  have hb := eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Sum.inr.inj he))).2
  exact hzw (eq_of_heq (Sigma.mk.inj hb).2)

theorem actualQuotientRoute_interior_bank (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) (z : ((D t).outline j).Switch) :
    routeInterior (F.actualQuotientRoute P Q D hi t j z)=
      (routeInterior (F.actualBankPaths P Q D hi ⟨t.1,F.quotientSwitchCore (D t) j z⟩
        (F.quotientRequest P Q D hi t ⟨j,z⟩))).image Subtype.val := by
  exact routeInterior_map_injective (F.actualBankHom hi _) Subtype.val_injective _

/-- The soft weight in the common router is exactly the indicator of
ordinary outline vertices in the actual selected core. -/
theorem actualQuotientRoute_soft (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) (z : ((D t).outline j).Switch) :
    ((routeInterior (F.actualQuotientRoute P Q D hi t j z)∩
      ((D t).ports j).softVertices ((D t).isCycle j) (F.quotientRoutingCores t) z).card:ℝ)≤
      (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*
        (((D t).ports j).softVertices ((D t).isCycle j) (F.quotientRoutingCores t) z).card := by
  let r : L.FoldCoreIndex i := ⟨t.1,F.quotientSwitchCore (D t) j z⟩
  let req := F.quotientRequest P Q D hi t ⟨j,z⟩
  let U := (L.foldCorePiece i r).vertices
  let A := ((D t).outline j).vertices\blockUnion (F.ambientBatchActive t)
  have hh := ((F.actualBankPaths_spec P Q D hi r).1 req).2.2.2
  change (∑ v∈routeInterior (F.actualBankPaths P Q D hi r req),if v.val∈A then (1:ℝ) else 0)≤
    (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*
      ∑ v : U,if v.val∈A then (1:ℝ) else 0 at hh
  rw [sum_port_indicator,sum_port_indicator,subtype_univ_image] at hh
  rw [←F.actualQuotientRoute_interior_bank P Q D hi t j z] at hh
  have hsoft : ((D t).ports j).softVertices ((D t).isCycle j) (F.quotientRoutingCores t) z=A∩U := rfl
  have hint : routeInterior (F.actualQuotientRoute P Q D hi t j z)∩(A∩U)=
      routeInterior (F.actualQuotientRoute P Q D hi t j z)∩A := by
    ext v
    simp only [mem_inter]
    constructor
    · exact fun h => ⟨h.1,h.2.1⟩
    · intro hv
      exact ⟨hv.1,hv.2,F.actualQuotientRoute_support P Q D hi t j z
        ((mem_routeInterior_iff _ _).mp hv.1).1⟩
  rw [hsoft,hint]
  simpa only [Finset.inter_comm] using hh

/-- An actual quotient cycle is closed using the common mixed routes,
with no extra cost per switch. Its only surcharge is the soft collision budget. -/
theorem actual_quotient_cycle_closure (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (j : Fin (Q t).count) :
    ∃ T : CyclePacking G,T.used=((D t).outline j).edges∪
      (⋃ z,(F.actualQuotientRoute P Q D hi t j z).edgeSet) ∧
      (T.count:ℝ)≤1+(gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*
        ((D t).walk j).length := by
  apply ((D t).ports j).contracted_soft_packing ((D t).isCycle j) (F.quotientRoutingCores t)
    (F.quotientRoutingCores_disjoint hi t) (F.quotientRoutingCores_contain t)
    (F.actualQuotientRoute P Q D hi t j)
  · intro z v hv
    exact F.actualQuotientRoute_support P Q D hi t j z ((mem_routeInterior_iff _ _).mp hv).1
  · exact fun z => F.boxRoute_isPath P Q D hi t.1 _
  · exact F.actualQuotientRoute_edges_disjoint P Q D hi t j
  · intro z
    apply (F.boxRoute_descendant_disjoint P Q D hi t.1 _ t.1).symm.mono _ subset_rfl
    exact (D t).outline_subset (F.ambient_quotient_unique P t) j |>.trans
      (edgeSet_mono ((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2)))
  · exact div_nonneg (by norm_num [gamma]) (Nat.cast_nonneg _)
  · exact F.actualQuotientRoute_soft P Q D hi t j

end ActualFoldStage12
end
end Cycle12.Even12
