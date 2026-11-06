import Cycle12.ActualAmbientQuotients12
import Cycle12.QuotientOutlineFamily12
import Cycle12.ActualCoreRouting12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V J : Type} [Fintype V] [Fintype J] [DecidableEq V]

/-- A certificate's recorded original edges determine the graph in which
its incidence load is measured. This allows the whole parent descendant
graph, even when the represented cycles are drawn in the ambient graph. -/
def OriginalEndpointCertificate.onGraph {G H : SimpleGraph V} {a b : J → V} {S : Set (Sym2 V)}
    (P : OriginalEndpointCertificate G a b S) (hS : S⊆H.edgeSet) : OriginalEndpointCertificate H a b S :=
  ⟨P.neighbor,fun k => hS (P.mem k),P.mem,P.injective⟩

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.fold_parent_le_original {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (z : L.FoldBoxIndex i) : (L.foldParent i z).graph ≤ G :=
  partition_member_le (past_partition L.splitter 0 i (originalPiece G))
    (List.mem_append_right _ (List.mem_map.mpr ⟨_,L.foldParent_mem i z,rfl⟩))

theorem EvenScaleLayers12.fold_core_le_original {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (i : ℕ) (r : L.FoldCoreIndex i) : (L.foldCorePiece i r).graph ≤ G :=
  (L.fold_core_le_box i r.1 r.2).trans ((L.fold_box_le_parent i r.1).trans (L.fold_parent_le_original i r.1))

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

theorem batch_graph_le_original (F : ActualFoldStage12 L i) (t : F.BatchIndex) : F.batchGraph t ≤ G :=
  ((F.batches t.1).graph_le t.2).trans ((L.fold_descendant_le_box i t.1).trans
    ((L.fold_box_le_parent i t.1).trans (L.fold_parent_le_original i t.1)))

def AmbientQuotientPacking (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (t : F.BatchIndex) :=
  CyclePacking ((F.ambientBatchRetained P t).map (contractVertex (F.ambientBatchActive t)))

def AmbientOutlineData (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (Q : ∀ t,F.AmbientQuotientPacking P t) (t : F.BatchIndex) :=
  QuotientOutlineFamily12 G (F.ambientBatchRetained P t) (contractVertex (F.ambientBatchActive t)) (Q t)

theorem ambient_outline_data_exists (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (Q : ∀ t,F.AmbientQuotientPacking P t) (t : F.BatchIndex) : Nonempty (F.AmbientOutlineData P Q t) :=
  quotientOutlineFamily_exists G (F.ambientBatchRetained P t) (contractVertex (F.ambientBatchActive t))
    ((F.ambient_retained_le P t).trans (F.batch_graph_le_original t)) (F.ambient_quotient_proper P t) (Q t)

def actualOutlineData (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (Q : ∀ t,F.AmbientQuotientPacking P t) (t : F.BatchIndex) : F.AmbientOutlineData P Q t :=
  Classical.choice (F.ambient_outline_data_exists P Q t)

def quotientSwitchCore (F : ActualFoldStage12 L i) {P : ∀ t,F.BatchPreparation t}
    {Q : ∀ t,F.AmbientQuotientPacking P t} {t : F.BatchIndex} (D : F.AmbientOutlineData P Q t)
    (j : Fin (Q t).count) (z : (D.outline j).Switch) : Fin (L.foldCores i t.1).length :=
  (F.active t.1).router t.2 ((D.ports j).switchOwner (D.isCycle j) z)

theorem quotientSwitchCore_injective (F : ActualFoldStage12 L i) {P : ∀ t,F.BatchPreparation t}
    {Q : ∀ t,F.AmbientQuotientPacking P t} {t : F.BatchIndex} (D : F.AmbientOutlineData P Q t)
    (j : Fin (Q t).count) : Function.Injective (F.quotientSwitchCore D j) :=
  (F.injective t.1 t.2).comp ((D.ports j).switchOwner_injective (D.isCycle j))

/-- Every actual quotient request has both endpoints in its assigned
selected core and in the parent-wide good vertex set. -/
theorem quotientSwitch_endpoints (F : ActualFoldStage12 L i) {P : ∀ t,F.BatchPreparation t}
    {Q : ∀ t,F.AmbientQuotientPacking P t} {t : F.BatchIndex} (D : F.AmbientOutlineData P Q t)
    (j : Fin (Q t).count) (z : (D.outline j).Switch) :
    (D.outline j).start z∈((L.foldCores i t.1).get (F.quotientSwitchCore D j z)).vertices ∧
    (D.outline j).finish z∈((L.foldCores i t.1).get (F.quotientSwitchCore D j z)).vertices ∧
    (D.outline j).start z∈F.activeVertices t.1 ∧ (D.outline j).finish z∈F.activeVertices t.1 := by
  have hp := (D.ports j).switch_endpoints_in_block (D.isCycle j) ((F.active t.1).disjoint t.2) z
  let r := (D.ports j).switchOwner (D.isCycle j) z
  refine ⟨(F.active t.1).subset_router t.2 r hp.1,(F.active t.1).subset_router t.2 r hp.2,?_,?_⟩
  · exact mem_biUnion.mpr ⟨t.2,mem_univ _,mem_biUnion.mpr ⟨r,mem_univ _,hp.1⟩⟩
  · exact mem_biUnion.mpr ⟨t.2,mem_univ _,mem_biUnion.mpr ⟨r,mem_univ _,hp.2⟩⟩

/-- The joint certificate for all quotient switches in one actual batch
is measured in the whole parent descendant graph. -/
def quotient_certificate (F : ActualFoldStage12 L i) {P : ∀ t,F.BatchPreparation t}
    {Q : ∀ t,F.AmbientQuotientPacking P t} {t : F.BatchIndex} (D : F.AmbientOutlineData P Q t) :
    OriginalEndpointCertificate (L.foldDescendantGraph i t.1)
      (fun k : D.RequestIndex => (D.outline k.1).start k.2)
      (fun k => (D.outline k.1).finish k.2) (⋃ j,(D.outline j).edges) :=
  (D.certificate (F.ambient_quotient_unique P t)).onGraph (by
    intro e he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact edgeSet_mono (((F.ambient_retained_le P t).trans ((F.batches t.1).graph_le t.2)))
      (D.outline_subset (F.ambient_quotient_unique P t) j hj))

end ActualFoldStage12
end
end Cycle12.Even12
