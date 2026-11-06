import Cycle12.Foundations.PathPacking
import Cycle12.Foundations.IncidentSampleEdges

/-! The outside paths used by reservoir closure, constructed from the
induced graph on the complement of the actual sample. Exact edge counts
charge all other original edges to the incident-edge budget. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W]

namespace EndpointPathPacking
variable {G : SimpleGraph V} {H : SimpleGraph W}

def mapCopy (P : EndpointPathPacking H) (f : H.Copy G) : EndpointPathPacking G where
  count := P.count
  paths i := {
    start := f (P.paths i).start
    finish := f (P.paths i).finish
    walk := (P.paths i).walk.map f.toHom
    isPath := (P.paths i).isPath.map f.injective
    positive := by simpa only [Walk.length_map] using (P.paths i).positive }
  disjoint := by
    intro i j hij
    simp only [Walk.edgeSet_map]
    apply Set.disjoint_left.mpr
    rintro e ⟨a,ha,he⟩ ⟨b,hb,hf⟩
    have hab := Sym2.map.injective f.injective (he.trans hf.symm)
    subst b
    exact Set.disjoint_left.mp (P.disjoint hij) ha hb
  endpoint_injective := by
    rintro ⟨i,b⟩ ⟨j,c⟩ hij
    apply P.endpoint_injective
    cases b <;> cases c <;> exact f.injective hij

theorem used_mapCopy (P : EndpointPathPacking H) (f : H.Copy G) :
    (P.mapCopy f).used=Sym2.map f '' P.used := by
  simp only [used,mapCopy,Walk.edgeSet_map,SimpleGraph.Copy.coe_toHom,Set.image_iUnion]

end EndpointPathPacking

variable [DecidableEq V]

def ambientIncidentEdges (G : SimpleGraph V) (U : Finset V) : Set (Sym2 V) :=
  Subtype.val '' (incidentSampleEdges G U:Set G.edgeSet)

theorem ambientIncidentEdges_ncard (G : SimpleGraph V) (U : Finset V) :
    (ambientIncidentEdges G U).ncard=incidentEdgeCount G U := by
  rw [ambientIncidentEdges,Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]
  rfl

theorem outside_or_incident (G : SimpleGraph V) (U : Finset V) :
    G.edgeSet ⊆ Sym2.map (Subtype.val : ((Uᶜ:Finset V):Set V)→V) ''
      (G.induce ((Uᶜ:Finset V):Set V)).edgeSet ∪ ambientIncidentEdges G U := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    by_cases hx : x∈U
    · exact Or.inr ⟨⟨s(x,y),he⟩,mem_filter.mpr
        ⟨mem_univ _,x,hx,Sym2.mem_mk_left _ _⟩,rfl⟩
    · by_cases hy : y∈U
      · exact Or.inr ⟨⟨s(x,y),he⟩,mem_filter.mpr
          ⟨mem_univ _,y,hy,Sym2.mem_mk_right _ _⟩,rfl⟩
      · exact Or.inl ⟨s((⟨x,mem_compl.mpr hx⟩:((Uᶜ:Finset V):Set V)),⟨y,mem_compl.mpr hy⟩),he,rfl⟩

theorem external_path_singles (G : SimpleGraph V) (U : Finset V)
    (P : EndpointPathPacking (G.induce ((Uᶜ:Finset V):Set V))) :
    (P.mapCopy (SimpleGraph.Copy.induce G ((Uᶜ:Finset V):Set V))).singles ≤
      P.singles+incidentEdgeCount G U := by
  let f := SimpleGraph.Copy.induce G ((Uᶜ:Finset V):Set V)
  have hsub : G.edgeSet\(P.mapCopy f).used ⊆
      Sym2.map f '' ((G.induce ((Uᶜ:Finset V):Set V)).edgeSet\P.used) ∪ ambientIncidentEdges G U := by
    rintro e ⟨he,hn⟩
    rcases outside_or_incident G U he with ⟨a,ha,rfl⟩ | hi
    · apply Or.inl
      refine ⟨a,⟨ha,?_⟩,rfl⟩
      intro hp
      apply hn
      rw [EndpointPathPacking.used_mapCopy]
      exact ⟨a,hp,rfl⟩
    · exact Or.inr hi
  calc
    _ ≤ (Sym2.map f '' ((G.induce ((Uᶜ:Finset V):Set V)).edgeSet\P.used) ∪ ambientIncidentEdges G U).ncard :=
      Set.ncard_le_ncard hsub
    _ ≤ (Sym2.map f '' ((G.induce ((Uᶜ:Finset V):Set V)).edgeSet\P.used)).ncard+
        (ambientIncidentEdges G U).ncard := Set.ncard_union_le _ _
    _ = _ := by rw [Set.ncard_image_of_injective _
      (Sym2.map.injective (show Function.Injective f from f.injective)),
      ambientIncidentEdges_ncard]; rfl

theorem exists_external_path_packing (G : SimpleGraph V) (U : Finset V) :
    ∃ P : EndpointPathPacking G,
      (∀ i, ∀ v∈(P.paths i).walk.support, v∉U) ∧
      2*P.count ≤ Fintype.card V-U.card ∧
      P.singles ≤ incidentEdgeCount G U+(Fintype.card V-U.card) := by
  obtain ⟨P,hP⟩ := exists_distinct_endpoint_path_packing (G.induce ((Uᶜ:Finset V):Set V))
  let f := SimpleGraph.Copy.induce G ((Uᶜ:Finset V):Set V)
  refine ⟨P.mapCopy f,?_,?_,?_⟩
  · intro i v hv
    change v∈((P.paths i).walk.map f.toHom).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
    exact mem_compl.mp w.property
  · have hh := P.count_bound
    simpa only [EndpointPathPacking.mapCopy,Set.fintypeCard_eq_ncard,Set.ncard_coe_finset,card_compl] using hh
  · have hh := external_path_singles G U P
    have hp' : P.singles ≤ Fintype.card V-U.card := by
      have hz := hP.trans (Nat.sub_le _ _)
      simpa only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset,card_compl] using hz
    exact hh.trans (by omega)

end
end Cycle13
