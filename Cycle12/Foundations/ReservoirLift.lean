import Cycle12.Foundations.SampleRouting
import Cycle12.Foundations.WeakRecycling

/-! Exact transport between graphs on the sampled vertex type and the
original ambient vertex type. Edges, degrees, cuts and immersion routes
are transported by injections, with no loss in any numerical budget. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def reservoirEmbedding (U : Finset V) : U ↪ V := ⟨Subtype.val,Subtype.val_injective⟩

@[simp] theorem reservoirEmbedding_apply (U : Finset V) (v : U) :
    reservoirEmbedding U v=v.val := rfl

def reservoirLift (U : Finset V) (H : SimpleGraph U) : SimpleGraph V :=
  H.map (reservoirEmbedding U)

def reservoirSide (U S : Finset V) : Finset U := univ.filter (fun v => v.val∈S)

@[simp] theorem mem_reservoirSide (U S : Finset V) (v : U) :
    v∈reservoirSide U S ↔ v.val∈S := by simp [reservoirSide]

theorem reservoirSide_card (U S : Finset V) (hSU : S⊆U) :
    (reservoirSide U S).card=S.card := by
  have he : (reservoirSide U S).image Subtype.val=S := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_reservoirSide U S w).mp hw
    · intro hv
      exact mem_image.mpr ⟨⟨v,hSU hv⟩,(mem_reservoirSide U S _).mpr hv,rfl⟩
  have hh := congrArg Finset.card he
  rw [card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reservoirLift_le (G : SimpleGraph V) (U : Finset V) (H : SimpleGraph U)
    (hHG : H≤G.induce (U:Set V)) : reservoirLift U H≤G := by
  intro x y hxy
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj (reservoirEmbedding U) H x y).mp hxy
  exact hHG hab

theorem reservoirLift_internal (U : Finset V) (H : SimpleGraph U) :
    ReservoirPorts.internalGraph (reservoirLift U H) U=reservoirLift U H := by
  ext x y
  constructor
  · exact fun h => h.1
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj (reservoirEmbedding U) H x y).mp h
    exact ⟨h,a.property,b.property⟩

theorem reservoirLift_induce (G : SimpleGraph V) (U : Finset V) :
    reservoirLift U (G.induce (U:Set V))=ReservoirPorts.internalGraph G U := by
  ext x y
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩ :=
      (SimpleGraph.map_adj (reservoirEmbedding U) (G.induce (U:Set V)) x y).mp h
    exact ⟨hab,a.property,b.property⟩
  · rintro ⟨h,hx,hy⟩
    exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨⟨x,hx⟩,⟨y,hy⟩,h,rfl,rfl⟩

theorem reservoirLift_degree (U : Finset V) (H : SimpleGraph U) (v : U) :
    (reservoirLift U H).degree v.val=H.degree v := by
  rw [← (reservoirLift U H).ncard_neighborSet v.val,← H.ncard_neighborSet v]
  change ((H.map (reservoirEmbedding U)).neighborSet (reservoirEmbedding U v)).ncard=(H.neighborSet v).ncard
  rw [SimpleGraph.neighborSet_map,Set.ncard_image_of_injective _ (reservoirEmbedding U).injective]

theorem reservoirLift_cutGraph (U S : Finset V) (H : SimpleGraph U) :
    cutGraph (reservoirLift U H) S=reservoirLift U (cutGraph H (reservoirSide U S)) := by
  ext x y
  constructor
  · rintro ⟨h,hside⟩
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj (reservoirEmbedding U) H x y).mp h
    apply (SimpleGraph.map_adj _ _ _ _).mpr
    refine ⟨a,b,⟨hab,?_⟩,rfl,rfl⟩
    simpa only [mem_coe,Set.mem_compl_iff,mem_reservoirSide,reservoirEmbedding_apply] using hside
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩ :=
      (SimpleGraph.map_adj (reservoirEmbedding U) (cutGraph H (reservoirSide U S)) x y).mp h
    refine ⟨(SimpleGraph.map_adj _ _ _ _).mpr ⟨a,b,hab.1,rfl,rfl⟩,?_⟩
    simpa only [mem_coe,Set.mem_compl_iff,mem_reservoirSide,reservoirEmbedding_apply] using hab.2

theorem reservoirLift_cutSize (U S : Finset V) (H : SimpleGraph U) :
    cutSize (reservoirLift U H) S=cutSize H (reservoirSide U S) := by
  rw [cutSize,reservoirLift_cutGraph,reservoirLift,SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _ (reservoirEmbedding U).sym2Map.injective]
  rfl

theorem reservoirLift_retains_cuts (G : SimpleGraph V) (U : Finset V)
    (H : SimpleGraph U) {f : ℝ}
    (hcut : ∀ S : Finset U, f*cutSize (G.induce (U:Set V)) S ≤ (cutSize H S:ℝ)) :
    ∀ S⊆U, f*cutSize (ReservoirPorts.internalGraph G U) S ≤
      (cutSize (ReservoirPorts.internalGraph (reservoirLift U H) U) S:ℝ) := by
  intro S _
  rw [reservoirLift_internal,← reservoirLift_induce,reservoirLift_cutSize,reservoirLift_cutSize]
  exact hcut _

namespace WeakCliqueImmersion
variable {W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {t : ℕ}

def mapCopy (M : WeakCliqueImmersion t H) (f : H.Copy G) : WeakCliqueImmersion t G where
  branch := M.branch.trans f.toEmbedding
  route q := ⟨(M.route q).val.map f.toHom,(M.route q).property.map f.injective⟩
  disjoint := by
    intro q r hqr
    change Disjoint ((M.route q).val.map f.toHom).edgeSet ((M.route r).val.map f.toHom).edgeSet
    rw [(M.route q).val.edgeSet_map f.toHom,(M.route r).val.edgeSet_map f.toHom]
    apply Set.disjoint_left.mpr
    rintro e ⟨a,ha,he⟩ ⟨b,hb,hf⟩
    have hab := Sym2.map.injective f.injective (he.trans hf.symm)
    subst b
    exact Set.disjoint_left.mp (M.disjoint hqr) ha hb

theorem used_mapCopy (M : WeakCliqueImmersion t H) (f : H.Copy G) :
    (M.mapCopy f).used=Sym2.map f '' M.used := by
  change (⋃ q, ((M.route q).val.map f.toHom).edgeSet)=Sym2.map f '' (⋃ q, (M.route q).val.edgeSet)
  simp_rw [Walk.edgeSet_map]
  rw [Set.image_iUnion]
  rfl

theorem mapCopy_inside (U : Finset V) (M : WeakCliqueImmersion t (G.induce (U:Set V))) :
    ∀ q : CliquePair t, ∀ v∈((M.mapCopy (SimpleGraph.Copy.induce G (U:Set V))).route q).val.support,
      v∈U := by
  intro q v hv
  change v∈((M.route q).val.map (SimpleGraph.Copy.induce G (U:Set V)).toHom).support at hv
  rw [Walk.support_map] at hv
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
  exact w.property

theorem reservoirLift_residue_disjoint (U : Finset V)
    (M : WeakCliqueImmersion t (G.induce (U:Set V))) :
    Disjoint (reservoirLift U M.residue).edgeSet
      (M.mapCopy (SimpleGraph.Copy.induce G (U:Set V))).used := by
  rw [reservoirLift,SimpleGraph.edgeSet_map,used_mapCopy]
  apply Set.disjoint_left.mpr
  rintro e ⟨a,ha,he⟩ ⟨b,hb,hf⟩
  have hab := Sym2.map.injective Subtype.val_injective (he.trans hf.symm)
  subst b
  exact Set.disjoint_left.mp M.residue_disjoint_used ha hb

end WeakCliqueImmersion
end
end Cycle13
