import Cycle12.RepresentedCycleOutline12
import Cycle12.Foundations.DisjointBlockContraction

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem contractVertex_eq_inr_iff (A : I → Finset V) (x : V)
    (v : {v : V // v∉blockUnion A}) : contractVertex A x=Sum.inr v ↔ x=v.val := by
  constructor
  · intro h
    unfold contractVertex at h
    split_ifs at h with hx
    cases h
    rfl
  · rintro rfl
    exact contractVertex_of_not_mem A v.val v.property

namespace RepresentedCyclePorts12
variable {G : SimpleGraph V} {A : I → Finset V} {S : Set (Sym2 V)}
variable {Q : SimpleGraph (ContractedVertices A)} {a : ContractedVertices A} {p : Q.Walk a a}
variable (r : RepresentedCyclePorts12 (G:=G) (contractVertex A) S p) (hp : p.IsCycle)

theorem switch_is_block (z : (r.outline hp).Switch) : ∃ i,z.val=Sum.inl i := by
  cases hz : z.val with
  | inl i => exact ⟨i,rfl⟩
  | inr v =>
    have hs := r.projects z z.property.1
    have h₁ := (contractVertex_eq_inr_iff A (r.start z) v).mp (hs.1.trans hz)
    have h₂ := (contractVertex_eq_inr_iff A (r.finish z) v).mp (hs.2.trans hz)
    exact False.elim (z.property.2 (h₁.trans h₂.symm))

def switchOwner (z : (r.outline hp).Switch) : I := (r.switch_is_block hp z).choose

theorem switchOwner_eq (z : (r.outline hp).Switch) : z.val=Sum.inl (r.switchOwner hp z) :=
  (r.switch_is_block hp z).choose_spec

/-- A simple cycle in the full-block quotient has at most one demand
in any indexed core. This fails for the older pair-contraction quotient. -/
theorem switchOwner_injective : Function.Injective (r.switchOwner hp) := by
  intro z w hzw
  apply Subtype.ext
  rw [r.switchOwner_eq hp z,r.switchOwner_eq hp w,hzw]

theorem switch_endpoints_in_block
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (z : (r.outline hp).Switch) :
    r.start z∈A (r.switchOwner hp z) ∧ r.finish z∈A (r.switchOwner hp z) := by
  have hh := r.projects z z.property.1
  exact ⟨(contractVertex_eq_inl_iff A hd _ _).mp (hh.1.trans (r.switchOwner_eq hp z)),
    (contractVertex_eq_inl_iff A hd _ _).mp (hh.2.trans (r.switchOwner_eq hp z))⟩

/-- Every original port inside the current block is one of its own two
ports; other quotient vertices have different projection fibres. -/
theorem active_vertex_is_port (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (z : (r.outline hp).Switch) {v : V} (hv : v∈(r.outline hp).vertices)
    (ha : v∈A (r.switchOwner hp z)) : v=r.start z ∨ v=r.finish z := by
  letI : DecidableEq (ContractedVertices A) := fun x y => Classical.propDecidable (x=y)
  rw [outline_ports_union] at hv
  obtain ⟨w,hw,hv⟩ := mem_biUnion.mp hv
  have hw' := List.mem_toFinset.mp hw
  have hport : contractVertex A v=w := by
    rcases mem_insert.mp hv with hv | hv
    · exact hv ▸ (r.projects w hw').1
    · exact (mem_singleton.mp hv) ▸ (r.projects w hw').2
  have hwz : w=z.val := hport.symm.trans
    ((contractVertex_of_mem A hd ha).trans (r.switchOwner_eq hp z).symm)
  rw [hwz] at hv
  exact (mem_insert.mp hv).imp_right mem_singleton.mp

/-- Uncontracted ordinary vertices of an outline inject into its cyclic
quotient vertex sequence, which has exactly one vertex per original edge. -/
theorem ordinary_vertices_card_le :
    ((r.outline hp).vertices\blockUnion A).card≤p.length := by
  letI : DecidableEq (ContractedVertices A) := fun x y => Classical.propDecidable (x=y)
  rw [←outline_cyclic_order (r.outline hp)]
  apply Finset.card_le_card_of_injOn (contractVertex A)
  · intro v hv
    have hv' := (mem_sdiff.mp hv).1
    rw [outline_ports_union] at hv'
    obtain ⟨w,hw,hv'⟩ := mem_biUnion.mp hv'
    have hw' := List.mem_toFinset.mp hw
    have hport : contractVertex A v=w := by
      rcases mem_insert.mp hv' with hv | hv
      · exact hv ▸ (r.projects w hw').1
      · exact (mem_singleton.mp hv) ▸ (r.projects w hw').2
    rwa [hport]
  · intro v hv w hw he
    have hv' := (mem_sdiff.mp hv).2
    have hw' := (mem_sdiff.mp hw).2
    rw [contractVertex_of_not_mem A v hv',contractVertex_of_not_mem A w hw'] at he
    exact congrArg Subtype.val (Sum.inr.inj he)

end RepresentedCyclePorts12
end
end Cycle12
