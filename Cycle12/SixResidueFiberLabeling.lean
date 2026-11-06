import Cycle12.SixResidueParameterCoverage
import Cycle12.SixCycleResidueOrder

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure SixSpokeLabels (G : SimpleGraph V) (f : Fin 6 ↪ V) (t : Fin 14) where
  counts : Fin 4 → Fin 3
  vertex : ∀ j, Fin (counts j).val → V
  valid : ∀ j, match sixResidueSlot t j with
    | none => counts j=0
    | some i => (counts j).val ≤ if i.val<9 then 1 else 2
  typed : ∀ j k, ∃ i, sixResidueSlot t j=some i ∧ SixAttachmentVertex G f i (vertex j k)
  injective : Function.Injective (fun p : Σ j, Fin (counts j).val => vertex p.1 p.2)
  cover : ∀ i∈sixAttachmentFamily t, ∀ x, SixAttachmentVertex G f i x →
    ∃ j k, vertex j k=x

/-- Enumerate the actual attachment fibers. Each label denotes one actual
vertex, different fibers are disjoint, and every classified vertex occurs. -/
theorem exists_six_spoke_labels (G : SimpleGraph V) (f : Fin 6 ↪ V) (t : Fin 14)
    (hbound : ∀ i, (sixAttachmentFiber G f i).card ≤ sixAttachmentCapacity i) :
    Nonempty (SixSpokeLabels G f t) := by
  let F (j : Fin 4) : Finset V := match sixResidueSlot t j with
    | none => ∅
    | some i => sixAttachmentFiber G f i
  have htwo : ∀ j, (F j).card<3 := by
    intro j
    cases hs : sixResidueSlot t j with
    | none => simp [F,hs]
    | some i =>
      have hh := hbound i
      have hc : sixAttachmentCapacity i≤2 := by
        unfold sixAttachmentCapacity
        split_ifs <;> omega
      simpa only [F,hs] using Nat.lt_of_le_of_lt hh (by omega)
  let counts (j : Fin 4) : Fin 3 := ⟨(F j).card,htwo j⟩
  let vertex (j : Fin 4) (k : Fin (counts j).val) : V :=
    ((F j).equivFin.symm k).val
  have htyped : ∀ j k, ∃ i, sixResidueSlot t j=some i ∧
      SixAttachmentVertex G f i (vertex j k) := by
    intro j k
    have hm := ((F j).equivFin.symm k).property
    change vertex j k∈F j at hm
    cases hs : sixResidueSlot t j with
    | none => simp [F,hs] at hm
    | some i =>
      refine ⟨i,rfl,?_⟩
      have hf : vertex j k∈sixAttachmentFiber G f i := by simpa only [F,hs] using hm
      exact (mem_filter.mp hf).2
  refine ⟨⟨counts,vertex,?_,htyped,?_,?_⟩⟩
  · intro j
    cases hs : sixResidueSlot t j with
    | none => apply Fin.ext; simp [counts,F,hs]
    | some i => simpa only [counts,F,hs,sixAttachmentCapacity] using hbound i
  · rintro ⟨j,k⟩ ⟨l,m⟩ he
    obtain ⟨a,ha,hak⟩ := htyped j k
    obtain ⟨b,hb,hbm⟩ := htyped l m
    have hab : a=b := six_attachment_vertex_type_unique (by simpa only [he] using hak) hbm
    subst b
    have hjl := six_residue_slot_injective t a j l ha hb
    subst l
    have hkm : k=m := (F j).equivFin.symm.injective (Subtype.ext he)
    subst m
    rfl
  · intro i hi x hx
    obtain ⟨j,hj⟩ := six_residue_slot_cover t i hi
    have hm : x∈F j := by
      simp only [F,hj,sixAttachmentFiber,mem_filter,mem_univ,true_and]
      exact hx
    exact ⟨j,(F j).equivFin ⟨x,hm⟩,by simp only [vertex,Equiv.symm_apply_apply]⟩

end
end Cycle12
