import Cycle12.SixResidueModelFacts

namespace Cycle12
open SimpleGraph Finset

/-- Only active slots occur in this type. Inactive padding is never
included in a bijective labeling of the actual graph. -/
abbrev SixResidueDomain (counts : Fin 4 → Fin 3) (ear : Fin 5) :=
  Fin 6 ⊕ ((Σ j : Fin 4, Fin (counts j).val) ⊕ {k : Fin 2 // ear≠0})

def sixResidueIndex (counts : Fin 4 → Fin 3) (ear : Fin 5) :
    SixResidueDomain counts ear → Fin 16
  | .inl i => sixResidueCore i
  | .inr (.inl ⟨j,k⟩) => ⟨6+2*j.val+k.val,by have := k.isLt; have := (counts j).isLt; omega⟩
  | .inr (.inr k) => ⟨14+k.val.val,by have := k.val.isLt; omega⟩

theorem six_residue_index_injective (counts : Fin 4 → Fin 3) (ear : Fin 5) :
    Function.Injective (sixResidueIndex counts ear) := by
  intro a b he
  have hv := congrArg Fin.val he
  rcases a with a | (⟨j,k⟩ | a) <;> rcases b with b | (⟨l,m⟩ | b)
  · exact congrArg Sum.inl (Fin.ext hv)
  · have := m.isLt; have := (counts l).isLt
    simp only [sixResidueIndex,sixResidueCore] at hv
    omega
  · simp only [sixResidueIndex,sixResidueCore] at hv
    omega
  · have := k.isLt; have := (counts j).isLt
    simp only [sixResidueIndex,sixResidueCore] at hv
    omega
  · have hk := k.isLt; have hm := m.isLt
    have hj := (counts j).isLt; have hl := (counts l).isLt
    simp only [sixResidueIndex] at hv
    have hjl : j=l := Fin.ext (by omega)
    subst l
    have hkm : k=m := Fin.ext (by omega)
    subst m
    rfl
  · have := k.isLt; have := (counts j).isLt
    simp only [sixResidueIndex] at hv
    omega
  · simp only [sixResidueIndex,sixResidueCore] at hv
    omega
  · have := m.isLt; have := (counts l).isLt
    simp only [sixResidueIndex] at hv
    omega
  · have hab : a=b := Subtype.ext (Fin.ext (by simpa only [sixResidueIndex,Nat.add_left_cancel_iff] using hv))
    subst b
    rfl

theorem six_residue_index_mem (counts : Fin 4 → Fin 3) (ear : Fin 5)
    (v : SixResidueDomain counts ear) : sixResidueIndex counts ear v∈sixResidueActive counts ear := by
  rcases v with i | (⟨j,k⟩ | k)
  · exact six_residue_core_mem counts ear i
  · let k' : Fin 2 := ⟨k.val,by have := k.isLt; have := (counts j).isLt; omega⟩
    exact six_residue_slot_mem counts ear j k' k.isLt
  · apply mem_union.mpr ∘ Or.inr
    rw [if_neg k.property]
    have hk := k.val.isLt
    have hm : k.val.val=0 ∨ k.val.val=1 := by omega
    rcases hm with h | h <;> simp [sixResidueIndex,h]

theorem six_residue_index_surjective (counts : Fin 4 → Fin 3) (ear : Fin 5)
    (v : Fin 16) (hv : v∈sixResidueActive counts ear) :
    ∃ w, sixResidueIndex counts ear w=v := by
  rcases mem_union.mp hv with hv | hv
  · rcases mem_union.mp hv with hv | hv
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact ⟨.inl i,rfl⟩
    · obtain ⟨j,_,hj⟩ := mem_biUnion.mp hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
      exact ⟨.inr (.inl ⟨j,⟨k.val,(mem_filter.mp hk).2⟩⟩),rfl⟩
  · by_cases he : ear=0
    · simp [he] at hv
    · rw [if_neg he] at hv
      rcases mem_insert.mp hv with hv | hv
      · subst v
        exact ⟨.inr (.inr ⟨0,he⟩),rfl⟩
      · have hv' := mem_singleton.mp hv
        subst v
        exact ⟨.inr (.inr ⟨1,he⟩),rfl⟩

noncomputable def sixResidueActiveEquiv (counts : Fin 4 → Fin 3) (ear : Fin 5) :
    SixResidueDomain counts ear ≃ (sixResidueActive counts ear : Set (Fin 16)) :=
  Equiv.ofBijective (fun v => ⟨sixResidueIndex counts ear v,six_residue_index_mem counts ear v⟩)
    ⟨fun _ _ he => six_residue_index_injective counts ear (congrArg Subtype.val he),by
      intro v
      obtain ⟨w,hw⟩ := six_residue_index_surjective counts ear v.val v.property
      exact ⟨w,Subtype.ext hw⟩⟩

noncomputable section
attribute [local instance] Classical.propDecidable

theorem terminal_affine_comap_equiv {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : W ≃ V)
    (hpack : ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard) :
    ∃ P : Cycle13.CyclePacking (G.comap f),
      P.cost ≤ 19*(Fintype.card W-1)+6*(G.comap f).edgeSet.ncard := by
  apply terminal_affine_of_labeling (G.comap f) f.symm.toEmbedding f.symm.surjective
  have he : (G.comap f).comap f.symm.toEmbedding=G := by
    ext x y
    simp only [comap_adj,Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
  rwa [he]

end
end Cycle12
