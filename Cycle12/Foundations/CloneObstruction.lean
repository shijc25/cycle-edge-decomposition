import Cycle12.Foundations.CloneGraph

/-! The nonempty small block in GLW's clone obstruction. The all-clone
case is handled explicitly by returning the corresponding original vertices. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem clone_obstruction_small_block {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hsize : 3*t+2*R.card ≤ Fintype.card V) (hRt : R.card < t)
    (hno : ¬ Nonempty (StrongCliqueImmersion t G))
    (hperfect : ¬ HasPerfectMatchingOn (cloneGraph G R)ᶜ Set.univ)
    (hhypo : ¬ Hypomatchable (cloneGraph G R)ᶜ) :
    ∃ W : Set V, W.Nonempty ∧ W.ncard < t ∧
      ∀ v ∈ W, Gᶜ.degree v ≤ W.ncard+R.card := by
  classical
  obtain ⟨W',L',hWnon,hWsmall,hd,hLsize,hmiss,hcross⟩ :=
    exists_DY_small_block_of_partition_bound (cloneGraph G R) (t+R.card)
      (CloneGraph.partition_bound G R ht hno) hperfect hhypo
  have hWloss := CloneGraph.old_part_bound R W'
  have hLloss := CloneGraph.old_part_bound R L'
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_coe] at hLsize
  have hL : t ≤ (Sum.inl ⁻¹' L').ncard := by omega
  by_cases hOld : (Sum.inl ⁻¹' W').Nonempty
  · have hW : (Sum.inl ⁻¹' W').ncard < t := by
      by_contra! hWt
      apply hno
      apply strong_model_of_complete_bipartite G (Sum.inl ⁻¹' W') (Sum.inl ⁻¹' L') t
      · exact Set.disjoint_left.mpr (fun _ hW hL => Set.disjoint_left.mp hd hW hL)
      · exact hWt
      · exact hL
      · intro v hv w hw
        exact hcross (Sum.inl v) hv (Sum.inl w) hw
    refine ⟨Sum.inl ⁻¹' W',hOld,hW,?_⟩
    intro v hv
    have h₁ := CloneGraph.old_missing_le G R v
    have h₂ := hmiss (Sum.inl v) hv
    simp only [← ncard_neighborSet] at h₁ h₂ ⊢
    omega
  · let T : Set R := Sum.inr ⁻¹' W'
    let W : Set V := Subtype.val '' T
    have hOldE : Sum.inl ⁻¹' W'=∅ := Set.not_nonempty_iff_eq_empty.mp hOld
    have hWT : W.ncard=T.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
    have hW' : W.ncard=W'.ncard := by
      have heq := CloneGraph.sum_set_card R W'
      rw [hOldE,Set.ncard_empty,zero_add] at heq
      exact hWT.trans heq.symm
    have hWcard : W.ncard ≤ R.card := by
      have hT := Set.ncard_le_card T
      rw [Nat.card_eq_fintype_card,Fintype.card_coe] at hT
      omega
    have hWnon' : W.Nonempty := by
      obtain ⟨v,hv⟩ := hWnon
      rcases v with v | v
      · exact False.elim (hOld ⟨v,hv⟩)
      · exact ⟨v.val,v,hv,rfl⟩
    refine ⟨W,hWnon',hWcard.trans_lt hRt,?_⟩
    rintro v ⟨w,hw,rfl⟩
    have h₁ := CloneGraph.clone_missing_le G R w
    have h₂ := hmiss (Sum.inr w) hw
    simp only [← ncard_neighborSet] at h₁ h₂ ⊢
    omega

end
end Cycle13
