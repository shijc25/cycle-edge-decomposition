import Cycle12.SixResidueFiberLabeling
import Cycle12.SixResidueRealization

namespace Cycle12
open SimpleGraph Finset TerminalCert
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every independent-exterior frame with bounded actual fibers has a
bijective labeling by one of the certified finite models. -/
theorem six_independent_residue_labeling (G : SimpleGraph V) (f : Fin 6 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1))) (hf : SixIndependentFrame G f)
    (hbound : ∀ i, (sixAttachmentFiber G f i).card ≤ sixAttachmentCapacity i) :
    ∃ (t : Fin 14) (counts : Fin 4 → Fin 3) (S : Finset (Fin 9))
      (r : SixResidueDomain counts 0 ↪ V),
      SixResidueParametersValid t counts 0 ∧ Function.Surjective r ∧
      G.comap r=(graph (chordEdges (sixResidueBase t counts 0) sixResidueChord S)).comap
        (sixResidueIndex counts 0) := by
  obtain ⟨t,ht⟩ := hf
  obtain ⟨L⟩ := exists_six_spoke_labels G f t hbound
  let r₀ : SixResidueDomain L.counts 0 → V
    | .inl i => f i
    | .inr (.inl ⟨j,k⟩) => L.vertex j k
    | .inr (.inr k) => False.elim (k.property rfl)
  have hr : Function.Injective r₀ := by
    intro a b he
    rcases a with i | (⟨j,k⟩ | k)
    · rcases b with l | (⟨j,k⟩ | k)
      · exact congrArg Sum.inl (f.injective he)
      · obtain ⟨_,_,hx⟩ := L.typed j k
        exact False.elim (hx.1 i he.symm)
      · exact False.elim (k.property rfl)
    · rcases b with l | (⟨j',k'⟩ | k')
      · obtain ⟨_,_,hx⟩ := L.typed j k
        exact False.elim (hx.1 l he)
      · exact congrArg (Sum.inr ∘ Sum.inl) (L.injective he)
      · exact False.elim (k'.property rfl)
    · exact False.elim (k.property rfl)
  let r : SixResidueDomain L.counts 0 ↪ V := ⟨r₀,hr⟩
  have hsurj : Function.Surjective r := by
    intro x
    rcases ht x with ⟨i,rfl⟩ | ⟨i,hi,hx⟩
    · exact ⟨.inl i,rfl⟩
    · obtain ⟨j,k,hk⟩ := L.cover i hi x hx
      exact ⟨.inr (.inl ⟨j,k⟩),hk⟩
  let g := Function.extend (sixResidueIndex L.counts 0) r (fun _ => f 0)
  have hg : ∀ v, g (sixResidueIndex L.counts 0 v)=r v :=
    (six_residue_index_injective L.counts 0).extend_apply r (fun _ => f 0)
  obtain ⟨S,hS⟩ := six_residue_realization G t L.counts 0 r hcycle
    (fun j k => by
      obtain ⟨i,hi,hx⟩ := L.typed j k
      exact ⟨i,hi,hx.2⟩) g hg
    (by intro x y he; simp [sixResidueEar] at he)
    (by intro k; exact False.elim (k.property rfl))
  exact ⟨t,L.counts,S,r,⟨by simp,L.valid⟩,hsurj,hS⟩

end
end Cycle12
