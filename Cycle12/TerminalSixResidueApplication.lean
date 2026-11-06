import Cycle12.TerminalSixResidueModels
import Cycle12.SixMatchingResidueLabeling

namespace Cycle12
open SimpleGraph Finset TerminalCert
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Apply the fully checked finite catalogue through an actual bijection.
The cycle restriction and exact order are transported together. -/
theorem terminal_affine_of_six_residue (G : SimpleGraph V)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (t : Fin 14) (counts : Fin 4 → Fin 3) (ear : Fin 5) (S : Finset (Fin 9))
    (hvalid : SixResidueParametersValid t counts ear)
    (r : SixResidueDomain counts ear ↪ V) (hsurj : Function.Surjective r)
    (hmodel : G.comap r=(graph (chordEdges (sixResidueBase t counts ear) sixResidueChord S)).comap
      (sixResidueIndex counts ear)) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let H := (graph (chordEdges (sixResidueBase t counts ear) sixResidueChord S)).induce
    (sixResidueActive counts ear : Set (Fin 16))
  let e := sixResidueActiveEquiv counts ear
  have he : H.comap e=G.comap r := hmodel.symm
  let j : ↥(sixResidueActive counts ear : Set (Fin 16)) → V := fun v => r (e.symm v)
  have hj : Function.Injective j := r.injective.comp e.symm.injective
  have hjadj : ∀ u v, H.Adj u v → G.Adj (j u) (j v) := by
    intro u v huv
    have hh : (H.comap e).Adj (e.symm u) (e.symm v) := by
      simpa only [comap_adj,Equiv.apply_symm_apply] using huv
    rw [he] at hh
    exact hh
  have hH : Cycle13.NoCycleAtLeast H 7 :=
    noLongCycle_of_injective_hom hshort ⟨j,fun {_ _} h => hjadj _ _ h⟩ hj
  have hpack := terminal_six_residue_model t counts ear hvalid S hH
  have hpack' := terminal_affine_comap_equiv H e hpack
  rw [he] at hpack'
  exact terminal_affine_of_labeling G r hsurj hpack'

theorem terminal_affine_six_independent (G : SimpleGraph V)
    (hshort : Cycle13.NoCycleAtLeast G 7) (f : Fin 6 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1))) (hf : SixIndependentFrame G f)
    (hbound : ∀ i, (sixAttachmentFiber G f i).card ≤ sixAttachmentCapacity i) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  obtain ⟨t,counts,S,r,hvalid,hsurj,hmodel⟩ :=
    six_independent_residue_labeling G f hcycle hf hbound
  exact terminal_affine_of_six_residue G hshort t counts 0 S hvalid r hsurj hmodel

theorem terminal_affine_six_matching (G : SimpleGraph V)
    (ih : TerminalProperInduction G) (hshort : Cycle13.NoCycleAtLeast G 7)
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hf : SixMatchingFrame G f) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  by_contra hbad
  have hbound := six_attachment_fiber_bound G ih hbad f
  obtain ⟨t,ht⟩ := hf
  by_cases he : ∃ x y, SixEdgeComponent G f x y
  · obtain ⟨x,y,hxy⟩ := he
    have cover : ∀ z, (∃ i, f i=z) ∨
        (∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i z) ∨ z=x ∨ z=y := by
      intro z
      rcases ht z with h | h | ⟨w,hzw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (six_edge_components_cover_pair G ih hbad f hxy hzw))
    have finish : ∀ {a b : V}, SixEdgeComponent G f a b → G.Adj a (f 0) → G.Adj b (f 3) →
        (∀ z, (∃ i, f i=z) ∨
          (∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i z) ∨ z=a ∨ z=b) → False := by
      intro a b hab ha hb hc
      obtain ⟨counts,ear,S,r,hvalid,hsurj,hmodel⟩ :=
        six_oriented_pair_residue_labeling G f hcycle t hab ha hb hc hbound
      exact hbad (terminal_affine_of_six_residue G hshort _ counts ear S hvalid r hsurj hmodel)
    rcases hxy.2.2.2.1 with ⟨hx0,hy3⟩ | ⟨hx3,hy0⟩
    · exact finish hxy hx0 hy3 cover
    · apply finish (six_edge_component_symm hxy) hy0 hx3
      intro z
      exact (cover z).imp_right (Or.imp_right Or.symm)
  · apply hbad
    apply terminal_affine_six_independent G hshort f hcycle _ hbound
    refine ⟨Fin.castLE (by decide) t,?_⟩
    intro z
    rcases ht z with h | h | ⟨w,hzw⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (he ⟨z,w,hzw⟩)

end
end Cycle12
