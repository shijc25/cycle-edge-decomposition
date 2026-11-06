import Cycle12.SixIndependentResidueLabeling
import Cycle12.SixResidueEarEncoding

namespace Cycle12
open SimpleGraph Finset TerminalCert
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem six_oriented_pair_residue_labeling (G : SimpleGraph V) (f : Fin 6 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1))) (t : Fin 4) {x y : V}
    (hxy : SixEdgeComponent G f x y) (hx0 : G.Adj x (f 0)) (hy3 : G.Adj y (f 3))
    (hcover : ∀ z, (∃ i, f i=z) ∨
      (∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i z) ∨ z=x ∨ z=y)
    (hbound : ∀ i, (sixAttachmentFiber G f i).card ≤ sixAttachmentCapacity i) :
    ∃ (counts : Fin 4 → Fin 3) (ear : Fin 5) (S : Finset (Fin 9))
      (r : SixResidueDomain counts ear ↪ V),
      SixResidueParametersValid (Fin.castLE (by decide) t) counts ear ∧ Function.Surjective r ∧
      G.comap r=(graph (chordEdges (sixResidueBase (Fin.castLE (by decide) t) counts ear)
        sixResidueChord S)).comap (sixResidueIndex counts ear) := by
  let t' : Fin 14 := Fin.castLE (by decide) t
  obtain ⟨L⟩ := exists_six_spoke_labels G f t' hbound
  let a : Bool := decide (G.Adj x (f 3))
  let b : Bool := decide (G.Adj y (f 0))
  let ear := sixResidueEarChoice a b
  have hearn : ear≠0 := six_residue_ear_choice_nonzero a b
  let pair : Fin 2 ↪ V := ⟨![x,y],by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp [hxy.2.2.1.ne,Ne.symm hxy.2.2.1.ne] at he ⊢⟩
  have hpairOut : ∀ k i, pair k≠f i := by
    intro k i
    fin_cases k
    · exact hxy.1 i
    · exact hxy.2.1 i
  have hspokePair : ∀ j k l, L.vertex j k≠pair l := by
    intro j k l he
    obtain ⟨_,_,hv⟩ := L.typed j k
    fin_cases l
    · exact six_attachment_vertex_no_external_neighbors hv hxy.2.1 (by
        change L.vertex j k=x at he
        rw [he]
        exact hxy.2.2.1)
    · exact six_attachment_vertex_no_external_neighbors hv hxy.1 (by
        change L.vertex j k=y at he
        rw [he]
        exact hxy.2.2.1.symm)
  let r₀ : SixResidueDomain L.counts ear → V
    | .inl i => f i
    | .inr (.inl ⟨j,k⟩) => L.vertex j k
    | .inr (.inr k) => pair k.val
  have hr : Function.Injective r₀ := by
    intro u v he
    rcases u with i | (⟨j,k⟩ | k)
    · rcases v with l | (⟨j,k⟩ | k)
      · exact congrArg Sum.inl (f.injective he)
      · obtain ⟨_,_,hx⟩ := L.typed j k
        exact False.elim (hx.1 i he.symm)
      · exact False.elim (hpairOut k.val i he.symm)
    · rcases v with l | (⟨j',k'⟩ | k')
      · obtain ⟨_,_,hx⟩ := L.typed j k
        exact False.elim (hx.1 l he)
      · exact congrArg (Sum.inr ∘ Sum.inl) (L.injective he)
      · exact False.elim (hspokePair j k k'.val he)
    · rcases v with l | (⟨j',k'⟩ | k')
      · exact False.elim (hpairOut k.val l he)
      · exact False.elim (hspokePair j' k' k.val he.symm)
      · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (pair.injective he))
  let r : SixResidueDomain L.counts ear ↪ V := ⟨r₀,hr⟩
  have hsurj : Function.Surjective r := by
    intro z
    rcases hcover z with ⟨i,rfl⟩ | ⟨i,hi,hz⟩ | rfl | rfl
    · exact ⟨.inl i,rfl⟩
    · obtain ⟨j,k,hk⟩ := L.cover i hi z hz
      exact ⟨.inr (.inl ⟨j,k⟩),hk⟩
    · exact ⟨.inr (.inr ⟨0,hearn⟩),rfl⟩
    · exact ⟨.inr (.inr ⟨1,hearn⟩),rfl⟩
  let g := Function.extend (sixResidueIndex L.counts ear) r (fun _ => f 0)
  have hg : ∀ v, g (sixResidueIndex L.counts ear v)=r v :=
    (six_residue_index_injective L.counts ear).extend_apply r (fun _ => f 0)
  have hg0 : g 0=f 0 := hg (.inl 0)
  have hg3 : g 3=f 3 := hg (.inl 3)
  have hg14 : g 14=x := hg (.inr (.inr ⟨0,hearn⟩))
  have hg15 : g 15=y := hg (.inr (.inr ⟨1,hearn⟩))
  have hear : ∀ u v, s(u,v)∈sixResidueEar ear → G.Adj (g u) (g v) := by
    intro u v he
    rw [six_residue_ear_choice_edges] at he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · simp only [mem_insert,mem_singleton] at he
        rcases he with he | he | he
        · exact adj_of_sym2_eq g (by simpa only [hg0,hg14] using hx0.symm) he.symm
        · exact adj_of_sym2_eq g (by simpa only [hg14,hg15] using hxy.2.2.1) he.symm
        · exact adj_of_sym2_eq g (by simpa only [hg3,hg15] using hy3.symm) he.symm
      · by_cases ha : a=true
        · simp only [ha,ite_true,mem_singleton] at he
          have hxa : G.Adj x (f 3) := of_decide_eq_true ha
          exact adj_of_sym2_eq g (by simpa only [hg3,hg14] using hxa.symm) he.symm
        · simp [ha] at he
    · by_cases hb : b=true
      · simp only [hb,ite_true,mem_singleton] at he
        have hyb : G.Adj y (f 0) := of_decide_eq_true hb
        exact adj_of_sym2_eq g (by simpa only [hg0,hg15] using hyb.symm) he.symm
      · simp [hb] at he
  have hm := six_residue_ear_choice_members a b
  have hfullEar : ∀ k : {k : Fin 2 // ear≠0}, ∀ v,
      G.Adj (r (.inr (.inr k))) (r v) →
        s(sixResidueIndex L.counts ear (.inr (.inr k)),sixResidueIndex L.counts ear v)∈sixResidueEar ear := by
    rintro ⟨k,hk⟩ v hv
    fin_cases k
    · change G.Adj x (r v) at hv
      rcases (hxy.2.2.2.2.1 (r v)).mp hv with he | ⟨he,ha⟩ | ⟨he,ha⟩
      · have hv' : v=.inr (.inr ⟨1,hearn⟩) := r.injective he
        subst v
        exact hm.1
      · have hv' : v=.inl 0 := r.injective he
        subst v
        exact hm.2.1
      · have hv' : v=.inl 3 := r.injective he
        subst v
        exact hm.2.2.2.1 (by simpa only [a,decide_eq_true_eq] using ha)
    · change G.Adj y (r v) at hv
      rcases (hxy.2.2.2.2.2 (r v)).mp hv with he | ⟨he,hb⟩ | ⟨he,hb⟩
      · have hv' : v=.inr (.inr ⟨0,hearn⟩) := r.injective he
        subst v
        change s(15,14)∈sixResidueEar ear
        simpa only [Sym2.eq_swap] using hm.1
      · have hv' : v=.inl 0 := r.injective he
        subst v
        exact hm.2.2.2.2 (by simpa only [b,decide_eq_true_eq] using hb)
      · have hv' : v=.inl 3 := r.injective he
        subst v
        exact hm.2.2.1
  obtain ⟨S,hS⟩ := six_residue_realization G t' L.counts ear r hcycle
    (fun j k => by
      obtain ⟨i,hi,hx⟩ := L.typed j k
      exact ⟨i,hi,hx.2⟩) g hg hear hfullEar
  exact ⟨L.counts,ear,S,r,⟨by intro _; exact t.isLt,L.valid⟩,hsurj,hS⟩

end
end Cycle12
