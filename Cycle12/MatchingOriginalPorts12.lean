import Cycle12.OriginalMatchingGroups12
import Cycle12.MixedEndpointIncidence12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- In an actual degree-one residue, one vertex cannot occur on two
different retained original edges. -/
theorem degree_one_incident_edge_unique (H : SimpleGraph V)
    (hd : ∀ v,H.degree v ≤ 1) {e f : Sym2 V} (he : e∈H.edgeSet) (hf : f∈H.edgeSet)
    {v : V} (hv : v∈e) (hw : v∈f) : e=f := by
  have hn (v : V) : Set.Subsingleton (H.neighborSet v) := by
    apply Set.ncard_le_one_iff_subsingleton.mp
    simpa only [ncard_neighborSet] using hd v
  induction e using Sym2.inductionOn with
  | _ x y =>
    induction f using Sym2.inductionOn with
    | _ z t =>
      rcases Sym2.mem_iff.mp hv with rfl|rfl <;> rcases Sym2.mem_iff.mp hw with h|h
      · subst z
        have hh := hn v he hf
        dsimp only at hh
        rw [hh]
      · subst t
        have hh := hn v he hf.symm
        dsimp only at hh
        rw [hh]
        exact Sym2.eq_swap
      · subst z
        have hh := hn v he.symm hf
        dsimp only at hh
        rw [hh]
        exact Sym2.eq_swap
      · subst t
        have hh := hn v he.symm hf.symm
        dsimp only at hh
        rw [hh]

/-- Orient every original edge from U to T. Both endpoint maps are
injective because the actual residue has degree at most one. -/
theorem orient_matching_original_edges (H : SimpleGraph V) (U T : Finset V)
    (hcross : ∀ {x y},H.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U))
    (hd : ∀ v,H.degree v ≤ 1) :
    ∃ a b : H.edgeSet → V,
      (∀ e,a e∈U ∧ b e∈T ∧ H.Adj (a e) (b e) ∧ s(a e,b e)=e.val) ∧
      Function.Injective a ∧ Function.Injective b := by
  have hex (e : H.edgeSet) : ∃ x y,x∈U ∧ y∈T ∧ H.Adj x y ∧ s(x,y)=e.val := by
    have ha := edge_out_adj H e
    rcases hcross ha with h|h
    · exact ⟨_,_,h.1,h.2,ha,e.val.out_eq⟩
    · exact ⟨_,_,h.2,h.1,ha.symm,Sym2.eq_swap.trans e.val.out_eq⟩
  choose a b hp using hex
  refine ⟨a,b,hp,?_,?_⟩
  · intro e f hef
    apply Subtype.ext
    apply degree_one_incident_edge_unique H hd e.property f.property (v:=a e)
    · rw [←(hp e).2.2.2]; simp
    · rw [hef,←(hp f).2.2.2]; simp
  · intro e f hef
    apply Subtype.ext
    apply degree_one_incident_edge_unique H hd e.property f.property (v:=b e)
    · rw [←(hp e).2.2.2]; simp
    · rw [hef,←(hp f).2.2.2]; simp

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The two members of every pairing of original edge indices are
globally distinct occurrences, not just distinct inside one pair. -/
def pairedOriginalItem (M : (⊤ : SimpleGraph I).Subgraph) (k : M.edgeSet × Bool) : I :=
  if k.2 then k.1.val.out.2 else k.1.val.out.1

theorem pairedOriginalItem_injective (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching) :
    Function.Injective (pairedOriginalItem M) := by
  rintro ⟨e,c⟩ ⟨f,d⟩ he
  have hef : e=f := by
    by_contra hn
    have hm : pairedOriginalItem M (e,c)∈matchingPairVertices M e := by
      cases c <;> simp [pairedOriginalItem,matchingPairVertices]
    have hm' : pairedOriginalItem M (f,d)∈matchingPairVertices M f := by
      cases d <;> simp [pairedOriginalItem,matchingPairVertices]
    exact Finset.disjoint_left.mp (matchingPairVertices_disjoint M hM hn) hm (he.symm ▸ hm')
  subst f
  have hn := (edge_out_adj M.spanningCoe e).ne
  have hcd : c=d := by
    cases c <;> cases d <;> simp_all [pairedOriginalItem,eq_comm]
  rw [hcd]

/-- Passing from paired original edges to their U-side endpoints keeps
all ports distinct; the same statement applies independently on the T side. -/
theorem matching_pair_ports_disjoint (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (a : I → V) (ha : Function.Injective a) :
    Pairwise (fun e f : M.edgeSet => Disjoint ({a e.val.out.1,a e.val.out.2}:Finset V)
      {a f.val.out.1,a f.val.out.2}) := by
  intro e f hef
  apply Finset.disjoint_left.mpr
  intro v hv hw
  rcases mem_insert.mp hv with hv|hv <;> rcases mem_insert.mp hw with hw|hw
  · exact Finset.disjoint_left.mp (matchingPairVertices_disjoint M hM hef)
      (show e.val.out.1∈matchingPairVertices M e by simp [matchingPairVertices])
      (by have hh := ha (hv.symm.trans hw); simp [matchingPairVertices,hh])
  · have hw' := mem_singleton.mp hw
    exact Finset.disjoint_left.mp (matchingPairVertices_disjoint M hM hef)
      (show e.val.out.1∈matchingPairVertices M e by simp [matchingPairVertices])
      (by have hh := ha (hv.symm.trans hw'); simp [matchingPairVertices,hh])
  · have hv' := mem_singleton.mp hv
    exact Finset.disjoint_left.mp (matchingPairVertices_disjoint M hM hef)
      (show e.val.out.2∈matchingPairVertices M e by simp [matchingPairVertices])
      (by have hh := ha (hv'.symm.trans hw); simp [matchingPairVertices,hh])
  · have hv' := mem_singleton.mp hv
    have hw' := mem_singleton.mp hw
    exact Finset.disjoint_left.mp (matchingPairVertices_disjoint M hM hef)
      (show e.val.out.2∈matchingPairVertices M e by simp [matchingPairVertices])
      (by have hh := ha (hv'.symm.trans hw'); simp [matchingPairVertices,hh])

end
end Cycle12
