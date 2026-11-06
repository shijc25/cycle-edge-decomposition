import Cycle12.ContractedCycleSwitch12
import Cycle12.ParityReserveSlots12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I L : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Classify original edges by the unordered pair of endpoint labels.
Equal labels are permitted here; the original graph remains simple. -/
def edgeLabelGraph (G : SimpleGraph V) (label : V → L) (e : Sym2 L) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ s(label x,label y)=e
  symm := ⟨by intro x y h; exact ⟨h.1.symm,(Sym2.eq_swap).trans h.2⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

theorem edgeLabelGraph_mem (G : SimpleGraph V) (label : V → L) (e : Sym2 L) (f : Sym2 V) :
    f∈(edgeLabelGraph G label e).edgeSet ↔ f∈G.edgeSet ∧ Sym2.map label f=e := by
  induction f using Sym2.inductionOn with
  | _ x y => rfl

theorem edgeLabelGraph_partition (G : SimpleGraph V) (label : V → L) :
    Pairwise (fun e f => Disjoint (edgeLabelGraph G label e).edgeSet (edgeLabelGraph G label f).edgeSet) ∧
      (⋃ e,(edgeLabelGraph G label e).edgeSet)=G.edgeSet := by
  constructor
  · intro e f hef
    apply Set.disjoint_left.mpr
    intro d he hf
    exact hef (((edgeLabelGraph_mem G label e d).mp he).2.symm.trans
      ((edgeLabelGraph_mem G label f d).mp hf).2)
  · ext e
    simp only [Set.mem_iUnion,edgeLabelGraph_mem]
    exact ⟨fun ⟨_,he,_⟩ => he,fun he => ⟨Sym2.map label e,he,rfl⟩⟩

def blockLabel (A : I → Finset V) (v : V) : Option I :=
  Sum.elim some (fun _ => none) (contractVertex A v)

theorem blockLabel_eq_some (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (v : V) (i : I) :
    blockLabel A v=some i ↔ v∈A i := by
  unfold blockLabel
  have he : Sum.elim some (fun _ => none) (contractVertex A v)=some i ↔
      contractVertex A v=Sum.inl i := by
    cases contractVertex A v <;> simp
  rw [he,contractVertex_eq_inl_iff A hd]

theorem blockLabel_eq_none (A : I → Finset V) (v : V) :
    blockLabel A v=none ↔ v∉blockUnion A := by
  unfold blockLabel contractVertex
  split_ifs with h
  · have hv : v∈blockUnion A := (mem_blockUnion A v).mpr h
    simp only [Sum.elim_inl,Option.some_ne_none,false_iff,not_not]
    exact hv
  · have hv : v∉blockUnion A := fun hv => h ((mem_blockUnion A v).mp hv)
    simp [hv]

theorem block_internal_graph (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (i : I) :
    edgeLabelGraph G (blockLabel A) s(some i,some i)=insideGraph G (A i) := by
  ext x y
  change (G.Adj x y ∧ s(blockLabel A x,blockLabel A y)=s(some i,some i)) ↔ _
  simp only [Sym2.eq_iff,and_self,or_self,blockLabel_eq_some A hd]
  rfl

theorem block_cross_graph (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (i j : I) (x y : V) :
    (edgeLabelGraph G (blockLabel A) s(some i,some j)).Adj x y ↔
      G.Adj x y ∧ ((x∈A i ∧ y∈A j) ∨ (x∈A j ∧ y∈A i)) := by
  change (G.Adj x y ∧ s(blockLabel A x,blockLabel A y)=s(some i,some j)) ↔ _
  simp only [Sym2.eq_iff,blockLabel_eq_some A hd]

theorem block_outside_graph (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (i : I) (x y : V) :
    (edgeLabelGraph G (blockLabel A) s(some i,none)).Adj x y ↔
      G.Adj x y ∧ ((x∈A i ∧ y∉blockUnion A) ∨ (x∉blockUnion A ∧ y∈A i)) := by
  change (G.Adj x y ∧ s(blockLabel A x,blockLabel A y)=s(some i,none)) ↔ _
  simp only [Sym2.eq_iff,blockLabel_eq_some A hd,blockLabel_eq_none]

theorem block_uncontracted_graph (G : SimpleGraph V) (A : I → Finset V) :
    edgeLabelGraph G (blockLabel A) s(none,none)=insideGraph G (blockUnion A)ᶜ := by
  ext x y
  change (G.Adj x y ∧ s(blockLabel A x,blockLabel A y)=s(none,none)) ↔ _
  simp only [Sym2.eq_iff,and_self,or_self,blockLabel_eq_none]
  change (G.Adj x y ∧ x∉blockUnion A ∧ y∉blockUnion A) ↔
    G.Adj x y ∧ x∈(blockUnion A)ᶜ ∧ y∈(blockUnion A)ᶜ
  simp only [mem_compl]

end
end Cycle12
