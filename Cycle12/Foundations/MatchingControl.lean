import Cycle12.Foundations.RoutedMultiplicity

/-! Extending a matching leaves every already covered port unchanged.
The output multiplicities retain edge indices, including parallel outputs. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem matching_extension_adj {I : Type} {H : SimpleGraph I}
    {M N : H.Subgraph} (hM : M.IsMatching) (hN : N.IsMatching) (hle : M≤N)
    {x y : I} (hx : x∈M.verts) : N.Adj x y ↔ M.Adj x y := by
  constructor
  · intro hxy
    obtain ⟨w,hw,_⟩ := hM hx
    have he : y=w := hN.eq_of_adj_left hxy (hle.2 hw)
    exact he ▸ hw
  · intro h; exact hle.2 h

namespace MatchingCounts
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {H : SimpleGraph I} (M : H.Subgraph) (o : I → V)

def outputCount (x y : V) : ℕ :=
  (univ.filter (fun e : M.edgeSet => Sym2.map o e.val=s(x,y))).card

theorem outputCount_le_one (hi : Set.InjOn (Sym2.map o) M.edgeSet) (x y : V) :
    outputCount M o x y≤1 := by
  apply card_le_one.mpr
  intro e he f hf
  exact Subtype.ext (hi e.property f.property ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm))

theorem outputCount_eq_zero {x y : V} (h : ∀ a b, M.Adj a b → s(o a,o b)≠s(x,y)) :
    outputCount M o x y=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hp := (mem_filter.mp he).2
  have ha : M.Adj e.val.out.1 e.val.out.2 := edge_out_adj M.spanningCoe e
  apply h _ _ ha
  exact (congrArg (Sym2.map o) (out_pair_eq e.val)).trans hp

theorem edge_mem_of_covered_output {N : H.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (hle : M≤N)
    {x y : V} (hc : ∀ a, o a=x → a∈M.verts)
    {e : Sym2 I} (he : e∈N.edgeSet) (ho : Sym2.map o e=s(x,y)) : e∈M.edgeSet := by
  induction e using Sym2.ind with
  | h a b =>
    change N.Adj a b at he
    change s(o a,o b)=s(x,y) at ho
    change M.Adj a b
    rcases Sym2.eq_iff.mp ho with h | h
    · exact (matching_extension_adj hM hN hle (hc a h.1)).mp he
    · exact ((matching_extension_adj hM hN hle (hc b h.2)).mp he.symm).symm

theorem outputCount_extension {N : H.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (hle : M≤N)
    {x y : V} (hc : ∀ a, o a=x → a∈M.verts) :
    outputCount N o x y=outputCount M o x y := by
  rw [outputCount,outputCount,← Fintype.card_subtype,← Fintype.card_subtype]
  apply Fintype.card_congr
  exact {
    toFun := fun e => ⟨⟨e.val.val,edge_mem_of_covered_output M o hM hN hle hc
      e.val.property e.property⟩,e.property⟩
    invFun := fun e => ⟨⟨e.val.val,Subgraph.edgeSet_mono hle e.val.property⟩,e.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end MatchingCounts

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)
    {H : SimpleGraph (R.Ports z)}

theorem multiplicity_paired (M : H.Subgraph) (hM : M.IsMatching)
    (x y : {v : V // v≠z}) :
    (R.pairedRoutes z M hM).multiplicity x y=
      MatchingCounts.outputCount M (R.portTip z) x y := by
  unfold multiplicity MatchingCounts.outputCount
  congr 1
  ext e
  simp only [mem_filter,mem_univ,true_and]
  change s(R.portTip z e.val.out.1,R.portTip z e.val.out.2)=s(x,y) ↔ _
  rw [← Sym2.map_mk, out_pair_eq]

theorem suppress_extension_multiplicity {M N : H.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (hle : M≤N)
    (x y : {v : V // v≠z}) (hc : ∀ a, R.portTip z a=x → a∈M.verts) :
    (R.suppress z N hN).multiplicity x y=
      R.multiplicity x.val y.val+MatchingCounts.outputCount M (R.portTip z) x y := by
  rw [multiplicity_suppress,multiplicity_paired,
    MatchingCounts.outputCount_extension M (R.portTip z) hM hN hle hc]

end RoutedEdges
end
end Cycle13
