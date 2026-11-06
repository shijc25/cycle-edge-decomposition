import Cycle12.Foundations.ControlledSuppression

/-! Exact output counts after adding one prescribed pair. Its external/internal
edge is the only possible change across the external boundary. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MatchingCounts
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {H : SimpleGraph I} {M P : H.Subgraph} (o : I → V)

theorem outputCount_eq_of_edges (hle : M≤P) {x y : V}
    (hretain : ∀ i j, P.Adj i j → s(o i,o j)=s(x,y) → M.Adj i j) :
    outputCount P o x y=outputCount M o x y := by
  have hm : ∀ e : P.edgeSet, Sym2.map o e.val=s(x,y) → e.val∈M.edgeSet := by
    intro e he
    have ha : P.Adj e.val.out.1 e.val.out.2 := edge_out_adj P.spanningCoe e
    have hp : s(o e.val.out.1,o e.val.out.2)=s(x,y) :=
      (congrArg (Sym2.map o) (out_pair_eq e.val)).trans he
    have h := hretain _ _ ha hp
    rw [← out_pair_eq e.val]
    exact h
  rw [outputCount,outputCount,← Fintype.card_subtype,← Fintype.card_subtype]
  apply Fintype.card_congr
  exact {
    toFun := fun e => ⟨⟨e.val.val,hm e.val e.property⟩,e.property⟩
    invFun := fun e => ⟨⟨e.val.val,Subgraph.edgeSet_mono hle e.val.property⟩,e.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem outputCount_single_pair {a b : I} (hp : P.Adj a b) (x y : V)
    (honly : ∀ i j, P.Adj i j → s(o i,o j)=s(x,y) → s(i,j)=s(a,b)) :
    outputCount P o x y=(if s(o a,o b)=s(x,y) then 1 else 0) := by
  have hedge : ∀ e : P.edgeSet, Sym2.map o e.val=s(x,y) → e.val=s(a,b) := by
    intro e he
    have ha : P.Adj e.val.out.1 e.val.out.2 := edge_out_adj P.spanningCoe e
    have h := honly _ _ ha ((congrArg (Sym2.map o) (out_pair_eq e.val)).trans he)
    exact (out_pair_eq e.val).symm.trans h
  have hle : outputCount P o x y≤1 := by
    apply card_le_one.mpr
    intro e he f hf
    exact Subtype.ext ((hedge e (mem_filter.mp he).2).trans (hedge f (mem_filter.mp hf).2).symm)
  by_cases heq : s(o a,o b)=s(x,y)
  · rw [if_pos heq]
    have hpos : 0<outputCount P o x y := by
      apply card_pos.mpr
      exact ⟨⟨s(a,b),hp⟩,mem_filter.mpr ⟨mem_univ _,heq⟩⟩
    omega
  · rw [if_neg heq]
    apply outputCount_eq_zero
    intro i j hij ho
    exact heq ((congrArg (Sym2.map o) (honly i j hij ho)).symm.trans ho)

theorem added_pair_internal (S : Set V) {a b : I} (hb : o b∉S)
    (hle : M≤P)
    (hnew : ∀ i j, P.Adj i j → M.Adj i j ∨ s(i,j)=s(a,b))
    {x y : V} (hx : x∈S) (hy : y∈S) : outputCount P o x y=outputCount M o x y := by
  apply outputCount_eq_of_edges o hle
  intro i j hij ho
  rcases hnew i j hij with hm | he
  · exact hm
  · have ht : s(o a,o b)=s(x,y) := (congrArg (Sym2.map o) he).symm.trans ho
    rcases Sym2.eq_iff.mp ht with h | h
    · exact False.elim (hb (h.2 ▸ hy))
    · exact False.elim (hb (h.2 ▸ hx))

theorem added_pair_cross (S : Set V) {a b : I} (hp : P.Adj a b)
    (hends : ∀ i j, M.Adj i j → o i∈S ∧ o j∈S)
    (hnew : ∀ i j, P.Adj i j → M.Adj i j ∨ s(i,j)=s(a,b))
    (x y : V) (hy : y∉S) :
    outputCount P o x y=(if s(o a,o b)=s(x,y) then 1 else 0) := by
  apply outputCount_single_pair o hp
  intro i j hij ho
  rcases hnew i j hij with hm | he
  · rcases Sym2.eq_iff.mp ho with h | h
    · exact False.elim (hy (h.2 ▸ (hends i j hm).2))
    · exact False.elim (hy (h.1 ▸ (hends i j hm).1))
  · exact he

end MatchingCounts
end
end Cycle13
