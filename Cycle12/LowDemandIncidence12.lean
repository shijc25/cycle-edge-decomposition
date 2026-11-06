import Cycle12.MixedEndpointIncidence12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Cyclic reconnection merely permutes the original endpoint occurrences. -/
def reconnectionPorts (next : Equiv.Perm I) : Equiv.Perm (I × Bool) where
  toFun k := if k.2 then (next k.1,false) else (k.1,true)
  invFun k := if k.2 then (k.1,false) else (next.symm k.1,true)
  left_inv := by rintro ⟨i,b⟩; cases b <;> simp
  right_inv := by rintro ⟨i,b⟩; cases b <;> simp

/-- The requests that cyclically close all low-path groups retain the
single original-incidence injection for the whole family. -/
theorem low_demands_original_incidences (F : SimpleGraph V) (a b z : I → V)
    (ha : ∀ i,F.Adj (z i) (a i)) (hb : ∀ i,F.Adj (z i) (b i))
    (hne : ∀ i,a i ≠ b i)
    (hd : Pairwise (fun i j => Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet
      (twoEdgeWalk (ha j) (hb j)).edgeSet)) (next : Equiv.Perm I) :
    ∃ neighbor : I × Bool → V,
      (∀ k,F.Adj (if k.2 then a (next k.1) else b k.1) (neighbor k) ∧
        s((if k.2 then a (next k.1) else b k.1),neighbor k)∈
          ⋃ i,(twoEdgeWalk (ha i) (hb i)).edgeSet) ∧
      Function.Injective (fun k : I × Bool =>
        ((if k.2 then a (next k.1) else b k.1),neighbor k)) := by
  let neighbor := fun k : I × Bool => z (reconnectionPorts next k).1
  refine ⟨neighbor,?_,?_⟩
  · rintro ⟨i,d⟩
    cases d
    · refine ⟨(hb i).symm,Set.mem_iUnion.mpr ⟨i,?_⟩⟩
      simp only [neighbor,reconnectionPorts,Bool.false_eq_true,ite_false,Equiv.coe_fn_mk,
        twoEdgeWalk_edges]
      simp [Sym2.eq_swap]
    · refine ⟨(ha (next i)).symm,Set.mem_iUnion.mpr ⟨next i,?_⟩⟩
      simp only [neighbor,reconnectionPorts,ite_true,Equiv.coe_fn_mk,twoEdgeWalk_edges]
      simp [Sym2.eq_swap]
  · have hi := (twoEdge_incidence_injective a b z ha hb hne hd).comp (reconnectionPorts next).injective
    intro k l hkl
    apply hi
    have he (j : I × Bool) :
        (if (reconnectionPorts next j).2 then b (reconnectionPorts next j).1
          else a (reconnectionPorts next j).1)=(if j.2 then a (next j.1) else b j.1) := by
      rcases j with ⟨j,d⟩
      cases d <;> rfl
    simpa only [Function.comp_apply,he,neighbor] using hkl

end
end Cycle12
