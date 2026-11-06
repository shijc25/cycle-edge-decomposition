import Cycle12.Foundations.DemandRelabel

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype I] [DecidableEq I] [DecidableEq V]

abbrev factorLeft (a : I → V) (F : Finset I) : F → V := fun i => a i.val
abbrev remainderLeft (a : I → V) (F : Finset I) : {i // i∉F} → V := fun i => a i.val

theorem remainder_degree_add_factor (a b : I → V) (F : Finset I) (v : V) :
    Suppression.incidenceDegree (remainderLeft a F) (remainderLeft b F) v+
      indexedDegreeOn a b F v=Suppression.incidenceDegree a b v := by
  let weight : I → ℕ := fun i => (if a i=v then 1 else 0)+(if b i=v then 1 else 0)
  change (∑ i : {i // i∉F}, weight i.val)+(∑ i∈F, weight i)=∑ i, weight i
  rw [← sum_subtype (univ\F) (p:=fun i => i∉F) (fun i => by simp) weight]
  exact sum_sdiff (subset_univ F)

def combineFactorRouting {G : SimpleGraph V} (a b : I → V) (F : Finset I)
    (R : DemandRouting G (factorLeft a F) (factorLeft b F))
    (S : DemandRouting G (remainderLeft a F) (remainderLeft b F))
    (hcross : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) : DemandRouting G a b :=
  (R.sum S hcross).relabel (Equiv.sumCompl (fun i => i∈F))
    (by intro j; cases j <;> exact Or.inl ⟨rfl,rfl⟩)

end
end Cycle13
