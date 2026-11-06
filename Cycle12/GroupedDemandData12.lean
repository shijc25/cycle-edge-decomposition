import Cycle12.IndexedGroupClosure12
import Cycle12.BoundedDemandGroups12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I T : Type} [Fintype V] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq I] [DecidableEq T]

/-- Rotate each group independently, then identify the disjoint union
of its fibers with the original demand index set. -/
def groupedCycleNext (group : I → T) : Equiv.Perm I :=
  (Equiv.sigmaFiberEquiv group).symm.trans
    ((Equiv.sigmaCongrRight (fun t => finiteCycleNext {i : I // group i=t})).trans
      (Equiv.sigmaFiberEquiv group))

theorem groupedCycleNext_on_fiber (group : I → T) (t : T) (j : {i : I // group i=t}) :
    groupedCycleNext group j.val=(finiteCycleNext {i : I // group i=t} j).val := by
  rcases j with ⟨j,hj⟩
  subst t
  rfl

theorem groupedCycleNext_preserves_group (group : I → T) (i : I) :
    group (groupedCycleNext group i)=group i := by
  rw [groupedCycleNext_on_fiber group (group i) (⟨i,rfl⟩ : {j : I // group j=group i})]
  exact (finiteCycleNext {j : I // group j=group i} ⟨i,rfl⟩).property

def groupPorts (group : I → T) (a b : I → V) (t : T) : Finset V :=
  (univ.filter (fun i => group i=t)).image a ∪ (univ.filter (fun i => group i=t)).image b

theorem mem_groupPorts (group : I → T) (a b : I → V) (t : T) (v : V) :
    v∈groupPorts group a b t ↔ ∃ i,group i=t ∧ (a i=v ∨ b i=v) := by
  simp only [groupPorts,mem_union,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro (⟨i,hi,hv⟩ | ⟨i,hi,hv⟩)
    · exact ⟨i,hi,Or.inl hv⟩
    · exact ⟨i,hi,Or.inr hv⟩
  · rintro ⟨i,hi,hv|hv⟩
    · exact Or.inl ⟨i,hi,hv⟩
    · exact Or.inr ⟨i,hi,hv⟩

theorem groupPorts_card (group : I → T) (a b : I → V) (t : T) :
    (groupPorts group a b t).card ≤ 2*teamLoad group t := by
  have hu := card_union_le ((univ.filter (fun i => group i=t)).image a)
    ((univ.filter (fun i => group i=t)).image b)
  have ha := card_image_le (s:=univ.filter (fun i => group i=t)) (f:=a)
  have hb := card_image_le (s:=univ.filter (fun i => group i=t)) (f:=b)
  change (groupPorts group a b t).card ≤ _ at hu
  unfold teamLoad
  omega

theorem colored_group_teamLoad (color : I → T) {Q : ℕ} (hQ : 0<Q)
    (t : ColoredDemandGroups color Q) :
    teamLoad (coloredDemandGroup color Q) t ≤ Q := by
  have hh := coloredDemandGroup_fiber_card color hQ t
  simpa only [Fintype.card_subtype,teamLoad] using hh

theorem grouped_reconnection_distinct (group : I → T) (a b : I → V)
    (hne : ∀ i,a i ≠ b i)
    (hsep : ∀ i j,i ≠ j → group i=group j → b i ≠ a j) (i : I) :
    b i ≠ a (groupedCycleNext group i) := by
  by_cases hi : i=groupedCycleNext group i
  · rw [←hi]
    exact (hne i).symm
  · exact hsep i _ hi (groupedCycleNext_preserves_group group i).symm

end
end Cycle12
