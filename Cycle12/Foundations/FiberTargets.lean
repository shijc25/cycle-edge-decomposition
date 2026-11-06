import Cycle12.Foundations.FiberBinaryLabels

/-! Simultaneous injections into disjoint color classes, with protected
vertices excluded. The final assignment is injective across all classes. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I V C : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V] [DecidableEq C]

theorem exists_fiber_targets (g : I → C) (color : V → C) (allowed : V → Prop)
    (hroom : ∀ r, (univ.filter (fun i => g i=r)).card ≤
      (univ.filter (fun v => color v=r ∧ allowed v)).card) :
    ∃ target : I ↪ V, ∀ i, color (target i)=g i ∧ allowed (target i) := by
  have he : ∀ r, Nonempty ({i // g i=r} ↪ {v // color v=r ∧ allowed v}) := by
    intro r
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_subtype] using hroom r
  let e (r : C) := Classical.choice (he r)
  let target (i : I) : V := (e (g i) ⟨i,rfl⟩).val
  have ht : ∀ i, color (target i)=g i ∧ allowed (target i) :=
    fun i => (e (g i) ⟨i,rfl⟩).property
  have htransport : ∀ (r s : C) (h : r=s) (i j : I) (hi : g i=r) (hj : g j=s),
      (e r ⟨i,hi⟩).val=(e s ⟨j,hj⟩).val → i=j := by
    intro r s h i j hi hj hc
    subst s
    exact congrArg Subtype.val ((e r).injective (Subtype.ext hc))
  have hinj : Function.Injective target := by
    intro i j h
    have hg : g i=g j := (ht i).1.symm.trans ((congrArg color h).trans (ht j).1)
    exact htransport _ _ hg i j rfl rfl h
  exact ⟨⟨target,hinj⟩,ht⟩

end
end Cycle13
