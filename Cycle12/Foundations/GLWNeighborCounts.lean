import Cycle12.Foundations.GLWHypoStep

/-! Count actual external neighbors and double neighbors in a routed state,
and select a neighbor that has never been incident to a double edge. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ} {hj : j+1≤p}
    (A : GLWState G rho (j+1) hj)

def neighborExternal (x : A.neighbors) : X := x.property.1.choose

theorem neighborExternal_spec (x : A.neighbors) :
    Sum.inl (A.neighborExternal x)=x.val.val := x.property.1.choose_spec

theorem neighborExternal_injective : Function.Injective A.neighborExternal := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact (A.neighborExternal_spec a).symm.trans ((congrArg Sum.inl h).trans (A.neighborExternal_spec b))

def neighborFinset : Finset X := univ.filter (fun x =>
  0<A.routes.multiplicity (Sum.inl x) (Sum.inr (Fin.last j)))

def neighborEquiv : A.neighbors ≃ A.neighborFinset := Equiv.ofBijective
    (fun x => ⟨A.neighborExternal x,by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [A.routes.multiplicity_symm,A.neighborExternal_spec x]
      exact x.property.2⟩) (by
  constructor
  · intro a b h
    exact A.neighborExternal_injective (congrArg Subtype.val h)
  · intro x
    have hx : keep j (Sum.inl x.val)∈A.neighbors := by
      refine ⟨(keep_mem_survivingExternal _).mpr ⟨x.val,rfl⟩,?_⟩
      rw [A.routes.multiplicity_symm]
      exact (mem_filter.mp x.property).2
    refine ⟨⟨keep j (Sum.inl x.val),hx⟩,Subtype.ext ?_⟩
    exact Sum.inl.inj (A.neighborExternal_spec ⟨keep j (Sum.inl x.val),hx⟩))

theorem neighbors_card : Fintype.card A.neighbors=A.neighborFinset.card := by
  exact (Fintype.card_congr A.neighborEquiv).trans (Fintype.card_coe _)

theorem doubleExternal_card_le :
    (A.routes.doubleExternal (lastVertex j) A.neighbors).card≤
      (if j=0 then p-(j+1) else rho p-rho (j+1)) := by
  let D := univ.filter (fun x : X => A.routes.multiplicity (Sum.inl x) (Sum.inr (Fin.last j))=2)
  let f : A.routes.doubleExternal (lastVertex j) A.neighbors → D := fun x =>
    ⟨A.neighborExternal x.val,by
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [A.routes.multiplicity_symm,A.neighborExternal_spec x.val]
      exact (mem_filter.mp x.property).2⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (A.neighborExternal_injective (congrArg Subtype.val h))
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  exact hcard.trans (A.doubles (Fin.last j))

theorem doubleExternal_card_le_removed :
    (A.routes.doubleExternal (lastVertex j) A.neighbors).card≤p-(j+1) := by
  let f : A.routes.doubleExternal (lastVertex j) A.neighbors → A.used := fun x =>
    ⟨A.neighborExternal x.val,by
      apply A.double_used _ (Fin.last j)
      rw [A.routes.multiplicity_symm,A.neighborExternal_spec x.val]
      exact (mem_filter.mp x.property).2⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (A.neighborExternal_injective (congrArg Subtype.val h))
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  exact hcard.trans A.used_card

theorem exists_fresh_neighbor (hcard : A.used.card<Fintype.card A.neighbors) :
    ∃ x : X, keep j (Sum.inl x)∈A.neighbors ∧ x∉A.used := by
  by_contra h
  push_neg at h
  let f : A.neighbors → A.used := fun x => ⟨A.neighborExternal x,by
    apply h
    have he : keep j (Sum.inl (A.neighborExternal x))=x.val :=
      Subtype.ext (A.neighborExternal_spec x)
    exact he ▸ x.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact A.neighborExternal_injective (congrArg Subtype.val hxy)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hh
  omega

end GLWState
end
end Cycle13
