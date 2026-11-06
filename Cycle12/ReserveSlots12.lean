import Cycle12.ReservedSpokeChoice12

namespace Cycle12
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

def ReserveSlots (A O : Finset V) := (A × Bool) ⊕ O

def reserveRoot (A O : Finset V) : ReserveSlots A O → V
  | .inl a => a.1.val
  | .inr o => o.val

instance reserveSlotsFintype (A O : Finset V) : Fintype (ReserveSlots A O) :=
  inferInstanceAs (Fintype ((A × Bool) ⊕ O))

def reserveFiberEquiv (A O : Finset V) (v : V) :
    {j : ReserveSlots A O // reserveRoot A O j = v} ≃
      ({a : A // a.val = v} × Bool) ⊕ {o : O // o.val = v} where
  toFun j := match j with
    | ⟨.inl (a,b),h⟩ => .inl (⟨a,h⟩,b)
    | ⟨.inr o,h⟩ => .inr ⟨o,h⟩
  invFun j := match j with
    | .inl (a,b) => ⟨.inl (a.val,b),a.property⟩
    | .inr o => ⟨.inr o.val,o.property⟩
  left_inv := by rintro ⟨j,h⟩; cases j <;> rfl
  right_inv := by intro j; cases j <;> rfl

theorem finset_vertex_fiber_card (A : Finset V) (v : V) :
    Fintype.card {a : A // a.val = v} = if v ∈ A then 1 else 0 := by
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    letI : Unique {a : A // a.val = v} :=
      ⟨⟨⟨⟨v,hv⟩,rfl⟩⟩,fun a => Subtype.ext (Subtype.ext a.property)⟩
    exact Fintype.card_unique
  · rw [if_neg hv]
    letI : IsEmpty {a : A // a.val = v} := ⟨fun a => hv (a.property ▸ a.val.property)⟩
    exact Fintype.card_eq_zero

@[simp] theorem reserveRoot_fiber_card (A O : Finset V) (v : V) :
    Fintype.card {j : ReserveSlots A O // reserveRoot A O j = v} =
      (if v ∈ A then 2 else 0) + (if v ∈ O then 1 else 0) := by
  rw [Fintype.card_congr (reserveFiberEquiv A O v),Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,finset_vertex_fiber_card,finset_vertex_fiber_card]
  split_ifs <;> omega

@[simp] theorem reserveSlots_card (A O : Finset V) :
    Fintype.card (ReserveSlots A O) = 2*A.card+O.card := by
  calc
    _ = Fintype.card ((A × Bool) ⊕ O) := Fintype.card_congr (Equiv.refl _)
    _ = _ := by simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,Fintype.card_bool]; omega

theorem reserveSlots_bounds (A O : Finset V) (hAO : Disjoint A O) :
    Fintype.card (ReserveSlots A O) ≤ 2*Fintype.card V ∧
      ∀ v, (univ.filter (fun j : ReserveSlots A O => reserveRoot A O j = v)).card ≤ 2 := by
  have hc := Finset.card_le_univ (A ∪ O)
  rw [card_union_of_disjoint hAO] at hc
  refine ⟨by rw [reserveSlots_card]; omega,?_⟩
  intro v
  have hn : ¬(v ∈ A ∧ v ∈ O) := fun h => Finset.disjoint_left.mp hAO h.1 h.2
  have hh : Fintype.card {j : ReserveSlots A O // reserveRoot A O j = v} ≤ 2 := by
    rw [reserveRoot_fiber_card]
    by_cases ha : v ∈ A
    · have ho : v ∉ O := fun ho => hn ⟨ha,ho⟩
      simp [ha,ho]
    · by_cases ho : v ∈ O <;> simp [ha,ho]
  rw [Fintype.card_subtype] at hh
  convert hh using 1

theorem reserveRoot_outside (A O C : Finset V) (hAC : Disjoint A C) (hOC : Disjoint O C)
    (j : ReserveSlots A O) : reserveRoot A O j ∉ C := by
  cases j with
  | inl a => exact fun hc => Finset.disjoint_left.mp hAC a.1.property hc
  | inr o => exact fun hc => Finset.disjoint_left.mp hOC o.property hc

end
end Cycle12
