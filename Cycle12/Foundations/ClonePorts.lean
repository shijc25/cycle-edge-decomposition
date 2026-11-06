import Cycle12.Foundations.ControlledSuppression

/-! Identify the actual one/two-edge external port fibers with GLW's
original-and-clone vertices, preserving each port's retained endpoint. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem exists_clone_fiber_equiv {I V : Type} [Fintype I] [Fintype V]
    [DecidableEq V] (o : I → V) (D : Finset V)
    (hc : ∀ v, Fintype.card {i // o i=v}=1+(if v∈D then 1 else 0)) :
    ∃ E : (V ⊕ D) ≃ I, ∀ a, o (E a)=cloneOrigin D a := by
  have hcard : ∀ v, Fintype.card {a : V ⊕ D // cloneOrigin D a=v}=
      Fintype.card {i // o i=v} := by
    intro v
    rw [hc,Fintype.card_subtype,CloneMatching.origin_fiber_card]
  let E := fun v => Fintype.equivOfCardEq (hcard v)
  exact ⟨Equiv.ofFiberEquiv E,Equiv.ofFiberEquiv_map E⟩

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)

theorem portTip_eq_iff (i : R.Ports z) (x : {v : V // v≠z}) :
    R.portTip z i=x ↔ R.edge i.val=s(z,x.val) := by
  have hp := i.property
  change (R.left i.val=z ∧ R.right i.val≠z) ∨
    (R.right i.val=z ∧ R.left i.val≠z) at hp
  rw [Subtype.ext_iff]
  change Suppression.otherEnd R.left R.right z i.val=x.val ↔ _
  by_cases ha : R.left i.val=z
  · rw [Suppression.otherEnd,if_pos ha]
    change R.right i.val=x.val ↔ s(R.left i.val,R.right i.val)=s(z,x.val)
    rw [ha,Sym2.eq_iff]
    simp [x.property,eq_comm]
    intro h₁ h₂
    exact h₁.symm.trans h₂
  · have hb := (hp.resolve_left (fun h => ha h.1)).1
    rw [Suppression.otherEnd,if_neg ha]
    change R.left i.val=x.val ↔ s(R.left i.val,R.right i.val)=s(z,x.val)
    rw [hb,Sym2.eq_iff]
    simp [ha,x.property,eq_comm]

theorem portTip_fiber_card (x : {v : V // v≠z}) :
    Fintype.card {i : R.Ports z // R.portTip z i=x}=R.multiplicity z x.val := by
  rw [multiplicity,← Fintype.card_subtype]
  apply Fintype.card_congr
  refine {
    toFun := fun i => ⟨i.val.val,(R.portTip_eq_iff z i.val x).mp i.property⟩
    invFun := fun i => ⟨⟨i.val,?_⟩,?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  · change (R.left i.val=z ∧ R.right i.val≠z) ∨ (R.right i.val=z ∧ R.left i.val≠z)
    rcases Sym2.eq_iff.mp i.property with h | h
    · exact Or.inl ⟨h.1,fun he => x.property (h.2.symm.trans he)⟩
    · exact Or.inr ⟨h.2,fun he => x.property (h.1.symm.trans he)⟩
  · apply (R.portTip_eq_iff z _ x).mpr
    exact i.property

variable [Fintype V] (X : Set {v : V // v≠z})

def doubleExternal : Finset X := univ.filter (fun x => R.multiplicity z x.val.val=2)

def externalPortMap (i : {i : R.Ports z // R.portTip z i∈X}) : X :=
  ⟨R.portTip z i.val,i.property⟩

theorem externalPortMap_fiber_card (x : X) :
    Fintype.card {i // R.externalPortMap z X i=x}=R.multiplicity z x.val.val := by
  rw [← R.portTip_fiber_card z x.val]
  apply Fintype.card_congr
  exact {
    toFun := fun i => ⟨i.val.val,congrArg Subtype.val i.property⟩
    invFun := fun i => ⟨⟨i.val,by rw [i.property]; exact x.property⟩,Subtype.ext i.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem exists_clone_port_embedding
    (hpos : ∀ x : X, 0<R.multiplicity z x.val.val)
    (hmax : ∀ x : X, R.multiplicity z x.val.val≤2) :
    ∃ E : (X ⊕ R.doubleExternal z X) ↪ R.Ports z,
      (∀ a, R.portTip z (E a)=(cloneOrigin (R.doubleExternal z X) a).val) ∧
      (∀ i, R.portTip z i∈X → ∃ a, E a=i) := by
  have hc : ∀ x : X, Fintype.card {i // R.externalPortMap z X i=x}=
      1+(if x∈R.doubleExternal z X then 1 else 0) := by
    intro x
    rw [externalPortMap_fiber_card]
    have hp := hpos x
    have hm := hmax x
    simp only [doubleExternal,mem_filter,mem_univ,true_and]
    split_ifs <;> omega
  obtain ⟨E,hE⟩ := exists_clone_fiber_equiv (R.externalPortMap z X)
    (R.doubleExternal z X) hc
  refine ⟨E.toEmbedding.trans (Function.Embedding.subtype _),?_,?_⟩
  · intro a
    exact congrArg Subtype.val (hE a)
  · intro i hi
    obtain ⟨a,ha⟩ := E.surjective ⟨i,hi⟩
    exact ⟨a,congrArg Subtype.val ha⟩

end RoutedEdges
end
end Cycle13
