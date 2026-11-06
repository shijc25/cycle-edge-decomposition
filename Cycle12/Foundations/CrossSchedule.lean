import Cycle12.Foundations.OrderedLinks
import Mathlib.Data.Prod.Lex

/-! Exact earlier-load bounds for the two-copy bipartite Link phase.
Old branches are processed in descending order. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev CrossSlot (p q : ℕ) := (Fin p)ᵒᵈ ×ₗ (Fin q ×ₗ Fin 2)

namespace CrossSlot
variable {p q : ℕ}
def old (i : CrossSlot p q) : Fin p := OrderDual.ofDual (ofLex i).1
def new (i : CrossSlot p q) : Fin q := (ofLex (ofLex i).2).1
def copy (i : CrossSlot p q) : Fin 2 := (ofLex (ofLex i).2).2

theorem ext {i j : CrossSlot p q} (ho : i.old=j.old) (hn : i.new=j.new)
    (hc : i.copy=j.copy) : i=j := by
  apply ofLex.injective
  apply Prod.ext
  · exact ho
  · apply ofLex.injective
    exact Prod.ext hn hc

def first (i : CrossSlot p q) : Fin p ⊕ Fin q := Sum.inl i.old
def second (i : CrossSlot p q) : Fin p ⊕ Fin q := Sum.inr i.new

theorem earlier_old_le {i j : CrossSlot p q} (hji : j < i) : i.old ≤ j.old := by
  rcases Prod.Lex.lt_iff.mp hji with h | ⟨h,_⟩
  · exact le_of_lt h
  · exact le_of_eq h.symm

theorem old_load_lt (i : CrossSlot p q) :
    priorLinkLoad first second i (Sum.inl i.old) < 2*q := by
  let S := univ.filter (fun j : CrossSlot p q =>
    j < i ∧ (Sum.inl i.old=first j ∨ Sum.inl i.old=second j))
  have hS : ∀ j : S, j.val < i ∧ j.val.old=i.old := by
    intro j
    have h := (mem_filter.mp j.property).2
    have he : i.old=j.val.old := by
      simpa only [first,second,Sum.inl.injEq,Sum.inl_ne_inr,or_false] using h.2
    exact ⟨h.1,he.symm⟩
  let f : S → Fin q × Fin 2 := fun j => (j.val.new,j.val.copy)
  have hinj : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    exact ext ((hS j).2.trans (hS k).2.symm) (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hmissing : (i.new,i.copy) ∉ Set.range f := by
    rintro ⟨j,hj⟩
    have he : j.val=i := ext (hS j).2 (congrArg Prod.fst hj) (congrArg Prod.snd hj)
    exact (ne_of_lt (hS j).1) he
  have h := Fintype.card_lt_of_injective_of_notMem f hinj hmissing
  simpa only [priorLinkLoad,S,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using h

theorem new_load_lt (i : CrossSlot p q) :
    priorLinkLoad first second i (Sum.inr i.new) < 2*(p-i.old.val) := by
  let S := univ.filter (fun j : CrossSlot p q =>
    j < i ∧ (Sum.inr i.new=first j ∨ Sum.inr i.new=second j))
  have hS : ∀ j : S, j.val < i ∧ j.val.new=i.new := by
    intro j
    have h := (mem_filter.mp j.property).2
    have he : i.new=j.val.new := by
      simpa only [first,second,Sum.inr.injEq,Sum.inr_ne_inl,false_or] using h.2
    exact ⟨h.1,he.symm⟩
  let f : S → {r : Fin p // i.old ≤ r} × Fin 2 := fun j =>
    (⟨j.val.old,earlier_old_le (hS j).1⟩,j.val.copy)
  have hinj : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    exact ext (congrArg (fun x : {r : Fin p // i.old ≤ r} × Fin 2 => x.1.val) he)
      ((hS j).2.trans (hS k).2.symm)
      (congrArg (fun x : {r : Fin p // i.old ≤ r} × Fin 2 => x.2) he)
  have hmissing : (⟨i.old,le_rfl⟩,i.copy) ∉ Set.range f := by
    rintro ⟨j,hj⟩
    have he : j.val=i := ext
      (congrArg (fun x : {r : Fin p // i.old ≤ r} × Fin 2 => x.1.val) hj)
      (hS j).2 (congrArg (fun x : {r : Fin p // i.old ≤ r} × Fin 2 => x.2) hj)
    exact (ne_of_lt (hS j).1) he
  have h := Fintype.card_lt_of_injective_of_notMem f hinj hmissing
  have hc : Fintype.card {r : Fin p // i.old ≤ r} = p-i.old.val := by
    rw [Fintype.card_subtype]
    have he : univ.filter (fun r : Fin p => i.old ≤ r) = Ici i.old := by ext; simp
    rw [he,Fin.card_Ici]
  simpa only [priorLinkLoad,S,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,hc,Nat.mul_comm] using h

theorem total_old_load (r : Fin p) :
    (univ.filter (fun j : CrossSlot p q =>
      Sum.inl r=first j ∨ Sum.inl r=second j)).card = 2*q := by
  let E : {j : CrossSlot p q // r=j.old} ≃ (Fin q × Fin 2) :=
    { toFun := fun j => (j.val.new,j.val.copy)
      invFun := fun x => ⟨toLex (OrderDual.toDual r,toLex x),rfl⟩
      left_inv := by
        intro j
        apply Subtype.ext
        exact ext j.property rfl rfl
      right_inv := fun _ => rfl }
  have h := Fintype.card_congr E
  simp only [Fintype.card_subtype,Fintype.card_prod,Fintype.card_fin] at h
  simpa only [first,second,Sum.inl.injEq,Sum.inl_ne_inr,or_false,Nat.mul_comm] using h

end CrossSlot
end
end Cycle13
