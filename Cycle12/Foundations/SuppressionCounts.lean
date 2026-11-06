import Cycle12.Foundations.RoutedEdges

/-! Degree and parity accounting for suppressing a vertex of an indexed
multigraph. Loops at the removed vertex are discarded and counted twice. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma sum_subtype_indicator {I : Type} [Fintype I] (P : I → Prop) (f : I → ℕ) :
    (∑ i : {i // P i}, f i.val)=∑ i, if P i then f i else 0 := by
  rw [← sum_subtype (univ.filter P) (fun i => by simp) f,sum_filter]

namespace Suppression
variable {I V : Type} [Fintype I] [DecidableEq V] (a b : I → V) (z : V)

def portPred (i : I) : Prop := (a i=z ∧ b i≠z) ∨ (b i=z ∧ a i≠z)
def keepPred (i : I) : Prop := a i≠z ∧ b i≠z
def otherEnd (i : I) : V := if a i=z then b i else a i
def incidenceDegree (v : V) : ℕ :=
  ∑ i, ((if a i=v then 1 else 0)+(if b i=v then 1 else 0))

lemma otherEnd_ne (i : {i // portPred a b z i}) : otherEnd a b z i.val ≠ z := by
  have hi := i.property
  dsimp [portPred] at hi
  by_cases ha : a i.val=z <;> simp_all [otherEnd]

theorem degree_port_parity :
    incidenceDegree a b z=Fintype.card {i // portPred a b z i}+
      2*(univ.filter (fun i => a i=z ∧ b i=z)).card := by
  have hp : ∀ i : I, ((if a i=z then (1:ℕ) else 0)+(if b i=z then 1 else 0))=
      (if portPred a b z i then 1 else 0)+2*(if a i=z ∧ b i=z then 1 else 0) := by
    intro i
    by_cases ha : a i=z <;> by_cases hb : b i=z <;> simp [portPred,ha,hb]
  unfold incidenceDegree
  rw [sum_congr rfl (fun i _ => hp i)]
  rw [sum_add_distrib,← mul_sum]
  simp [Fintype.card_subtype]

theorem degree_retained (v : V) (hv : v≠z) :
    incidenceDegree a b v=
      (∑ i : {i // keepPred a b z i},
        ((if a i.val=v then 1 else 0)+(if b i.val=v then 1 else 0)))+
      (univ.filter (fun i : {i // portPred a b z i} => otherEnd a b z i.val=v)).card := by
  have hp : ∀ i : I, ((if a i=v then (1:ℕ) else 0)+(if b i=v then 1 else 0))=
      (if keepPred a b z i then ((if a i=v then 1 else 0)+(if b i=v then 1 else 0)) else 0)+
      (if portPred a b z i then (if otherEnd a b z i=v then 1 else 0) else 0) := by
    intro i
    by_cases ha : a i=z <;> by_cases hb : b i=z <;>
      simp [keepPred,portPred,otherEnd,ha,hb,hv.symm]
  unfold incidenceDegree
  rw [sum_congr rfl (fun i _ => hp i)]
  rw [sum_add_distrib,← sum_subtype_indicator,← sum_subtype_indicator]
  simp

theorem even_ports_of_even_degree (h : Even (incidenceDegree a b z)) :
    Even (Fintype.card {i // portPred a b z i}) := by
  rw [degree_port_parity] at h
  exact (Nat.even_add.mp h).mpr (even_two_mul _)

end Suppression
end
end Cycle13
