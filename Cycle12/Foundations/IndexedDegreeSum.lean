import Cycle12.Foundations.LiftDegree
import Cycle12.Foundations.HubProtection

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem incidenceDegree_eq_ncard (a b : I → V) (v : V) :
    Suppression.incidenceDegree a b v={i | a i=v}.ncard+{i | b i=v}.ncard := by
  unfold Suppression.incidenceDegree
  rw [sum_add_distrib]
  simp only [sum_boole,Nat.cast_id,← Set.ncard_coe_finset,coe_filter,mem_univ,true_and]

theorem sum_incidenceDegree (a b : I → V) :
    (∑ v, Suppression.incidenceDegree a b v)=2*Fintype.card I := by
  unfold Suppression.incidenceDegree
  rw [sum_comm]
  simp [sum_add_distrib,eq_comm,mul_comm]

theorem indexed_card_le_degree_cap (a b : I → V) {q : ℕ}
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ q) :
    Fintype.card I ≤ q*Fintype.card V := by
  have hh := sum_le_sum (s:=univ) (fun v _ => hd v)
  rw [sum_incidenceDegree] at hh
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at hh
  rw [Nat.mul_comm (Fintype.card V) q] at hh
  omega

theorem append_edge_degree (a b : I → V) (x y v : V) :
    Suppression.incidenceDegree (Sum.elim a (fun _ : Unit => x))
      (Sum.elim b (fun _ : Unit => y)) v=
      Suppression.incidenceDegree a b v+(if x=v then 1 else 0)+(if y=v then 1 else 0) := by
  unfold Suppression.incidenceDegree
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,add_assoc]
  rfl

theorem exists_indexed_edge_away (a b : I → V) (hne : ∀ i, a i≠b i) {u v : V}
    (hdegree : Suppression.incidenceDegree a b v < Suppression.incidenceDegree a b u) :
    ∃ i, a i≠v ∧ b i≠v := by
  by_contra h
  push Not at h
  have hsub : indexedIncident a b u ⊆ indexedIncident a b v := by
    intro i hi
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    by_cases ha : a i=v
    · exact Or.inl ha
    · exact Or.inr (h i ha)
  have hh := card_le_card hsub
  rw [indexedIncident_card_eq a b hne,indexedIncident_card_eq a b hne] at hh
  omega

theorem single_even_deficit (a b : I → V) (v : V) {k : ℕ}
    (hv : Suppression.incidenceDegree a b v < 2*k)
    (hother : ∀ u, u≠v → Suppression.incidenceDegree a b u=2*k) :
    Suppression.incidenceDegree a b v+2 ≤ 2*k := by
  have hsum := sum_erase_add (s:=univ) (f:=Suppression.incidenceDegree a b) (mem_univ v)
  have he : (∑ u∈univ.erase v, Suppression.incidenceDegree a b u)=(Fintype.card V-1)*(2*k) := by
    rw [sum_congr rfl (fun u hu => hother u (mem_erase.mp hu).1)]
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,card_erase_of_mem (mem_univ v),card_univ]
  rw [he,sum_incidenceDegree] at hsum
  have hm : (Fintype.card V-1)*(2*k)=2*((Fintype.card V-1)*k) := by ring
  rw [hm] at hsum
  omega

theorem singleton_lift_card (i : I) :
    Fintype.card (LiftIndex ({i} : Finset I))=Fintype.card I+1 := by
  simp only [LiftIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,card_singleton,
    Fintype.card_bool,one_mul]
  have hrest : Fintype.card {j : I // j∉({i} : Finset I)}+1=Fintype.card I := by
    have hsum := Fintype.card_congr (Equiv.sumCompl (fun j : I => j∈({i} : Finset I)))
    simp only [Fintype.card_sum,Fintype.card_coe,card_singleton] at hsum
    omega
  omega

end
end Cycle13
