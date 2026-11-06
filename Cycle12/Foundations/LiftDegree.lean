import Cycle12.Foundations.DemandRouting

/-! Exact degree and looplessness accounting for a batch of edge lifts. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem lift_incidence_degree (a b hub : I → V) (F : Finset I) (v : V) :
    Suppression.incidenceDegree (liftLeft a hub F) (liftRight b hub F) v=
      Suppression.incidenceDegree a b v+2*(F.filter (fun i => hub i=v)).card := by
  have hs : Suppression.incidenceDegree (liftLeft a hub F) (liftRight b hub F) v=
      (∑ i : {i // i∉F}, ((if a i.val=v then (1:ℕ) else 0)+(if b i.val=v then 1 else 0)))+
      (∑ i : F, ((if a i.val=v then 1 else 0)+(if b i.val=v then 1 else 0)+
        2*(if hub i.val=v then 1 else 0))) := by
    unfold Suppression.incidenceDegree
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    congr 1
    apply sum_congr rfl
    intro i _
    simp only [Fintype.sum_bool,liftLeft,liftRight]
    omega
  rw [hs]
  have hpartition :
      (∑ i : {i // i∉F}, ((if a i.val=v then (1:ℕ) else 0)+(if b i.val=v then 1 else 0)))+
      (∑ i : F, ((if a i.val=v then 1 else 0)+(if b i.val=v then 1 else 0)))=
      Suppression.incidenceDegree a b v := by
    let weight : I → ℕ := fun i => (if a i=v then 1 else 0)+(if b i=v then 1 else 0)
    rw [← sum_subtype (univ\F) (p:=fun i => i∉F) (fun i => by simp) weight,
      ← sum_subtype F (p:=fun i => i∈F) (fun i => Iff.rfl) weight]
    exact sum_sdiff (subset_univ F)
  have hf : (∑ i : F, if hub i.val=v then (1:ℕ) else 0)=(F.filter (fun i => hub i=v)).card := by
    rw [← sum_subtype F (p:=fun i => i∈F) (fun i => Iff.rfl) (fun i => if hub i=v then (1:ℕ) else 0)]
    simp only [sum_boole,Nat.cast_id]
  conv_lhs => rhs; rw [sum_add_distrib,← mul_sum]
  rw [hf]
  omega

theorem lift_loopless (a b hub : I → V) (F : Finset I) (hne : ∀ i, a i≠b i)
    (hhub : ∀ i∈F, hub i≠a i ∧ hub i≠b i) :
    ∀ i : LiftIndex F, liftLeft a hub F i≠liftRight b hub F i := by
  rintro (i | ⟨i,q⟩)
  · exact hne i.val
  · cases q
    · exact (hhub i.val i.property).1.symm
    · exact (hhub i.val i.property).2

end
end Cycle13
