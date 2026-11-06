import Cycle12.Foundations.StarRouting

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {U V K I : Type} [Fintype K] [Fintype I] [DecidableEq U] [DecidableEq V]

theorem star_residual_degree (e : U ↪ V) (x : I → V) (hx : ∀ i u, x i≠e u)
    (a b : K → U) (other : I → U) (target : I ↪ U) (v : U) :
    Suppression.incidenceDegree (Sum.elim a target) (Sum.elim b other) v=
      Suppression.incidenceDegree (Sum.elim (e ∘ a) x) (e ∘ Sum.elim b other) (e v)+
      (univ.filter (fun i => target i=v)).card := by
  unfold Suppression.incidenceDegree
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have hkeep : (∑ i : K, ((if a i=v then (1:ℕ) else 0)+(if b i=v then 1 else 0)))=
      ∑ i : K, ((if e (a i)=e v then 1 else 0)+(if e (b i)=e v then 1 else 0)) := by
    simp only [e.injective.eq_iff]
  have hstar : (∑ i : I, ((if target i=v then (1:ℕ) else 0)+(if other i=v then 1 else 0)))=
      (∑ i : I, ((if x i=e v then 1 else 0)+(if e (other i)=e v then 1 else 0)))+
      (univ.filter (fun i => target i=v)).card := by
    simp only [if_neg (hx _ _),zero_add,e.injective.eq_iff,sum_add_distrib,sum_boole,Nat.cast_id]
    omega
  change (∑ i : K, ((if a i=v then (1:ℕ) else 0)+(if b i=v then 1 else 0)))+
      (∑ i : I, ((if target i=v then 1 else 0)+(if other i=v then 1 else 0)))=
      (∑ i : K, ((if e (a i)=e v then 1 else 0)+(if e (b i)=e v then 1 else 0)))+
      (∑ i : I, ((if x i=e v then 1 else 0)+(if e (other i)=e v then 1 else 0)))+
      (univ.filter (fun i => target i=v)).card
  rw [hkeep,hstar]
  omega

theorem star_residual_degree_le (e : U ↪ V) (x : I → V) (hx : ∀ i u, x i≠e u)
    (a b : K → U) (other : I → U) (target : I ↪ U) (v : U) :
    Suppression.incidenceDegree (Sum.elim a target) (Sum.elim b other) v ≤
      Suppression.incidenceDegree (Sum.elim (e ∘ a) x) (e ∘ Sum.elim b other) (e v)+1 := by
  rw [star_residual_degree e x hx a b other target v]
  have hh : (univ.filter (fun i => target i=v)).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact target.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  omega

theorem star_residual_protected_degree (e : U ↪ V) (x : I → V) (hx : ∀ i u, x i≠e u)
    (a b : K → U) (other : I → U) (target : I ↪ U) (v : U) (hv : ∀ i, target i≠v) :
    Suppression.incidenceDegree (Sum.elim a target) (Sum.elim b other) v=
      Suppression.incidenceDegree (Sum.elim (e ∘ a) x) (e ∘ Sum.elim b other) (e v) := by
  rw [star_residual_degree e x hx a b other target v]
  have hz : (univ.filter (fun i => target i=v)).card=0 := by simp [hv]
  rw [hz,add_zero]

end
end Cycle13
