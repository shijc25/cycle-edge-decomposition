import Mathlib

namespace Cycle12
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I C : Type} [Fintype I] [Fintype C]

/-- Consecutive bounded groups of a finite family. A final empty group
is harmless; it is charged only once per color, never once per demand. -/
def demandGroup (Q : ℕ) (i : I) : Fin (Fintype.card I/Q+1) :=
  ⟨(Fintype.equivFin I i).val/Q,Nat.lt_succ_of_le (Nat.div_le_div_right (Fintype.equivFin I i).isLt.le)⟩

theorem demandGroup_fiber_card {Q : ℕ} (hQ : 0<Q) (b : Fin (Fintype.card I/Q+1)) :
    Fintype.card {i : I // demandGroup Q i=b} ≤ Q := by
  let f : {i : I // demandGroup Q i=b} → Fin Q :=
    fun i => ⟨(Fintype.equivFin I i.val).val%Q,Nat.mod_lt _ hQ⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hm : (Fintype.equivFin I i.val).val%Q=(Fintype.equivFin I j.val).val%Q :=
      congrArg Fin.val hij
    have hd : (Fintype.equivFin I i.val).val/Q=(Fintype.equivFin I j.val).val/Q :=
      congrArg Fin.val (i.property.trans j.property.symm)
    apply Subtype.ext
    apply (Fintype.equivFin I).injective
    apply Fin.ext
    have hi := Nat.mod_add_div (Fintype.equivFin I i.val).val Q
    have hj := Nat.mod_add_div (Fintype.equivFin I j.val).val Q
    rw [hm,hd] at hi
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem demandGroup_count_bound {Q : ℕ} (hQ : 0<Q) :
    (Fintype.card (Fin (Fintype.card I/Q+1)):ℝ) ≤ (Fintype.card I:ℝ)/Q+1 := by
  have hmul := Nat.div_mul_le_self (Fintype.card I) Q
  have hmulR : ((Fintype.card I/Q:ℕ):ℝ)*(Q:ℝ) ≤ Fintype.card I := by exact_mod_cast hmul
  have hdiv : ((Fintype.card I/Q:ℕ):ℝ) ≤ (Fintype.card I:ℝ)/Q :=
    (le_div_iff₀ (by exact_mod_cast hQ)).mpr hmulR
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using add_le_add hdiv (le_refl (1:ℝ))

def ColoredDemandGroups (color : I → C) (Q : ℕ) :=
  Σ c : C, Fin (Fintype.card {i : I // color i=c}/Q+1)

instance (color : I → C) (Q : ℕ) : Fintype (ColoredDemandGroups color Q) :=
  inferInstanceAs (Fintype (Σ c : C, Fin (Fintype.card {i : I // color i=c}/Q+1)))

def coloredDemandGroup (color : I → C) (Q : ℕ) (i : I) : ColoredDemandGroups color Q :=
  ⟨color i,demandGroup Q (⟨i,rfl⟩ : {j : I // color j=color i})⟩

theorem coloredDemandGroup_on_fiber (color : I → C) (Q : ℕ) (c : C)
    (j : {i : I // color i=c}) :
    coloredDemandGroup color Q j.val = ⟨c,demandGroup Q j⟩ := by
  rcases j with ⟨j,hj⟩
  subst c
  rfl

theorem coloredDemandGroup_fiber_card (color : I → C) {Q : ℕ} (hQ : 0<Q)
    (b : ColoredDemandGroups color Q) :
    Fintype.card {i : I // coloredDemandGroup color Q i=b} ≤ Q := by
  rcases b with ⟨c,b⟩
  let f : {i : I // coloredDemandGroup color Q i=⟨c,b⟩} →
      {j : {i : I // color i=c} // demandGroup Q j=b} := fun i => by
    have hc : color i.val=c := congrArg Sigma.fst i.property
    let j : {i : I // color i=c} := ⟨i.val,hc⟩
    refine ⟨j,?_⟩
    have hh := (coloredDemandGroup_on_fiber color Q c j).symm.trans i.property
    exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (by simpa only [f] using congrArg (fun x => x.val.val) hij)
  exact (Fintype.card_le_of_injective f hf).trans (demandGroup_fiber_card hQ b)

theorem coloredDemandGroup_same_color (color : I → C) (Q : ℕ) {i j : I}
    (h : coloredDemandGroup color Q i=coloredDemandGroup color Q j) : color i=color j :=
  congrArg Sigma.fst h

/-- Summing ceiling losses costs at most the color count. -/
theorem coloredDemandGroups_count_bound (color : I → C) {Q : ℕ} (hQ : 0<Q) :
    (Fintype.card (ColoredDemandGroups color Q):ℝ) ≤
      (Fintype.card I:ℝ)/Q+Fintype.card C := by
  have hh := Finset.sum_le_sum (fun c (_ : c∈(univ:Finset C)) =>
    demandGroup_count_bound (I:={i : I // color i=c}) hQ)
  have he : (∑ c,Fintype.card {i : I // color i=c})=Fintype.card I := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv color)
  have heR : (∑ c,(Fintype.card {i : I // color i=c}:ℝ))=Fintype.card I := by
    exact_mod_cast he
  change ((Fintype.card (Σ c : C,Fin (Fintype.card {i : I // color i=c}/Q+1))):ℝ) ≤ _
  rw [Fintype.card_sigma,Nat.cast_sum]
  rw [Finset.sum_add_distrib,←Finset.sum_div,heR] at hh
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hh

end
end Cycle12
