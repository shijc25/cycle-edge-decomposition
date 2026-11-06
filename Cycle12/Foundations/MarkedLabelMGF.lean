import Cycle12.Foundations.SubsetBernoulliMGF

/-! Label-sensitive counting in the mark-first sampling experiment.
The side may depend on the marked set and its labels, but not on the
independent residual sample. The exact label sum pays for marked vertices
only in the side bearing that label. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem marked_sample_inter_card (T S C : Finset V) :
    ((T∪S)∩C).card=(T∩C).card+(S∩(C\T)).card := by
  have he : (T∪S)∩C=(T∩C)∪(S∩(C\T)) := by ext v; simp; tauto
  rw [he,card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (by
    intro v hv hw
    exact (mem_sdiff.mp (mem_inter.mp hw).2).2 (mem_inter.mp hv).1)

theorem marked_label_tail (ρ : unitInterval) (T A C : Finset V) (hmark : C∩T=A)
    (a p b θ : ℝ) (hθ : 0 < θ) (hslope : (ρ:ℝ)*(exp θ-1) ≤ θ*a*p) :
    (subsetBernoulli (univ\T) ρ).prob (fun S => a*p*C.card+b < (((T∪S)∩C).card:ℝ)) ≤
      exp (-θ*b+θ*(1-a*p)*A.card) := by
  let D := C\T
  have hc : C.card=A.card+D.card := by
    have hh := card_sdiff_add_card_inter C T
    rw [hmark] at hh
    change D.card+A.card=C.card at hh
    omega
  have hcount : ∀ S : Finset V, ((T∪S)∩C).card=A.card+(S∩D).card := by
    intro S
    rw [marked_sample_inter_card,inter_comm T C,hmark]
  have hmgf : (subsetBernoulli (univ\T) ρ).expect (fun S => exp (θ*(((T∪S)∩C).card:ℝ))) ≤
      exp (θ*A.card)*exp ((ρ:ℝ)*(exp θ-1)*D.card) := by
    have hex : (fun S : Finset V => exp (θ*(((T∪S)∩C).card:ℝ)))=
        (fun S => exp (θ*A.card)*exp (θ*(S∩D).card)) := by
      funext S
      rw [hcount,Nat.cast_add,mul_add,exp_add]
    rw [hex,FiniteLaw.expect_const_mul]
    exact mul_le_mul_of_nonneg_left (subsetBernoulli_count_mgf_le (univ\T) ρ D θ (sdiff_subset_sdiff_left T (subset_univ C))) (exp_pos _).le
  have hh := (subsetBernoulli (univ\T) ρ).exp_markov (fun S => (((T∪S)∩C).card:ℝ)) θ
    (a*p*C.card+b) hθ
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_left hmgf (exp_pos _).le)
  rw [← exp_add,← exp_add]
  apply exp_le_exp.mpr
  have hs := mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg D.card : (0:ℝ) ≤ D.card)
  have hcR : (C.card:ℝ)=(A.card:ℝ)+(D.card:ℝ) := by exact_mod_cast hc
  rw [hcR]
  nlinarith

theorem marked_all_labels_tail (ρ : unitInterval) (T : Finset V)
    (side : {A : Finset V // A⊆T} → Finset V)
    (hmark : ∀ A, side A∩T=A.val) (a p b θ : ℝ) (hθ : 0 < θ)
    (hslope : (ρ:ℝ)*(exp θ-1) ≤ θ*a*p) :
    (subsetBernoulli (univ\T) ρ).prob
      (fun S => ∃ A, a*p*(side A).card+b < (((T∪S)∩side A).card:ℝ)) ≤
        exp (-θ*b)*(1+exp (θ*(1-a*p)))^T.card := by
  have hh := (subsetBernoulli (univ\T) ρ).prob_exists_le_sum
    (fun A S => a*p*(side A).card+b < (((T∪S)∩side A).card:ℝ))
  apply hh.trans
  calc
    _ ≤ ∑ A : {A : Finset V // A⊆T}, exp (-θ*b+θ*(1-a*p)*A.val.card) := by
      exact sum_le_sum (fun A _ => marked_label_tail ρ T A.val (side A) (hmark A) a p b θ hθ hslope)
    _ = exp (-θ*b)*(1+exp (θ*(1-a*p)))^T.card := by
      simp_rw [exp_add]
      rw [← mul_sum]
      congr 1
      rw [← sum_subtype T.powerset (p:=fun A => A⊆T) (fun A => mem_powerset)
        (fun A => exp (θ*(1-a*p)*A.card)),label_exponential_sum]

theorem marked_label_mgf_unconditional (markP ρ : unitInterval)
    (side : ∀ T : Finset V, {A : Finset V // A⊆T} → Finset V)
    (hmark : ∀ T A, side T A∩T=A.val) (a p b θ : ℝ) (hθ : 0 < θ)
    (hslope : (ρ:ℝ)*(exp θ-1) ≤ θ*a*p) :
    (bernoulliSubset markP).expect (fun T => (subsetBernoulli (univ\T) ρ).prob
      (fun S => ∃ A, a*p*(side T A).card+b < (((T∪S)∩side T A).card:ℝ))) ≤
        exp (-θ*b+(markP:ℝ)*exp (θ*(1-a*p))*Fintype.card V) := by
  apply le_trans ((bernoulliSubset markP).expect_mono (fun T =>
    marked_all_labels_tail ρ T (side T) (hmark T) a p b θ hθ hslope))
  rw [FiniteLaw.expect_const_mul]
  have hh := bernoulliSubset_generating_le_exp (V:=V) markP
    (z:=1+exp (θ*(1-a*p))) (by positivity)
  have he : (1+exp (θ*(1-a*p))-1)=exp (θ*(1-a*p)) := by ring
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hh (exp_pos _).le).trans_eq (exp_add _ _).symm

theorem marked_label_mgf_with_auxiliary (markP ρ : unitInterval)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V → FiniteLaw Ξ)
    (side : ∀ T : Finset V, Ξ → {A : Finset V // A⊆T} → Finset V)
    (hmark : ∀ T ξ A, side T ξ A∩T=A.val) (a p b θ : ℝ) (hθ : 0 < θ)
    (hslope : (ρ:ℝ)*(exp θ-1) ≤ θ*a*p) :
    (bernoulliSubset markP).expect (fun T => (κ T).expect (fun ξ => (subsetBernoulli (univ\T) ρ).prob
      (fun S => ∃ A, a*p*(side T ξ A).card+b < (((T∪S)∩side T ξ A).card:ℝ)))) ≤
        exp (-θ*b+(markP:ℝ)*exp (θ*(1-a*p))*Fintype.card V) := by
  have hconditional : ∀ T, (κ T).expect (fun ξ => (subsetBernoulli (univ\T) ρ).prob
      (fun S => ∃ A, a*p*(side T ξ A).card+b < (((T∪S)∩side T ξ A).card:ℝ))) ≤
        exp (-θ*b)*(1+exp (θ*(1-a*p)))^T.card := by
    intro T
    have hh := (κ T).expect_mono (fun ξ =>
      marked_all_labels_tail ρ T (side T ξ) (hmark T ξ) a p b θ hθ hslope)
    simpa only [FiniteLaw.expect_const] using hh
  apply le_trans ((bernoulliSubset markP).expect_mono hconditional)
  rw [FiniteLaw.expect_const_mul]
  have hh := bernoulliSubset_generating_le_exp (V:=V) markP
    (z:=1+exp (θ*(1-a*p))) (by positivity)
  have he : (1+exp (θ*(1-a*p))-1)=exp (θ*(1-a*p)) := by ring
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hh (exp_pos _).le).trans_eq (exp_add _ _).symm

end
end Cycle13
