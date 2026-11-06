import Cycle12.Foundations.MarkedLabelMGF

/-! The label-aware MGF estimate in the original sample-then-mark
experiment, including an arbitrary finite auxiliary law depending only
on the marked set. The change of exposure order is proved, not assumed. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem marked_label_tail_original (p q markP ρ : unitInterval)
    (hmarkP : (markP:ℝ)=(p:ℝ)*(q:ℝ))
    (hρ : (1-(markP:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ)))
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V → FiniteLaw Ξ)
    (side : ∀ T : Finset V, Ξ → {A : Finset V // A⊆T} → Finset V)
    (hmark : ∀ T ξ A, side T ξ A∩T=A.val) (a b θ : ℝ) (hθ : 0 < θ)
    (hslope : (ρ:ℝ)*(exp θ-1) ≤ θ*a*(p:ℝ)) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T => (κ T).prob
      (fun ξ => ∃ A, a*(p:ℝ)*(side T ξ A).card+b < ((U∩side T ξ A).card:ℝ)))) ≤
        exp (-θ*b+(markP:ℝ)*exp (θ*(1-a*(p:ℝ)))*Fintype.card V) := by
  rw [marked_sampling_order_reversal p q markP ρ hmarkP hρ]
  have he : (bernoulliSubset markP).expect (fun T =>
      (subsetBernoulli (univ\T) ρ).expect (fun S => (κ T).prob
        (fun ξ => ∃ A, a*(p:ℝ)*(side T ξ A).card+b < (((T∪S)∩side T ξ A).card:ℝ))))=
      (bernoulliSubset markP).expect (fun T => (κ T).expect (fun ξ =>
        (subsetBernoulli (univ\T) ρ).prob
          (fun S => ∃ A, a*(p:ℝ)*(side T ξ A).card+b < (((T∪S)∩side T ξ A).card:ℝ)))) := by
    congr 1
    funext T
    exact FiniteLaw.expect_comm _ _ _
  rw [he]
  exact marked_label_mgf_with_auxiliary markP ρ κ side hmark a p b θ hθ hslope

theorem label_aware_mgf (p q : unitInterval) (hpq : (p:ℝ)*(q:ℝ) < 1)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V → FiniteLaw Ξ)
    (side : ∀ T : Finset V, Ξ → {A : Finset V // A⊆T} → Finset V)
    (hmark : ∀ T ξ A, side T ξ A∩T=A.val) (a b θ : ℝ) (hθ : 0 < θ)
    (hslope : exp θ-1 ≤ θ*a) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T => (κ T).prob
      (fun ξ => ∃ A, a*(p:ℝ)*(side T ξ A).card+b < ((U∩side T ξ A).card:ℝ)))) ≤
        exp (-θ*b+(p:ℝ)*(q:ℝ)*exp (θ*(1-a*(p:ℝ)))*Fintype.card V) := by
  apply marked_label_tail_original p q (markProbability p q) (residualProbability p q hpq)
    rfl (residualProbability_identity p q hpq) κ side hmark a b θ hθ
  have hrem := (residual_probability_bounds p q hpq).2
  have he : 0 ≤ exp θ-1 := by have hh := Real.one_le_exp hθ.le; linarith
  calc
    _ ≤ (p:ℝ)*(exp θ-1) := mul_le_mul_of_nonneg_right hrem he
    _ ≤ (p:ℝ)*(θ*a) := mul_le_mul_of_nonneg_left hslope p.2.1
    _ = _ := by ring

theorem label_aware_mgf_two_families (p q : unitInterval) (hpq : (p:ℝ)*(q:ℝ) < 1)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V → FiniteLaw Ξ)
    (side : Bool → ∀ T : Finset V, Ξ → {A : Finset V // A⊆T} → Finset V)
    (hmark : ∀ i T ξ A, side i T ξ A∩T=A.val) (a b θ : ℝ) (hθ : 0 < θ)
    (hslope : exp θ-1 ≤ θ*a) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T => (κ T).prob
      (fun ξ => ∃ i A, a*(p:ℝ)*(side i T ξ A).card+b < ((U∩side i T ξ A).card:ℝ)))) ≤
        2*exp (-θ*b+(p:ℝ)*(q:ℝ)*exp (θ*(1-a*(p:ℝ)))*Fintype.card V) := by
  have hh := (bernoulliSubset p).expect_mono (fun U =>
    (subsetBernoulli U q).expect_mono (fun T => (κ T).prob_exists_le_sum
      (fun i ξ => ∃ A, a*(p:ℝ)*(side i T ξ A).card+b < ((U∩side i T ξ A).card:ℝ))))
  apply hh.trans
  simp_rw [FiniteLaw.expect_sum]
  have hsum := sum_le_sum (s:=univ) (fun i _ =>
    label_aware_mgf p q hpq κ (side i) (hmark i) a b θ hθ hslope)
  simpa only [sum_const,card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat] using hsum

end
end Cycle13
