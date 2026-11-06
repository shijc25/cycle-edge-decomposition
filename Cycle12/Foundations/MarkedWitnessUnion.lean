import Cycle12.Foundations.ReverseLabelGeneral
import Cycle12.Foundations.TruncatedCutJanson

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem marked_residual_union_bound (markP ρ : unitInterval)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V→FiniteLaw Ξ)
    (E : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→Finset V→Prop)
    {cap rate : ℝ}
    (hE : ∀ T, (T.card:ℝ)≤cap → ∀ ξ A,
      (subsetBernoulli (univ\T) ρ).prob (E T ξ A)≤exp (-rate)) :
    (bernoulliSubset markP).expect (fun T => (κ T).expect (fun ξ =>
      (subsetBernoulli (univ\T) ρ).prob (fun S => (T.card:ℝ)≤cap ∧ ∃ A, E T ξ A S))) ≤
      exp (-rate+(markP:ℝ)*Fintype.card V) := by
  have hpoint : ∀ T, (κ T).expect (fun ξ =>
      (subsetBernoulli (univ\T) ρ).prob (fun S => (T.card:ℝ)≤cap ∧ ∃ A, E T ξ A S)) ≤
      (2:ℝ)^T.card*exp (-rate) := by
    intro T
    apply le_trans ((κ T).expect_mono (Y:=fun _ => (2:ℝ)^T.card*exp (-rate)) ?_)
      (le_of_eq ((κ T).expect_const _))
    intro ξ
    by_cases hT : (T.card:ℝ)≤cap
    · apply (FiniteLaw.prob_mono _ (fun S h => h.2)).trans
      apply (FiniteLaw.prob_exists_le_sum _ (fun A S => E T ξ A S)).trans
      have hh := sum_le_sum (s:=univ) (fun A _ => hE T hT ξ A)
      simpa only [sum_const,card_univ,label_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hh
    · simp only [hT,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
      positivity
  apply ((bernoulliSubset markP).expect_mono hpoint).trans
  rw [FiniteLaw.expect_mul_const]
  have hh := bernoulliSubset_generating_le_exp (V:=V) markP (z:=2) (by norm_num)
  norm_num only [show (2:ℝ)-1=1 by norm_num,mul_one] at hh
  apply (mul_le_mul_of_nonneg_right hh (exp_pos _).le).trans_eq
  rw [← exp_add]
  congr 1
  ring

theorem marked_graph_janson_union (markP ρ : unitInterval)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V→FiniteLaw Ξ)
    (J : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→SimpleGraph (↑(univ\T):Set V))
    (D : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→ℕ)
    (eligible : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→Prop)
    {cap rate τ : ℝ} (hτ0 : 0≤τ) (hτ1 : τ≤1)
    (hD : ∀ T, (T.card:ℝ)≤cap → ∀ ξ A, eligible T ξ A → ∀ v w,
      (J T ξ A).Adj v w → (J T ξ A).degree v+(J T ξ A).degree w≤D T ξ A+2)
    (hrate : ∀ T, (T.card:ℝ)≤cap → ∀ ξ A, eligible T ξ A →
      rate≤(1-τ)^2*(Fintype.card (J T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2/
        (2*(1+(D T ξ A:ℝ)*(ρ:ℝ)))) :
    (bernoulliSubset markP).expect (fun T => (κ T).expect (fun ξ =>
      (subsetBernoulli (univ\T) ρ).prob (fun S => (T.card:ℝ)≤cap ∧ ∃ A, eligible T ξ A ∧
        (sampledEdgeCount (J T ξ A) {v | v.val∈S}:ℝ)≤
          τ*(Fintype.card (J T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2))) ≤
      exp (-rate+(markP:ℝ)*Fintype.card V) := by
  apply marked_residual_union_bound
  intro T hT ξ A
  by_cases hel : eligible T ξ A
  · apply (FiniteLaw.prob_mono _ (fun S h => h.2)).trans
    apply (finite_graph_janson_fraction_restricted (univ\T) (J T ξ A) ρ
      (hD T hT ξ A hel) hτ0 hτ1).trans
    apply exp_le_exp.mpr
    have hh := hrate T hT ξ A hel
    simp only [neg_mul,neg_div,← Nat.card_eq_fintype_card] at hh ⊢
    exact neg_le_neg hh
  · simp only [hel,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
    exact (exp_pos _).le

theorem marked_graph_janson_original (p q markP ρ : unitInterval)
    (hmarkP : (markP:ℝ)=(p:ℝ)*(q:ℝ))
    (hρ : (1-(markP:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ)))
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V→FiniteLaw Ξ)
    (J : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→SimpleGraph (↑(univ\T):Set V))
    (D : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→ℕ)
    (eligible : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→Prop)
    {cap rate τ : ℝ} (hτ0 : 0≤τ) (hτ1 : τ≤1)
    (hD : ∀ T, (T.card:ℝ)≤cap → ∀ ξ A, eligible T ξ A → ∀ v w,
      (J T ξ A).Adj v w → (J T ξ A).degree v+(J T ξ A).degree w≤D T ξ A+2)
    (hrate : ∀ T, (T.card:ℝ)≤cap → ∀ ξ A, eligible T ξ A →
      rate≤(1-τ)^2*(Fintype.card (J T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2/
        (2*(1+(D T ξ A:ℝ)*(ρ:ℝ)))) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T => (κ T).prob
      (fun ξ => (T.card:ℝ)≤cap ∧ ∃ A, eligible T ξ A ∧
        (sampledEdgeCount (J T ξ A) {v | v.val∈U}:ℝ)≤
          τ*(Fintype.card (J T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2))) ≤
      exp (-rate+(markP:ℝ)*Fintype.card V) := by
  rw [marked_sampling_order_reversal p q markP ρ hmarkP hρ]
  have hs : ∀ T S : Finset V,
      {v : (↑(univ\T):Set V) | v.val∈T∪S}={v | v.val∈S} := by
    intro T S
    ext v
    have hv : v.val∉T := (mem_sdiff.mp v.property).2
    simp [hv]
  simp_rw [hs]
  have he : (bernoulliSubset markP).expect (fun T =>
      (subsetBernoulli (univ\T) ρ).expect (fun S => (κ T).prob
        (fun ξ => (T.card:ℝ)≤cap ∧ ∃ A, eligible T ξ A ∧
          (sampledEdgeCount (J T ξ A) {v | v.val∈S}:ℝ)≤
            τ*(Fintype.card (J T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2)))=
      (bernoulliSubset markP).expect (fun T => (κ T).expect (fun ξ =>
        (subsetBernoulli (univ\T) ρ).prob (fun S => (T.card:ℝ)≤cap ∧ ∃ A, eligible T ξ A ∧
          (sampledEdgeCount (J T ξ A) {v | v.val∈S}:ℝ)≤
            τ*(Fintype.card (J T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2))) := by
    congr 1
    funext T
    exact FiniteLaw.expect_comm _ _ _
  rw [he]
  exact marked_graph_janson_union markP ρ κ J D eligible hτ0 hτ1 hD hrate

end
end Cycle13
