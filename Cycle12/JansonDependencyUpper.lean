import Cycle12.BernoulliJansonSharp

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem full_janson_phi_nonneg (tau : ℝ) (ht : 0 ≤ tau) : 0 ≤ fullJansonPhi tau := by
  have hh := self_sub_one_le_mul_log ht
  unfold fullJansonPhi
  linarith

theorem full_janson_dependency_upper (phi m a b : ℝ) (hphi : 0 ≤ phi)
    (ha : 0 < a) (hab : a ≤ b) :
    exp (-phi*m^2/a) ≤ exp (-phi*m^2/b) := by
  apply exp_le_exp.mpr
  apply (div_le_div_iff₀ ha (ha.trans_le hab)).mpr
  nlinarith [mul_nonneg (mul_nonneg hphi (sq_nonneg m)) (sub_nonneg.mpr hab)]

theorem bernoulli_janson_full_lower_tail_upper (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (K : I → Finset I)
    (hK : ∀ i j, j∉K i → Disjoint (E i) (E j)) (hself : ∀ i, i∈K i)
    (p : unitInterval) (hm : 0 < occurrenceMean E p) (B : ℝ)
    (hB : occurrenceLambda E K p ≤ B) (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (subsetBernoulli D p).prob (fun S => occurrenceCount E S ≤ tau*occurrenceMean E p) ≤
      exp (-fullJansonPhi tau*(occurrenceMean E p)^2/B) := by
  apply (bernoulli_janson_full_lower_tail D E hE K hK hself p hm tau ht0 ht1).trans
  exact full_janson_dependency_upper _ _ _ _ (full_janson_phi_nonneg tau ht0)
    (hm.trans_le (occurrence_lambda_ge_mean E K hself p)) hB

end
end Cycle12
