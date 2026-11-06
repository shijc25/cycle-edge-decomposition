import Cycle12.BernoulliJansonSlope
import Cycle12.LaplaceLowerTail

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem bernoulli_janson_laplace (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (K : I → Finset I)
    (hK : ∀ i j, j∉K i → Disjoint (E i) (E j)) (hself : ∀ i, i∈K i)
    (p : unitInterval) (hm : 0 < occurrenceMean E p) (s : ℝ) (hs : 0 ≤ s) :
    finiteLaplace (subsetBernoulli D p) (occurrenceCount E) s ≤
      exp ((occurrenceMean E p/(occurrenceLambda E K p/occurrenceMean E p))*
        (exp (-(occurrenceLambda E K p/occurrenceMean E p)*s)-1)) := by
  have hLa : 0 < occurrenceLambda E K p := hm.trans_le (occurrence_lambda_ge_mean E K hself p)
  apply finite_laplace_of_slope _ _ _ _ (div_pos hLa hm) _ s hs
  intro t ht
  have hh := bernoulli_janson_slope D E hE K hK p hm t ht
  convert hh using 1 <;> congr 2 <;> ring

/-- Full Janson lower tail with ordered dependencies, including the diagonal.
The proof is from finite product laws, Harris and finite Jensen; no
probabilistic inequality is supplied as an additional assumption. -/
theorem bernoulli_janson_full_lower_tail (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (K : I → Finset I)
    (hK : ∀ i j, j∉K i → Disjoint (E i) (E j)) (hself : ∀ i, i∈K i)
    (p : unitInterval) (hm : 0 < occurrenceMean E p)
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    (subsetBernoulli D p).prob (fun S => occurrenceCount E S ≤ tau*occurrenceMean E p) ≤
      exp (-fullJansonPhi tau*(occurrenceMean E p)^2/occurrenceLambda E K p) := by
  have hLa : 0 < occurrenceLambda E K p := hm.trans_le (occurrence_lambda_ge_mean E K hself p)
  have hh := finite_lower_tail_of_laplace (subsetBernoulli D p) (occurrenceCount E)
    (occurrenceMean E p) (occurrenceLambda E K p/occurrenceMean E p) (div_pos hLa hm)
    (bernoulli_janson_laplace D E hE K hK hself p hm) tau ht0 ht1
  apply hh.trans_eq
  congr 1
  field_simp

end
end Cycle12
