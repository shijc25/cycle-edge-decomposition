import Cycle12.BernoulliOccurrence
import Cycle12.FiniteExpJensen

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def occurrenceMean (E : I → Finset V) (p : unitInterval) : ℝ :=
  ∑ i, (p:ℝ)^(E i).card

def occurrenceLambda (E : I → Finset V) (K : I → Finset I) (p : unitInterval) : ℝ :=
  ∑ i, ∑ j ∈ K i, (p:ℝ)^(E i∪E j).card

theorem occurrence_mean_eq_expect (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (p : unitInterval) :
    (subsetBernoulli D p).expect (occurrenceCount E)=occurrenceMean E p := by
  unfold occurrenceCount
  rw [FiniteLaw.expect_sum]
  apply sum_congr rfl
  intro i _
  exact subset_bernoulli_contains_expect D (E i) (hE i) p

theorem occurrence_lambda_ge_mean (E : I → Finset V) (K : I → Finset I)
    (hself : ∀ i, i∈K i) (p : unitInterval) :
    occurrenceMean E p ≤ occurrenceLambda E K p := by
  apply sum_le_sum
  intro i _
  have hh := single_le_sum (s:=K i) (f:=fun j => (p:ℝ)^(E i∪E j).card)
    (fun j _ => pow_nonneg p.2.1 _) (hself i)
  simpa only [union_self] using hh

/-- The sharp logarithmic-derivative estimate, derived from actual events
in a Bernoulli sample. K may be any valid dependency neighborhoods. -/
theorem bernoulli_janson_slope (D : Finset V) (E : I → Finset V)
    (hE : ∀ i, E i⊆D) (K : I → Finset I)
    (hK : ∀ i j, j∉K i → Disjoint (E i) (E j)) (p : unitInterval)
    (hm : 0 < occurrenceMean E p) (s : ℝ) (hs : 0 ≤ s) :
    occurrenceMean E p*exp (-s*occurrenceLambda E K p/occurrenceMean E p)*
        finiteLaplace (subsetBernoulli D p) (occurrenceCount E) s ≤
      (subsetBernoulli D p).expect (fun S => occurrenceCount E S*exp (-s*occurrenceCount E S)) := by
  let b : I → ℝ := fun i => (subsetBernoulli (D\E i) p).expect
    (fun R => occurrencePart E (K i) (E i∪R))
  have hb : ∑ i, (p:ℝ)^(E i).card*b i=occurrenceLambda E K p := by
    apply sum_congr rfl
    intro i _
    exact occurrence_conditional_mean D E hE (K i) i p
  have hi (i : I) := bernoulli_indicator_laplace_lower D (E i) (hE i) p
    (occurrenceCount E) (occurrencePart E (K i)) (occurrencePart E (K i)ᶜ)
    (occurrence_part_partition E (K i)) (occurrence_part_monotone E (K i))
    (occurrence_part_monotone E (K i)ᶜ) (occurrence_part_nonneg E (K i))
    (occurrence_part_ignore E (K i)ᶜ (E i) (fun j hj => hK i j (mem_compl.mp hj))) s hs
  have hj := finite_weighted_exp_jensen (fun i => (p:ℝ)^(E i).card) (fun i => -s*b i)
    (fun i => pow_nonneg p.2.1 _) hm
  have hx : (∑ i, (p:ℝ)^(E i).card*(-s*b i)) = -s*occurrenceLambda E K p := by
    rw [← hb,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [hx] at hj
  calc
    _ ≤ (∑ i, (p:ℝ)^(E i).card*exp (-s*b i))*
        finiteLaplace (subsetBernoulli D p) (occurrenceCount E) s :=
      mul_le_mul_of_nonneg_right hj (finite_laplace_nonneg _ _ _)
    _ = ∑ i, (p:ℝ)^(E i).card*exp (-s*b i)*
        finiteLaplace (subsetBernoulli D p) (occurrenceCount E) s := by rw [sum_mul]
    _ ≤ ∑ i, (subsetBernoulli D p).expect
        (fun S => containsIndicator (E i) S*exp (-s*occurrenceCount E S)) :=
      sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← FiniteLaw.expect_sum]
      apply congrArg (FiniteLaw.expect _)
      funext S
      exact (sum_mul _ _ _).symm

end
end Cycle12
