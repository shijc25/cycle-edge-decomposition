import Cycle12.Foundations.FiniteBernoulliMeasure
import Cycle12.Independent.Bernoulli

namespace Cycle13
open Finset MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bernoulliSubset_contains (p : unitInterval) (D : Finset V) :
    (bernoulliSubset p).prob (fun S => D⊆S)=(p:ℝ)^D.card := by
  have he : (fun S : Finset V => D⊆S)=(fun S : Finset V => (D:Set V)⊆(S:Set V)) := rfl
  rw [he,bernoulliSubset_prob_eq_setBernoulli p (fun S => (D:Set V)⊆S),
    measureReal_def,Cycle12.Independent.setBernoulli_contains,ENNReal.toReal_pow,
    ENNReal.coe_toReal,unitInterval.coe_toNNReal]

def containsIndicator (D S : Finset V) : ℝ := if D⊆S then 1 else 0

theorem containsIndicator_mul (A B S : Finset V) :
    containsIndicator A S*containsIndicator B S=containsIndicator (A∪B) S := by
  simp only [containsIndicator,union_subset_iff]
  by_cases ha : A⊆S <;> by_cases hb : B⊆S <;> simp [ha,hb]

theorem bernoulliSubset_contains_expect (p : unitInterval) (D : Finset V) :
    (bernoulliSubset p).expect (containsIndicator D)=(p:ℝ)^D.card := by
  rw [← bernoulliSubset_contains p D,FiniteLaw.prob]
  congr 1
  funext S
  by_cases h : D⊆S <;> simp [containsIndicator,h]

theorem bernoulliSubset_contains_product (p : unitInterval) (A B : Finset V) :
    (bernoulliSubset p).expect (fun S => containsIndicator A S*containsIndicator B S)=
      (p:ℝ)^(A∪B).card := by
  simp_rw [containsIndicator_mul]
  exact bernoulliSubset_contains_expect p _

end
end Cycle13
