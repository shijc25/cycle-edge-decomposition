import Cycle12.Foundations.BernoulliContainment
import Cycle12.Foundations.SubsetBernoulliTransport
import Cycle12.Foundations.FiniteCantelli

namespace Cycle12
open Finset Cycle13 MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Transport the already formalized Harris function inequality to the
finite laws used by the sampling construction. -/
theorem bernoulli_expect_eq_integral (p : unitInterval) (f : Finset V → ℝ) :
    (bernoulliSubset p).expect f=
      ∫ S : Set V, f S.toFinset ∂(setBernoulli Set.univ p) := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  have hh := (Fintype.finsetEquivSet : Finset V ≃ Set V).sum_comp
    (fun S : Set V => (setBernoulli (Set.univ:Set V) p).real {S}*f S.toFinset)
  rw [← hh]
  unfold FiniteLaw.expect
  apply sum_congr rfl
  intro S _
  rw [bernoulliSubset_mass_eq_setBernoulli]
  congr 1
  apply congrArg f
  ext v
  exact (@Set.mem_toFinset V (Fintype.finsetEquivSet S)
    (Subtype.fintype (Membership.mem (Fintype.finsetEquivSet S))) v).symm

theorem bernoulli_harris_monotone (p : unitInterval) (f g : Finset V → ℝ)
    (hf : Monotone f) (hg : Monotone g) :
    (bernoulliSubset p).expect f*(bernoulliSubset p).expect g ≤
      (bernoulliSubset p).expect (fun S => f S*g S) := by
  exact Cycle12.Independent.bernoulli_association_real p hf hg

theorem subset_bernoulli_harris_monotone (W : Finset V) (p : unitInterval)
    (f g : Finset V → ℝ) (hf : Monotone f) (hg : Monotone g) :
    (subsetBernoulli W p).expect f*(subsetBernoulli W p).expect g ≤
      (subsetBernoulli W p).expect (fun S => f S*g S) := by
  simp_rw [subsetBernoulli_expect_subtype]
  apply bernoulli_harris_monotone
  · intro A B hAB
    exact hf (map_subset_map.mpr hAB)
  · intro A B hAB
    exact hg (map_subset_map.mpr hAB)

theorem subset_bernoulli_harris_antitone (W : Finset V) (p : unitInterval)
    (f g : Finset V → ℝ) (hf : Antitone f) (hg : Antitone g) :
    (subsetBernoulli W p).expect f*(subsetBernoulli W p).expect g ≤
      (subsetBernoulli W p).expect (fun S => f S*g S) := by
  have hh := subset_bernoulli_harris_monotone W p (fun S => -f S) (fun S => -g S)
    (fun A B hAB => neg_le_neg (hf hAB)) (fun A B hAB => neg_le_neg (hg hAB))
  have hneg (h : Finset V → ℝ) : (subsetBernoulli W p).expect (fun S => -h S)=
      -(subsetBernoulli W p).expect h := by
    unfold FiniteLaw.expect
    simp only [mul_neg,sum_neg_distrib]
  simpa only [hneg,neg_mul_neg] using hh

end
end Cycle12
