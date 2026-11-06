import Cycle12.FixedMajorityClassifier
import Cycle12.FixedMarkedTwoSides

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual majority auxiliary law and classifier satisfy the two-color,
all-label counting bound in the original sample/mark experiment. -/
theorem fixed_majority_two_colors_counting_failure (G : SimpleGraph V) (D : Finset V)
    {N t : ℕ} (hN : N ≤ D.card) (ht : t ≤ N) (htD : t<D.card)
    {theta lam err : ℝ} (htheta : 0<theta)
    (hbase : 1-((N-t:ℕ):ℝ)/(D.card-t)+
      ((N-t:ℕ):ℝ)/(D.card-t)*exp theta ≤ exp lam) :
    (fixedMarkedExperiment D N t (fixedMajorityLaw G)).prob (fun x => ∃ A⊆x.2.1,
        (lam/theta)*(fixedMajoritySide D x.2.1 A x.2.2).card+err <
          ((x.1∩fixedMajoritySide D x.2.1 A x.2.2).card:ℝ) ∨
        (lam/theta)*(D\fixedMajoritySide D x.2.1 A x.2.2).card+err <
          ((x.1∩(D\fixedMajoritySide D x.2.1 A x.2.2)).card:ℝ)) ≤
      2*exp (-theta*err)*(1+exp (theta-lam))^t := by
  apply fixed_marked_two_sides_counting_failure D hN ht htD (fixedMajorityLaw G)
    (fixedMajoritySide D) _ _ htheta hbase
  · intro T _ _ A _ xi
    exact fixed_majority_side_subset D T A xi
  · intro T hT _ A hA xi
    exact fixed_majority_side_marked D T A xi hT hA

end
end Cycle12
