import Cycle12.FixedMajorityError
import Cycle12.Foundations.GraphCopyExpectation

namespace Cycle12
open Finset SimpleGraph Cycle13
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- All auxiliary choices depend on the unlabelled marked set only. -/
def fixedMajorityLaw (G : SimpleGraph V) (T : Finset V) : FiniteLaw (V → Finset V) :=
  FiniteLaw.independent (fun v => subsetVoteLaw (neighborsIn G v T))

def fixedMajoritySide (D T A : Finset V) (xi : V → Finset V) : Finset V :=
  D.filter (fun v => if v∈T then v∈A else subsetMajority A (xi v))

theorem fixed_majority_side_subset (D T A : Finset V) (xi : V → Finset V) :
    fixedMajoritySide D T A xi⊆D := filter_subset _ _

theorem fixed_majority_side_marked (D T A : Finset V) (xi : V → Finset V)
    (hT : T⊆D) (hA : A⊆T) : fixedMajoritySide D T A xi∩T=A := by
  ext v
  by_cases hv : v∈T
  · simp [fixedMajoritySide,hv,hT hv]
  · have ha : v∉A := fun h => hv (hA h)
    simp [hv,ha]

theorem fixed_majority_marginal (G : SimpleGraph V) (T : Finset V)
    (v : V) (f : Finset V → ℝ) :
    (fixedMajorityLaw G T).expect (fun xi => f (xi v))=
      (subsetVoteLaw (neighborsIn G v T)).expect f :=
  FiniteLaw.independent_expect_eval _ _ _

theorem fixed_majority_error_marginal (G : SimpleGraph V) (D T A : Finset V)
    {v : V} (hvD : v∈D) :
    (fixedMajorityLaw G T).prob
        (fun xi => ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi))=
      (subsetVoteLaw (neighborsIn G v T)).prob (subsetCopiedError T A v) := by
  have he (xi : V → Finset V) :
      ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi) ↔ subsetCopiedError T A v (xi v) := by
    by_cases hv : v∈T <;> simp [fixedMajoritySide,subsetCopiedError,hv,hvD]
  unfold FiniteLaw.prob
  simp_rw [he]
  convert fixed_majority_marginal G T v
    (fun S => if subsetCopiedError T A v S then (1:ℝ) else 0) using 1
    <;> congr 1 <;> funext xi <;> split_ifs <;> rfl

/-- The actual graph classifier inherits the fixed-sample mixture bound.
Its marked vertices are always correct, and the zero-vote default is charged
only to vertices originally in A. -/
theorem fixed_majority_graph_error_mean (G : SimpleGraph V) (D U A : Finset V)
    (hU : U.Nonempty) {v : V} (hvD : v∈D)
    (hdeg : 3 ≤ (neighborsIn G v U).card) {k : ℕ} (hk : k ≤ U.card) :
    (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).prob
        (fun xi => ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi))) ≤
      lowPositiveVoteProbability U (neighborsIn G v U) k*
        (((if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card:ℝ)/
          (neighborsIn G v U).card)+
      (1-lowPositiveVoteProbability U (neighborsIn G v U) k)*
        majorityCorrection (neighborsIn G v U).card*
        majorityPolynomial
          (((if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card:ℝ)/
            (neighborsIn G v U).card)+
      if v∈A then Real.exp (-(k:ℝ)*(neighborsIn G v U).card/U.card) else 0 := by
  simp_rw [fixed_majority_error_marginal G D _ A hvD]
  have he : (fixedSizeLaw U k).expect
      (fun T => (subsetVoteLaw (neighborsIn G v T)).prob (subsetCopiedError T A v))=
      (fixedSizeLaw U k).expect
        (fun T => (subsetVoteLaw (T∩neighborsIn G v U)).prob (subsetCopiedError T A v)) := by
    apply finite_expect_congr_support
    intro T hT
    rw [neighborsIn_subset_inter G U T (fixed_size_support U T hk hT).1 v,
      inter_comm (neighborsIn G v U) T]
  rw [he]
  exact fixed_subset_copied_error_mean U (neighborsIn G v U) A v hU
    (filter_subset _ _) hdeg hk

end
end Cycle12
