import Cycle12.Foundations.MarkedSamplingCoupling
import Cycle12.Foundations.FiniteBernoulliMeasure

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_expect_subtype (W : Finset V) (p : unitInterval)
    (f : Finset V → ℝ) :
    (subsetBernoulli W p).expect f=(bernoulliSubset (V:=W) p).expect
      (fun S => f (S.map (Function.Embedding.subtype (·∈W)))) := by
  rw [subsetBernoulli_expect,FiniteLaw.expect]
  symm
  apply sum_bij (fun S _ => S.map (Function.Embedding.subtype (·∈W)))
  · intro S _
    exact mem_powerset.mpr (fun x hx => S.property_of_mem_map_subtype hx)
  · intro S _ T _ he
    exact Finset.map_injective _ he
  · intro S hS
    refine ⟨S.subtype (·∈W),mem_univ _,?_⟩
    exact subtype_map_of_mem (fun x hx => mem_powerset.mp hS hx)
  · intro S _
    rw [subsetBernoulli_mass _ _ _ (fun x hx => S.property_of_mem_map_subtype hx)]
    simp only [bernoulliSubset,card_map,Fintype.card_coe]

theorem subsetBernoulli_prob_subtype (W : Finset V) (p : unitInterval)
    (E : Finset V → Prop) :
    (subsetBernoulli W p).prob E=(bernoulliSubset (V:=W) p).prob
      (fun S => E (S.map (Function.Embedding.subtype (·∈W)))) :=
  subsetBernoulli_expect_subtype W p _

end
end Cycle13
