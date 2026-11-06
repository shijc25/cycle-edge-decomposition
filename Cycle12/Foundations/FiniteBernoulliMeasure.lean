import Cycle12.Foundations.MarkedSamplingAtoms

/-! Equality of all finite events with mathlib's Bernoulli-set measure,
not merely equality of atom formulas. -/
namespace Cycle13
open Finset MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_mass_eq_setBernoulli (W S : Finset V) (p : unitInterval) :
    (subsetBernoulli W p).mass S=(setBernoulli (W:Set V) p).real {(S:Set V)} := by
  by_cases hs : S⊆W
  · rw [subsetBernoulli_mass _ _ _ hs,setBernoulli_real_singleton p
      (show (S:Set V)⊆(W:Set V) from hs) (Set.toFinite _)]
    rw [Set.ncard_sdiff' (show (S:Set V)⊆(W:Set V) from hs) (Set.toFinite _)]
    simp only [Set.ncard_coe_finset]
  · rw [subsetBernoulli_mass_not_subset _ _ _ hs,measureReal_def,
      setBernoulli_singleton_of_not_subset p
        (show ¬(S:Set V)⊆(W:Set V) from hs),ENNReal.toReal_zero]

theorem finiteLaw_prob_eq_measure (μ : FiniteLaw (Finset V))
    (P : Measure (Set V)) [IsProbabilityMeasure P]
    (hmass : ∀ S : Finset V, μ.mass S=P.real {(S:Set V)}) (E : Set V → Prop) :
    μ.prob (fun S => E (S:Set V))=P.real {S | E S} := by
  unfold FiniteLaw.prob FiniteLaw.expect
  simp_rw [hmass]
  have he := (Fintype.finsetEquivSet : Finset V ≃ Set V).sum_comp
    (fun S : Set V => P.real {S}*(if E S then 1 else 0))
  change (∑ S : Finset V, P.real {(Fintype.finsetEquivSet S : Set V)}*
    (if E (Fintype.finsetEquivSet S) then 1 else 0))=_
  rw [he]
  simp_rw [mul_ite,mul_one,mul_zero]
  rw [← sum_filter,MeasureTheory.sum_measureReal_singleton]
  congr 1
  ext S
  simp

theorem subsetBernoulli_prob_eq_setBernoulli (W : Finset V) (p : unitInterval)
    (E : Set V → Prop) :
    (subsetBernoulli W p).prob (fun S => E (S:Set V))=
      (setBernoulli (W:Set V) p).real {S | E S} :=
  finiteLaw_prob_eq_measure _ _ (fun S => subsetBernoulli_mass_eq_setBernoulli W S p) E

theorem bernoulliSubset_prob_eq_setBernoulli (p : unitInterval) (E : Set V → Prop) :
    (bernoulliSubset (V:=V) p).prob (fun S => E (S:Set V))=
      (setBernoulli (Set.univ:Set V) p).real {S | E S} :=
  finiteLaw_prob_eq_measure _ _ (bernoulliSubset_mass_eq_setBernoulli p) E

end
end Cycle13
