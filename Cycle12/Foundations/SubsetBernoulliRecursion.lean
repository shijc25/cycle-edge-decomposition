import Cycle12.Foundations.MarkedSamplingCoupling

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_mass_insert_ground (W S : Finset V) (v : V) (hv : v∉W)
    (hS : S⊆W) (p : unitInterval) :
    (subsetBernoulli (insert v W) p).mass S=(1-(p:ℝ))*(subsetBernoulli W p).mass S := by
  rw [subsetBernoulli_mass _ _ _ (hS.trans (subset_insert _ _)),subsetBernoulli_mass _ _ _ hS,
    card_insert_of_notMem hv]
  have hc : W.card+1-S.card=(W.card-S.card)+1 := by have hh := card_le_card hS; omega
  rw [hc,pow_succ]
  ring

theorem subsetBernoulli_mass_insert_both (W S : Finset V) (v : V) (hv : v∉W)
    (hS : S⊆W) (p : unitInterval) :
    (subsetBernoulli (insert v W) p).mass (insert v S)=(p:ℝ)*(subsetBernoulli W p).mass S := by
  have hvS : v∉S := fun h => hv (hS h)
  rw [subsetBernoulli_mass _ _ _ (insert_subset_insert v hS),subsetBernoulli_mass _ _ _ hS,
    card_insert_of_notMem hv,card_insert_of_notMem hvS]
  have hc : W.card+1-(S.card+1)=W.card-S.card := by omega
  rw [hc,pow_succ]
  ring

theorem subsetBernoulli_expect_insert (W : Finset V) (v : V) (hv : v∉W)
    (p : unitInterval) (f : Finset V→ℝ) :
    (subsetBernoulli (insert v W) p).expect f=
      (1-(p:ℝ))*(subsetBernoulli W p).expect f+
        (p:ℝ)*(subsetBernoulli W p).expect (fun S => f (insert v S)) := by
  rw [subsetBernoulli_expect,Finset.sum_powerset_insert hv]
  rw [subsetBernoulli_expect,subsetBernoulli_expect,mul_sum,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro S hS
    rw [subsetBernoulli_mass_insert_ground W S v hv (mem_powerset.mp hS) p]
    ring
  · apply sum_congr rfl
    intro S hS
    rw [subsetBernoulli_mass_insert_both W S v hv (mem_powerset.mp hS) p]
    ring

theorem subsetBernoulli_expect_empty (p : unitInterval) (f : Finset V→ℝ) :
    (subsetBernoulli ∅ p).expect f=f ∅ := by
  rw [subsetBernoulli_expect]
  simp [subsetBernoulli]

end
end Cycle13
