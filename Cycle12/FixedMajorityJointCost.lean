import Cycle12.FixedMajorityVertexCharge

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def fixedMajorityExperiment (G : SimpleGraph V) (U : Finset V) (k : ℕ) :
    FiniteLaw (Finset V×(V → Finset V)) :=
  (fixedSizeLaw U k).joint (fixedMajorityLaw G)

def fixedMajorityInSample (D U A : Finset V) (x : Finset V×(V → Finset V)) : Finset V :=
  U∩fixedMajoritySide D x.1 (A∩x.1) x.2

theorem fixed_majority_joint_error_probability (G : SimpleGraph V) (D U A : Finset V)
    (k : ℕ) {v : V} (hv : v∈U) :
    (fixedMajorityExperiment G U k).prob (fun x => v∈A ∆ fixedMajorityInSample D U A x)=
      (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).prob
        (fun xi => ¬(v∈A ↔ v∈fixedMajoritySide D T (A∩T) xi))) := by
  have he (x : Finset V×(V → Finset V)) :
      v∈A ∆ fixedMajorityInSample D U A x ↔
        ¬(v∈A ↔ v∈fixedMajoritySide D x.1 (A∩x.1) x.2) := by
    simp only [fixedMajorityInSample,mem_symmDiff,mem_inter,hv,true_and]
    tauto
  unfold fixedMajorityExperiment FiniteLaw.prob
  simp_rw [he]
  rw [FiniteLaw.expect_joint]
  congr 1
  funext T
  congr 1
  funext xi
  split_ifs <;> rfl

theorem fixed_cross_neighbor_set (G : SimpleGraph V) (U A : Finset V) (hA : A⊆U) (v : V) :
    (if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A)=
      neighborsIn G v (if v∈A then U\A else A) := by
  by_cases hv : v∈A
  · simp only [hv,ite_true]
    ext w
    simp [neighborsIn,and_assoc,and_left_comm,and_comm]
  · simp only [hv,ite_false]
    ext w
    simp only [neighborsIn,mem_inter,mem_filter]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hA h.1,h.2⟩,h.1⟩⟩

theorem same_degree_eq_total_sub_cross (G : SimpleGraph V) (U A : Finset V)
    (hA : A⊆U) (v : V) :
    ((neighborsIn G v (if v∈A then A else U\A)).card:ℝ)=
      ((neighborsIn G v U).card:ℝ)-(neighborsIn G v (if v∈A then U\A else A)).card := by
  have hh : ((neighborsIn G v U).card:ℝ)=
      (neighborsIn G v A).card+(neighborsIn G v (U\A)).card := by
    exact_mod_cast neighborsIn_partition_card G v A U hA
  by_cases hv : v∈A <;> simp only [hv,ite_true,ite_false] <;> linarith only [hh]

/-- Complete joint-cost expectation for the actual fixed-marking majority
classifier. No independence of vertex error events is used. -/
theorem fixed_majority_joint_cost_mean (G : SimpleGraph V) (D U A : Finset V)
    (hUD : U⊆D) (hU : U.Nonempty) (hA : A⊆U) {k : ℕ} (hk : k ≤ U.card)
    {z dm tau lambda K : ℝ} (hz : 0<z) (hdm : 0<dm) (htau : 0 ≤ tau)
    (hdelta : 2<dm*z) (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hlambda : 3 ≤ lambda) (hmean : lambda ≤ ((k:ℝ)/U.card)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K) :
    (fixedMajorityExperiment G U k).expect (fun x =>
      jointCutError G U A (fixedMajorityInSample D U A x)+
        tau*z*(A ∆ fixedMajorityInSample D U A x).card) ≤
      2*K*(G.interedges A (U\A)).card+
        (dm*z+tau*z)*exp (-((k:ℝ)/U.card)*(dm*z))*A.card := by
  apply joint_classifier_expectation_bound _ G U A (fixedMajorityInSample D U A) hA
    (fun _ => inter_subset_left)
  intro v hv
  have hh := fixed_majority_vertex_charge G D U A hU (hUD hv) hk hz hdm htau hdelta
    (hdeg v hv) hlambda hmean hK hpure hmixed
  rw [fixed_cross_neighbor_set G U A hA v] at hh
  rw [same_degree_eq_total_sub_cross G U A hA v,
    fixed_majority_joint_error_probability G D U A k hv]
  exact hh

end
end Cycle12
