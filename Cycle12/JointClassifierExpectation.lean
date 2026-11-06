import Cycle12.JointCutWitness
import Cycle12.Foundations.GraphCopyWitness

namespace Cycle12
open SimpleGraph Finset Cycle13 Real
open scoped symmDiff
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem joint_cut_cost_eq_sum (G : SimpleGraph V) (U A B : Finset V)
    (hA : A⊆U) (hB : B⊆U) (t : ℝ) :
    jointCutError G U A B+t*(A ∆ B).card =
      ∑ v∈U, (((neighborsIn G v (if v∈A then A else U\A)).card:ℝ)+t)*
        (if v∈A ∆ B then 1 else 0) := by
  have hs : A ∆ B⊆U := by
    intro v hv
    rcases mem_symmDiff.mp hv with hv | hv
    · exact hA hv.1
    · exact hB hv.1
  have hf : U.filter (fun v => v∈A ∆ B)=A ∆ B := by
    ext v
    simp only [mem_filter]
    exact ⟨And.right,fun h => ⟨hs h,h⟩⟩
  simp_rw [mul_ite,mul_one,mul_zero]
  rw [← sum_filter,hf,sum_add_distrib]
  simp only [jointCutError,sum_const,nsmul_eq_mul]
  ring

theorem joint_classifier_expectation {Ω : Type} [Fintype Ω]
    (mu : FiniteLaw Ω) (G : SimpleGraph V) (U A : Finset V) (B : Ω → Finset V)
    (hA : A⊆U) (hB : ∀ w, B w⊆U) (t : ℝ) :
    mu.expect (fun w => jointCutError G U A (B w)+t*(A ∆ B w).card)=
      ∑ v∈U, (((neighborsIn G v (if v∈A then A else U\A)).card:ℝ)+t)*
        mu.prob (fun w => v∈A ∆ B w) := by
  simp_rw [joint_cut_cost_eq_sum G U A _ hA (hB _) t,
    FiniteLaw.expect_finset_sum,FiniteLaw.expect_const_mul]
  apply sum_congr rfl
  intro v hv
  congr 1
  unfold FiniteLaw.prob
  congr 1
  funext w
  by_cases h : v∈A ∆ B w <;> simp [h]

/-- Graph-level expectation accounting for any classifier. The probability
experiment can be dependent; only its actual per-vertex error bounds enter. -/
theorem joint_classifier_expectation_bound {Ω : Type} [Fintype Ω]
    (mu : FiniteLaw Ω) (G : SimpleGraph V) (U A : Finset V) (B : Ω → Finset V)
    (hA : A⊆U) (hB : ∀ w, B w⊆U) {t K tail : ℝ}
    (hpoint : ∀ v∈U,
      (((neighborsIn G v (if v∈A then A else U\A)).card:ℝ)+t)*
          mu.prob (fun w => v∈A ∆ B w) ≤
        K*((neighborsIn G v (if v∈A then U\A else A)).card:ℝ)+
          if v∈A then tail else 0) :
    mu.expect (fun w => jointCutError G U A (B w)+t*(A ∆ B w).card) ≤
      2*K*(G.interedges A (U\A)).card+tail*A.card := by
  rw [joint_classifier_expectation mu G U A B hA hB t]
  apply (sum_le_sum hpoint).trans_eq
  rw [sum_add_distrib,← mul_sum,← sum_filter]
  have hf : U.filter (fun v => v∈A)=A := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr hA]
  rw [hf,sum_const,nsmul_eq_mul]
  have hn₁ (v : V) : neighborsIn G v U\A=neighborsIn G v (U\A) := by
    ext w
    simp [neighborsIn,and_assoc,and_left_comm,and_comm]
  have hn₂ (v : V) : neighborsIn G v U∩A=neighborsIn G v A := by
    ext w
    simp only [neighborsIn,mem_inter,mem_filter]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hA h.1,h.2⟩,h.1⟩⟩
  have hsum := sum_sample_cross_neighbors G U A hA
  simp_rw [hn₁,hn₂] at hsum
  have he (v : V) : (if v∈A then neighborsIn G v (U\A) else neighborsIn G v A)=
      neighborsIn G v (if v∈A then U\A else A) := by split_ifs <;> rfl
  simp_rw [he] at hsum
  rw [hsum]
  ring

/-- The additional vertex charge is included before applying the
exponential degree tail, avoiding separate worst-case error budgets. -/
theorem shifted_degree_exp_antitone {p delta d t : ℝ}
    (hp : 0 ≤ p) (hmark : 1 ≤ p*(delta+t)) (hd : delta ≤ d) :
    (d+t)*exp (-p*d) ≤ (delta+t)*exp (-p*delta) := by
  have hh := degree_exp_antitone hp hmark (show delta+t ≤ d+t by linarith only [hd])
  have hm := mul_le_mul_of_nonneg_left hh (exp_pos (p*t)).le
  have he (x : ℝ) : exp (p*t)*((x+t)*exp (-p*(x+t)))=(x+t)*exp (-p*x) := by
    rw [mul_left_comm,← exp_add]
    congr 2
    ring
  simpa only [he] using hm

end
end Cycle12
