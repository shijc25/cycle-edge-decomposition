import Cycle12.BernoulliSplitting

namespace Cycle12
open Polynomial Finset
noncomputable section

def bernoulliListPGF (l : List ℝ) : Polynomial ℝ :=
  (l.map realBernoulliPolynomial).prod

@[simp] theorem bernoulli_list_nil : bernoulliListPGF []=1 := rfl

@[simp] theorem bernoulli_list_cons (p : ℝ) (l : List ℝ) :
    bernoulliListPGF (p::l)=realBernoulliPolynomial p*bernoulliListPGF l := rfl

@[simp] theorem bernoulli_list_append (l r : List ℝ) :
    bernoulliListPGF (l++r)=bernoulliListPGF l*bernoulliListPGF r := by
  simp [bernoulliListPGF]

theorem bernoulli_list_finset (l : List ℝ) :
    bernoulliListPGF l=bernoulliPGF univ l.get := by
  unfold bernoulliListPGF bernoulliPGF
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

theorem bernoulli_list_sum (l : List ℝ) : (∑ i : Fin l.length, l.get i)=l.sum := by
  rw [← List.sum_ofFn, List.ofFn_get]

theorem bernoulli_list_coeff_two_ge_one (l : List ℝ)
    (hp : ∀ p∈l, 0 ≤ p ∧ p ≤ 1) (hmean : 2 ≤ l.sum) :
    (bernoulliListPGF l).coeff 1 ≤ (bernoulliListPGF l).coeff 2 := by
  rw [bernoulli_list_finset]
  apply bernoulli_coeff_two_ge_one
  · intro i _
    exact hp _ (List.get_mem _ _)
  · simpa only [bernoulli_list_sum] using hmean

theorem bernoulli_split_general_identity (a b : ℝ) (Q : Polynomial ℝ) :
    smallTailTwo ((realBernoulliPolynomial a*realBernoulliPolynomial b)*Q)-
      smallTailTwo (realBernoulliPolynomial (a+b)*Q)=a*b*(Q.coeff 2-Q.coeff 1) := by
  simp only [smallTailTwo,mul_assoc,bernoulli_step_coeff_zero,
    bernoulli_step_coeff_succ _ _ 0,bernoulli_step_coeff_succ _ _ 1]
  ring

theorem bernoulli_split_general_le (l : List ℝ)
    (hl : ∀ p∈l, 0 ≤ p ∧ p ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) (hmean : 3 ≤ a+b+l.sum) :
    smallTailTwo (realBernoulliPolynomial (a+b)*bernoulliListPGF l) ≤
      smallTailTwo ((realBernoulliPolynomial a*realBernoulliPolynomial b)*bernoulliListPGF l) := by
  apply sub_nonneg.mp
  rw [bernoulli_split_general_identity]
  exact mul_nonneg (mul_nonneg ha hb)
    (sub_nonneg.mpr (bernoulli_list_coeff_two_ge_one l hl (by linarith only [hab,hmean])))

/-- Replacing a parameter by any number of equal independent parameters
increases the CDF through two, provided the full mean is at least three. -/
theorem bernoulli_replicate_cdf_le (n : ℕ) (a : ℝ) (l : List ℝ)
    (ha : 0 ≤ a) (hl : ∀ p∈l, 0 ≤ p ∧ p ≤ 1)
    (hcap : (n:ℝ)*a ≤ 1) (hmean : 3 ≤ (n:ℝ)*a+l.sum) :
    smallTailTwo (realBernoulliPolynomial ((n:ℝ)*a)*bernoulliListPGF l) ≤
      smallTailTwo (bernoulliListPGF (List.replicate n a++l)) := by
  induction n generalizing l with
  | zero => simp [realBernoulliPolynomial]
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ)*a := mul_nonneg (Nat.cast_nonneg _) ha
    have ha1 : a ≤ 1 := by
      push_cast at hcap
      nlinarith only [hcap,hn]
    have hcap' : a+(n:ℝ)*a ≤ 1 := by push_cast at hcap; linarith only [hcap]
    have hmean' : 3 ≤ a+(n:ℝ)*a+l.sum := by push_cast at hmean; linarith only [hmean]
    have hstep := bernoulli_split_general_le l hl ha hn hcap' hmean'
    have hrest : ∀ p∈a::l, 0 ≤ p ∧ p ≤ 1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨ha,ha1⟩
      · exact hl p hp
    have hnext := ih (a::l) hrest (by linarith only [hcap',ha])
      (by simpa only [List.sum_cons,add_left_comm,add_assoc] using hmean')
    have heq : ((n+1:ℕ):ℝ)*a=a+(n:ℝ)*a := by push_cast; ring
    rw [heq]
    refine hstep.trans ?_
    simpa only [List.replicate_succ,List.cons_append,bernoulli_list_cons,
      bernoulli_list_append,mul_assoc,mul_left_comm,mul_comm] using hnext

def bernoulliRefine (n : ℕ) (l : List ℝ) : List ℝ :=
  l.flatMap (fun p => List.replicate n (p/(n:ℝ)))

@[simp] theorem bernoulli_refine_cons (n : ℕ) (p : ℝ) (l : List ℝ) :
    bernoulliRefine n (p::l)=List.replicate n (p/(n:ℝ))++bernoulliRefine n l := rfl

theorem bernoulli_refine_sum (n : ℕ) (hn : 0<n) (l : List ℝ) :
    (bernoulliRefine n l).sum=l.sum := by
  induction l with
  | nil => simp [bernoulliRefine]
  | cons p l ih =>
    rw [bernoulli_refine_cons,List.sum_append,List.sum_replicate,ih,List.sum_cons]
    rw [nsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]

theorem bernoulli_refine_bounds (n : ℕ) (hn : 0<n) (l : List ℝ)
    (hl : ∀ p∈l, 0 ≤ p ∧ p ≤ 1) :
    ∀ p∈bernoulliRefine n l, 0 ≤ p ∧ p ≤ 1 := by
  intro p hp
  obtain ⟨q,hq,hpq⟩ := List.mem_flatMap.mp hp
  have hpq' : p=q/(n:ℝ) := (List.mem_replicate.mp hpq).2
  rw [hpq']
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨div_nonneg (hl q hq).1 hn0.le,(div_le_one hn0).mpr ((hl q hq).2.trans hn1)⟩

theorem bernoulli_refine_cdf_le_aux (n : ℕ) (hn : 0<n) (l r : List ℝ)
    (hl : ∀ p∈l, 0 ≤ p ∧ p ≤ 1) (hr : ∀ p∈r, 0 ≤ p ∧ p ≤ 1)
    (hmean : 3 ≤ l.sum+r.sum) :
    smallTailTwo (bernoulliListPGF (l++r)) ≤
      smallTailTwo (bernoulliListPGF (bernoulliRefine n l++r)) := by
  induction l generalizing r with
  | nil => simp [bernoulliRefine]
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have hl' : ∀ q∈l, 0 ≤ q ∧ q ≤ 1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hn0 : (0:ℝ)<n := by exact_mod_cast hn
    have hpa : (n:ℝ)*(p/(n:ℝ))=p := mul_div_cancel₀ p hn0.ne'
    have hr' : ∀ q∈l++r, 0 ≤ q ∧ q ≤ 1 := by
      intro q hq
      exact (List.mem_append.mp hq).elim (hl' q) (hr q)
    have hstep := bernoulli_replicate_cdf_le n (p/(n:ℝ)) (l++r)
      (div_nonneg hp.1 hn0.le) hr' (by rw [hpa]; exact hp.2)
      (by simpa only [hpa,List.sum_cons,List.sum_append,add_assoc] using hmean)
    have hrep : ∀ q∈List.replicate n (p/(n:ℝ))++r, 0 ≤ q ∧ q ≤ 1 := by
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · have hq' := (List.mem_replicate.mp hq).2
        rw [hq']
        refine ⟨div_nonneg hp.1 hn0.le,(div_le_one hn0).mpr ?_⟩
        exact hp.2.trans (by exact_mod_cast hn)
      · exact hr q hq
    have hnext := ih (List.replicate n (p/(n:ℝ))++r) hl' hrep (by
      simp only [List.sum_append,List.sum_replicate,nsmul_eq_mul,hpa]
      simpa only [List.sum_cons,add_left_comm,add_assoc] using hmean)
    rw [hpa] at hstep
    change smallTailTwo (realBernoulliPolynomial p*bernoulliListPGF (l++r)) ≤ _
    refine hstep.trans ?_
    simpa only [bernoulli_refine_cons,bernoulli_list_append,mul_assoc,mul_left_comm,mul_comm] using hnext

theorem bernoulli_refine_cdf_le (n : ℕ) (hn : 0<n) (l : List ℝ)
    (hl : ∀ p∈l, 0 ≤ p ∧ p ≤ 1) (hmean : 3 ≤ l.sum) :
    smallTailTwo (bernoulliListPGF l) ≤ smallTailTwo (bernoulliListPGF (bernoulliRefine n l)) := by
  simpa only [List.append_nil] using bernoulli_refine_cdf_le_aux n hn l [] hl
    (by simp) (by simpa using hmean)

end
end Cycle12
