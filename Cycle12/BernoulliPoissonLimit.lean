import Cycle12.BernoulliListSplitting

namespace Cycle12
open Polynomial Finset Filter
open scoped Topology
noncomputable section

theorem bernoulli_list_product_function (l : List ℝ) (f : ℝ → ℝ) :
    (∏ i : Fin l.length, f (l.get i))=(l.map f).prod := by
  rw [← List.prod_ofFn]
  have hh := congrArg (fun xs : List ℝ => (xs.map f).prod) (List.ofFn_get l)
  simpa only [List.map_ofFn,Function.comp_def] using hh

theorem bernoulli_list_sum_function (l : List ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin l.length, f (l.get i))=(l.map f).sum := by
  rw [← List.sum_ofFn]
  have hh := congrArg (fun xs : List ℝ => (xs.map f).sum) (List.ofFn_get l)
  simpa only [List.map_ofFn,Function.comp_def] using hh

theorem bernoulli_list_small_tail (l : List ℝ) (hl : ∀ p∈l, p<1) :
    smallTailTwo (bernoulliListPGF l)=
      (l.map (fun p => 1-p)).prod*
        (1+(l.map bernoulliOdds).sum+
          ((l.map bernoulliOdds).sum^2-(l.map (fun p => (bernoulliOdds p)^2)).sum)/2) := by
  have hp : ∀ i∈(univ : Finset (Fin l.length)), l.get i<1 := fun i _ => hl _ (List.get_mem _ _)
  obtain ⟨h₀,h₁,h₂⟩ := bernoulli_low_coefficients univ l.get hp
  rw [← bernoulli_list_finset] at h₀ h₁ h₂
  simp only [bernoulli_list_product_function,bernoulli_list_sum_function] at h₀ h₁ h₂
  rw [bernoulli_list_sum_function l (fun p => (bernoulliOdds p)^2)] at h₂
  unfold smallTailTwo
  nlinarith only [h₀,h₁,h₂]

theorem bernoulli_refine_product (n : ℕ) (l : List ℝ) :
    ((bernoulliRefine n l).map (fun p => 1-p)).prod=
      (l.map (fun p => (1-p/(n:ℝ))^n)).prod := by
  induction l with
  | nil => simp [bernoulliRefine]
  | cons p l ih => simp [bernoulli_refine_cons,ih]

theorem bernoulli_refine_odds_sum (n : ℕ) (l : List ℝ) :
    ((bernoulliRefine n l).map bernoulliOdds).sum=
      (l.map (fun p => (n:ℝ)*bernoulliOdds (p/(n:ℝ)))).sum := by
  induction l with
  | nil => simp [bernoulliRefine]
  | cons p l ih => simp [bernoulli_refine_cons,ih,nsmul_eq_mul]

theorem bernoulli_refine_odds_square_sum (n : ℕ) (l : List ℝ) :
    ((bernoulliRefine n l).map (fun p => (bernoulliOdds p)^2)).sum=
      (l.map (fun p => (n:ℝ)*(bernoulliOdds (p/(n:ℝ)))^2)).sum := by
  induction l with
  | nil => simp [bernoulliRefine]
  | cons p l ih => simp [bernoulli_refine_cons,ih,nsmul_eq_mul]

theorem tendsto_refined_odds (p : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*bernoulliOdds (p/(n:ℝ))) atTop (𝓝 p) := by
  have hz : Tendsto (fun n : ℕ => p/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => p/(1-p/(n:ℝ))) atTop (𝓝 p) := by
    simpa only [div_eq_mul_inv,sub_zero,inv_one,mul_one] using
      tendsto_const_nhds.mul ((tendsto_const_nhds.sub hz).inv₀ (by norm_num : (1:ℝ)-0≠0))
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  unfold bernoulliOdds
  rw [← mul_div_assoc,mul_div_cancel₀ p (by exact_mod_cast hn.ne')]

theorem tendsto_refined_odds_square (p : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*(bernoulliOdds (p/(n:ℝ)))^2) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => p/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ho : Tendsto (fun n : ℕ => bernoulliOdds (p/(n:ℝ))) atTop (𝓝 0) := by
    simpa only [bernoulliOdds,div_eq_mul_inv,sub_zero,zero_mul] using
      hz.mul ((tendsto_const_nhds.sub hz).inv₀ (by norm_num : (1:ℝ)-0≠0))
  simpa only [pow_two,mul_assoc,mul_zero] using (tendsto_refined_odds p).mul ho

theorem tendsto_refined_zero_product (l : List ℝ) :
    Tendsto (fun n : ℕ => (l.map (fun p => (1-p/(n:ℝ))^n)).prod)
      atTop (𝓝 (Real.exp (-l.sum))) := by
  induction l with
  | nil => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
  | cons p l ih =>
    have hh := (Real.tendsto_one_add_div_pow_exp (-p)).mul ih
    simpa only [List.map_cons,List.prod_cons,List.sum_cons,neg_add,Real.exp_add,
      neg_div,sub_eq_add_neg] using hh

theorem tendsto_refined_odds_sum (l : List ℝ) :
    Tendsto (fun n : ℕ => (l.map (fun p => (n:ℝ)*bernoulliOdds (p/(n:ℝ)))).sum)
      atTop (𝓝 l.sum) := by
  induction l with
  | nil => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  | cons p l ih => simpa only [List.map_cons,List.sum_cons] using (tendsto_refined_odds p).add ih

theorem tendsto_refined_odds_square_sum (l : List ℝ) :
    Tendsto (fun n : ℕ => (l.map (fun p => (n:ℝ)*(bernoulliOdds (p/(n:ℝ)))^2)).sum)
      atTop (𝓝 0) := by
  induction l with
  | nil => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  | cons p l ih => simpa only [List.map_cons,List.sum_cons,zero_add] using (tendsto_refined_odds_square p).add ih

/-- The first three masses of the refined finite Bernoulli product converge
to the corresponding Poisson masses. No probability limit theorem is assumed. -/
theorem tendsto_refined_small_tail (l : List ℝ) (hl : ∀ p∈l, p ≤ 1) :
    Tendsto (fun n : ℕ => smallTailTwo (bernoulliListPGF (bernoulliRefine n l)))
      atTop (𝓝 (Real.exp (-l.sum)*(1+l.sum+l.sum^2/2))) := by
  have hA := tendsto_refined_zero_product l
  have hB := tendsto_refined_odds_sum l
  have hC := tendsto_refined_odds_square_sum l
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh := hA.mul ((h1.add hB).add (((hB.pow 2).sub hC).div_const 2))
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have hstrict : ∀ p∈bernoulliRefine n l, p<1 := by
    intro p hp
    obtain ⟨q,hq,hpq⟩ := List.mem_flatMap.mp hp
    rw [(List.mem_replicate.mp hpq).2]
    have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    apply (div_lt_one hn0).mpr
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hl q hq,hn2]
  rw [bernoulli_list_small_tail _ hstrict,bernoulli_refine_product,
    bernoulli_refine_odds_sum,bernoulli_refine_odds_square_sum]

/-- The needed lower-CDF Poisson comparison, proved specifically through
degree two by finite splitting and the elementary exponential limit. -/
theorem bernoulli_small_tail_poisson (l : List ℝ)
    (hl : ∀ p∈l, 0 ≤ p ∧ p ≤ 1) (hmean : 3 ≤ l.sum) :
    smallTailTwo (bernoulliListPGF l) ≤ Real.exp (-l.sum)*(1+l.sum+l.sum^2/2) := by
  apply ge_of_tendsto (tendsto_refined_small_tail l (fun p hp => (hl p hp).2))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact bernoulli_refine_cdf_le n hn l hl hmean

end
end Cycle12
