import Cycle12.FixedSampleComplement
import Cycle12.Foundations.SamplingGeometry

namespace Cycle12
open Finset Cycle13 Real SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_sample_count_upper (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {theta threshold : ℝ} (htheta : 0<theta) :
    (fixedSizeLaw D k).prob (fun T => threshold < ((T∩B).card:ℝ)) ≤
      exp (-theta*threshold+((k:ℝ)/D.card)*(exp theta-1)*B.card) := by
  have hm := (fixedSizeLaw D k).exp_markov (fun T => ((T∩B).card:ℝ)) theta threshold htheta
  have he := mul_le_mul_of_nonneg_left (fixed_sample_count_mgf_exponential D B hD hB hk theta)
    (exp_pos (-theta*threshold)).le
  apply hm.trans
  simpa only [← exp_add] using he

theorem fixed_sample_count_lower (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {theta threshold : ℝ} (htheta : 0 ≤ theta) :
    (fixedSizeLaw D k).prob (fun T => ((T∩B).card:ℝ) ≤ threshold) ≤
      exp (theta*threshold+((k:ℝ)/D.card)*(exp (-theta)-1)*B.card) := by
  have hm := (fixedSizeLaw D k).exp_markov_le (fun T => -((T∩B).card:ℝ)) theta (-threshold) htheta
  have he := mul_le_mul_of_nonneg_left
    (fixed_sample_count_mgf_exponential D B hD hB hk (-theta)) (exp_pos (theta*threshold)).le
  have hp : (fun T : Finset V => -threshold ≤ -((T∩B).card:ℝ))=
      (fun T => ((T∩B).card:ℝ) ≤ threshold) := by funext T; apply propext; exact neg_le_neg_iff
  rw [hp] at hm
  simp only [mul_neg,neg_mul,neg_neg] at hm he
  exact hm.trans (by simpa only [← exp_add] using he)

/-- The minority-label exception exp(-q) is paid under the fixed-size
marking law itself, including q=6 used in the accepted sampler. -/
theorem fixed_mark_minority_tail (D A : Finset V) (hD : D.Nonempty) (hA : A⊆D)
    {t : ℕ} (ht : t ≤ D.card) (q : ℝ) :
    (fixedSizeLaw D t).prob (fun T =>
      (exp 1-1)*((t:ℝ)/D.card)*A.card+q < ((T∩A).card:ℝ)) ≤ exp (-q) := by
  have hh := fixed_sample_count_upper D A hD hA ht
    (theta:=1) (threshold:=(exp 1-1)*((t:ℝ)/D.card)*A.card+q) (by norm_num)
  convert hh using 1 <;> congr 1 <;> ring

theorem fixed_sample_lower_chernoff (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {mu dm z : ℝ}
    (hz : 0<z) (hdm : 0<dm) (hgap : dm < mu)
    (hmean : mu*z ≤ ((k:ℝ)/D.card)*B.card) :
    (fixedSizeLaw D k).prob (fun T => ((T∩B).card:ℝ) ≤ dm*z) ≤
      exp (-(mu-dm-dm*log (mu/dm))*z) := by
  have hmu := hdm.trans hgap
  have hratio : 1 < mu/dm := (one_lt_div hdm).mpr hgap
  have htheta : 0<log (mu/dm) := log_pos hratio
  have hh := fixed_sample_count_lower D B hD hB hk htheta.le (threshold:=dm*z)
  apply hh.trans
  apply exp_le_exp.mpr
  have he : exp (-log (mu/dm))=dm/mu := by
    rw [exp_neg,exp_log (div_pos hmu hdm),inv_div]
  rw [he]
  have hn : dm/mu-1 ≤ 0 := by
    have hh := (div_le_one hmu).mpr hgap.le
    linarith only [hh]
  have hmul := mul_le_mul_of_nonpos_left hmean hn
  have hcancel : (dm/mu-1)*(mu*z)=(dm-mu)*z := by field_simp
  rw [hcancel] at hmul
  nlinarith only [hmul]

/-- Actual degree failure for all original vertices in one fixed-size
sample. The union bound does not assume their degree events independent. -/
theorem fixed_sample_degree_failure [Nonempty V] (G : SimpleGraph V)
    {k : ℕ} (hk : k ≤ Fintype.card V) {mu dm z : ℝ}
    (hz : 0<z) (hdm : 0<dm) (hgap : dm < mu)
    (hmean : ∀ v, mu*z ≤ ((k:ℝ)/Fintype.card V)*(neighborsIn G v univ).card) :
    (fixedSizeLaw (univ:Finset V) k).prob
        (fun T => ∃ v, ((neighborsIn G v T).card:ℝ) ≤ dm*z) ≤
      Fintype.card V*exp (-(mu-dm-dm*log (mu/dm))*z) := by
  have hpoint (v : V) : (fixedSizeLaw (univ:Finset V) k).prob
      (fun T => ((neighborsIn G v T).card:ℝ) ≤ dm*z) ≤
        exp (-(mu-dm-dm*log (mu/dm))*z) := by
    have hh := fixed_sample_lower_chernoff univ (neighborsIn G v univ)
      univ_nonempty (subset_univ _) (by simpa only [card_univ] using hk)
      hz hdm hgap (by simpa only [card_univ] using hmean v)
    have he (T : Finset V) : T∩neighborsIn G v univ=neighborsIn G v T := by
      ext w
      simp only [neighborsIn,mem_inter,mem_filter,mem_univ,true_and]
    simpa only [he] using hh
  have hu := (fixedSizeLaw (univ:Finset V) k).prob_exists_le_sum
    (fun v T => ((neighborsIn G v T).card:ℝ) ≤ dm*z)
  apply hu.trans
  calc
    _ ≤ ∑ _v : V, exp (-(mu-dm-dm*log (mu/dm))*z) := sum_le_sum (fun v _ => hpoint v)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

end
end Cycle12
