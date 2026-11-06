import Cycle12.Foundations.BernsteinExponential
import Cycle12.Foundations.SubsetBernoulliRecursion
import Cycle12.Foundations.FiniteCantelli

/-! A one-sided Bernstein bound from finite Bernoulli exposure. The
coordinate increments are nonnegative, yielding the upper increment
(1-p)*r and variance budget p*(1-p)*sum d(v)^2. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem FiniteLaw.centered_exp_shift {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω→ℝ) (θ a b : ℝ) :
    μ.expect (fun S => exp (θ*(f S-a)))=
      exp (θ*(b-a))*μ.expect (fun S => exp (θ*(f S-b))) := by
  have he : ∀ S, θ*(f S-a)=θ*(b-a)+θ*(f S-b) := by intro S; ring
  simp_rw [he,exp_add]
  rw [FiniteLaw.expect_const_mul]

def bernsteinFactor (p : unitInterval) (θ r : ℝ) : ℝ :=
  θ^2*(p:ℝ)*(1-(p:ℝ))/(2*(1-θ*(1-(p:ℝ))*r/3))

theorem bernsteinFactor_nonneg (p : unitInterval) {θ r : ℝ}
    (hθr : θ*(1-(p:ℝ))*r < 3) : 0 ≤ bernsteinFactor p θ r := by
  unfold bernsteinFactor
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (sq_nonneg θ) p.2.1) (sub_nonneg.mpr p.2.2)
  · linarith

theorem subsetBernoulli_monotone_mgf (W : Finset V) (p : unitInterval)
    (f : Finset V→ℝ) (d : V→ℝ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hθr : θ*(1-(p:ℝ))*r < 3)
    (hd : ∀ v∈W, 0 ≤ d v ∧ d v ≤ r)
    (hinc : ∀ v∈W, ∀ S : Finset V, v∉S → 0 ≤ f (insert v S)-f S ∧ f (insert v S)-f S ≤ d v) :
    (subsetBernoulli W p).expect (fun S => exp (θ*(f S-(subsetBernoulli W p).expect f))) ≤
      exp (bernsteinFactor p θ r*(∑ v∈W, (d v)^2)) := by
  induction W using Finset.induction_on generalizing f with
  | empty => simp only [subsetBernoulli_expect_empty,sub_self,mul_zero,exp_zero,sum_empty,le_refl]
  | @insert v W hv ih =>
    let μ := subsetBernoulli W p
    let f₁ : Finset V→ℝ := fun S => f (insert v S)
    let m₀ := μ.expect f
    let m₁ := μ.expect f₁
    let M := (1-(p:ℝ))*m₀+(p:ℝ)*m₁
    let K := bernsteinFactor p θ r
    have hK : 0 ≤ K := bernsteinFactor_nonneg p hθr
    have hdv := hd v (mem_insert_self _ _)
    have hdW : ∀ w∈W, 0 ≤ d w ∧ d w ≤ r := fun w hw => hd w (mem_insert_of_mem hw)
    have hincW := fun w hw => hinc w (mem_insert_of_mem hw)
    have hinc₁ : ∀ w∈W, ∀ S : Finset V, w∉S →
        0 ≤ f₁ (insert w S)-f₁ S ∧ f₁ (insert w S)-f₁ S ≤ d w := by
      intro w hw S hwS
      have hwv : w≠v := by intro he; subst w; exact hv hw
      have hh := hincW w hw (insert v S) (by simpa [hwv] using hwS)
      simpa only [f₁,insert_comm v w] using hh
    have h₀ := ih f hdW hincW
    have h₁ := ih f₁ hdW hinc₁
    have hdiff : ∀ S : Finset V, 0 ≤ f₁ S-f S ∧ f₁ S-f S ≤ d v := by
      intro S
      by_cases hvS : v∈S
      · simpa only [f₁,insert_eq_of_mem hvS,sub_self] using ⟨le_refl (0:ℝ),hdv.1⟩
      · exact hinc v (mem_insert_self _ _) S hvS
    have hmean : μ.expect (fun S => f₁ S-f S)=m₁-m₀ := μ.expect_sub f₁ f
    have hdm0 : 0 ≤ m₁-m₀ := by rw [← hmean]; exact μ.expect_nonneg (fun S => (hdiff S).1)
    have hdmv : m₁-m₀ ≤ d v := by
      rw [← hmean]
      exact (μ.expect_mono (Y:=fun _ => d v) (fun S => (hdiff S).2)).trans_eq (μ.expect_const _)
    have htotal : (subsetBernoulli (insert v W) p).expect f=M :=
      subsetBernoulli_expect_insert W v hv p f
    rw [htotal,subsetBernoulli_expect_insert W v hv p]
    change (1-(p:ℝ))*μ.expect (fun S => exp (θ*(f S-M)))+
      (p:ℝ)*μ.expect (fun S => exp (θ*(f₁ S-M))) ≤ _
    rw [μ.centered_exp_shift f θ M m₀,μ.centered_exp_shift f₁ θ M m₁]
    have hshift₀ : θ*(m₀-M)= -θ*(p:ℝ)*(m₁-m₀) := by dsimp [M]; ring
    have hshift₁ : θ*(m₁-M)=θ*(1-(p:ℝ))*(m₁-m₀) := by dsimp [M]; ring
    rw [hshift₀,hshift₁]
    have hp1 : 0 ≤ 1-(p:ℝ) := sub_nonneg.mpr p.2.2
    have h₀' := mul_le_mul_of_nonneg_left h₀
      (mul_nonneg hp1 (exp_pos (-θ*(p:ℝ)*(m₁-m₀))).le)
    have h₁' := mul_le_mul_of_nonneg_left h₁
      (mul_nonneg p.2.1 (exp_pos (θ*(1-(p:ℝ))*(m₁-m₀))).le)
    have hbin := centered_bernoulli_mgf_bound p hdm0 (hdmv.trans hdv.2) hθ hθr
    have hbin' : (1-(p:ℝ))*exp (-θ*(p:ℝ)*(m₁-m₀))+
        (p:ℝ)*exp (θ*(1-(p:ℝ))*(m₁-m₀)) ≤ exp (K*(d v)^2) := by
      have he : θ^2*(p:ℝ)*(1-(p:ℝ))*(m₁-m₀)^2/(2*(1-θ*(1-(p:ℝ))*r/3))=
          K*(m₁-m₀)^2 := by dsimp [K,bernsteinFactor]; ring
      rw [he] at hbin
      apply hbin.trans
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (sq_le_sq₀ hdm0 hdv.1 |>.mpr hdmv) hK
    have hfinal := mul_le_mul_of_nonneg_left hbin' (exp_pos (K*∑ w∈W, (d w)^2)).le
    have he : exp (K*(∑ w∈W, (d w)^2))*exp (K*(d v)^2)=
        exp (K*(∑ w∈insert v W, (d w)^2)) := by
      rw [← exp_add,sum_insert hv]
      congr 1
      ring
    rw [he] at hfinal
    change _ ≤ exp (K*(∑ w∈insert v W, (d w)^2))
    change ((1-(p:ℝ))*exp (-θ*(p:ℝ)*(m₁-m₀)))*μ.expect
      (fun S => exp (θ*(f S-m₀))) ≤ ((1-(p:ℝ))*exp (-θ*(p:ℝ)*(m₁-m₀)))*
        exp (K*(∑ w∈W, (d w)^2)) at h₀'
    change ((p:ℝ)*exp (θ*(1-(p:ℝ))*(m₁-m₀)))*μ.expect
      (fun S => exp (θ*(f₁ S-m₁))) ≤ ((p:ℝ)*exp (θ*(1-(p:ℝ))*(m₁-m₀)))*
        exp (K*(∑ w∈W, (d w)^2)) at h₁'
    nlinarith

end
end Cycle13
