import Cycle12.Foundations.MonotoneBernoulliMGF

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bernstein_optimal_parameter {v b t : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (ht : 0 < t) :
    0 < t/(v+b*t/3) ∧ (t/(v+b*t/3))*b < 3 ∧
      -(t/(v+b*t/3))*t+(t/(v+b*t/3))^2*v/(2*(1-(t/(v+b*t/3))*b/3))=
        -t^2/(2*(v+b*t/3)) := by
  have hden : 0 < v+b*t/3 := by positivity
  have hθ : 0 < t/(v+b*t/3) := div_pos ht hden
  have hθb : (t/(v+b*t/3))*b < 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  refine ⟨hθ,hθb,?_⟩
  have hden₂ : 0 < 1-(t/(v+b*t/3))*b/3 := by linarith
  have hlinear : 3*v+b*t ≠ 0 := by positivity
  field_simp [hden.ne',hden₂.ne',hv.ne',hlinear]
  <;> ring

theorem subsetBernoulli_monotone_upper_tail (W : Finset V) (p : unitInterval)
    (f : Finset V→ℝ) (d : V→ℝ) {r v t : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (ht : 0 < t)
    (hd : ∀ x∈W, 0 ≤ d x ∧ d x ≤ r)
    (hinc : ∀ x∈W, ∀ S : Finset V, x∉S → 0 ≤ f (insert x S)-f S ∧ f (insert x S)-f S ≤ d x)
    (hvar : (p:ℝ)*(1-(p:ℝ))*(∑ x∈W, (d x)^2) ≤ v) :
    (subsetBernoulli W p).prob (fun S => (subsetBernoulli W p).expect f+t ≤ f S) ≤
      exp (-t^2/(2*(v+(1-(p:ℝ))*r*t/3))) := by
  let b := (1-(p:ℝ))*r
  let θ := t/(v+b*t/3)
  have hb : 0 ≤ b := mul_nonneg (sub_nonneg.mpr p.2.2) hr
  have hopt := bernstein_optimal_parameter hv hb ht
  have hθ : 0 ≤ θ := hopt.1.le
  have hθr : θ*(1-(p:ℝ))*r < 3 := by
    have hh : θ*b < 3 := hopt.2.1
    simpa only [b,mul_assoc] using hh
  have hden : 0 < 2*(1-θ*(1-(p:ℝ))*r/3) := by linarith
  have hmgf := subsetBernoulli_monotone_mgf W p f d hr hθ hθr hd hinc
  have hbudget : bernsteinFactor p θ r*(∑ x∈W, (d x)^2) ≤
      θ^2*v/(2*(1-θ*(1-(p:ℝ))*r/3)) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvar (sq_nonneg θ)) hden.le
    convert hh using 1 <;> dsimp [bernsteinFactor] <;> ring
  have hmark := (subsetBernoulli W p).exp_markov_le
    (fun S => f S-(subsetBernoulli W p).expect f) θ t hθ
  have hevent : (fun S : Finset V => (subsetBernoulli W p).expect f+t ≤ f S)=
      (fun S : Finset V => t ≤ f S-(subsetBernoulli W p).expect f) := by
    funext S; apply propext; constructor <;> intro h <;> linarith
  rw [hevent]
  apply hmark.trans
  have hbound := hmgf.trans (exp_le_exp.mpr hbudget)
  apply (mul_le_mul_of_nonneg_left hbound (exp_pos (-θ*t)).le).trans_eq
  rw [← exp_add]
  congr 1
  simpa only [b,θ,mul_assoc] using hopt.2.2

end
end Cycle13
