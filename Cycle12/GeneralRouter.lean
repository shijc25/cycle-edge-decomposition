import Mathlib

namespace Cycle12

theorem pruning_cutoffs {q a : ℝ} (hq : 0 < q) (ha : 0 < a) (ha1 : a < 1)
    (hgap : 1+q+a*q < 2*a^2*(q+2)) :
    q/(a*(q+2)) < 2*a*q/(1+q+a*q) ∧ 2*a*q/(1+q+a*q) < 1 := by
  have hd : 0 < 1+q+a*q := by positivity
  constructor
  · apply (div_lt_div_iff₀ (by positivity : 0 < a*(q+2)) hd).mpr
    nlinarith [mul_pos hq (sub_pos.mpr hgap)]
  · apply (div_lt_one hd).mpr
    nlinarith [mul_pos hq (sub_pos.mpr ha1)]

theorem pruning_constant_branch {q a x : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hx : x < 2*a*q/(1+q+a*q)) :
    q*a*x/(2*(1+q)) < (a*q/(1+q))^2/(1+a*q/(1+q)) := by
  have hd1 : 0 < 1+q := by positivity
  have hd2 : 0 < 1+q+a*q := by positivity
  have hd3 : 0 < 1+a*q/(1+q) := by positivity
  have hp : 0 < 2*a*q-x*(1+q+a*q) := by
    have hh := (lt_div_iff₀ hd2).mp hx
    linarith
  have he : (a*q/(1+q))^2/(1+a*q/(1+q))-q*a*x/(2*(1+q)) =
      a*q*(2*a*q-x*(1+q+a*q))/(2*(1+q)*(1+q+a*q)) := by
    field_simp [hd1.ne',hd2.ne',hd3.ne']
    <;> ring
  have hh : 0 < (a*q/(1+q))^2/(1+a*q/(1+q))-q*a*x/(2*(1+q)) := by
    rw [he]
    positivity
  linarith

theorem pruning_variable_branch {q a x : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hx : q/(a*(q+2)) < x) :
    q*a*x/(2*(1+q)) < (a*x)^2/(1+a*x) := by
  have hd : 0 < a*(q+2) := by positivity
  have hx0 : 0 < x := lt_trans (div_pos hq hd) hx
  have hd1 : 0 < 1+q := by positivity
  have hd2 : 0 < 1+a*x := by positivity
  have hp : 0 < a*(q+2)*x-q := by
    have hh := (div_lt_iff₀ hd).mp hx
    nlinarith
  have he : (a*x)^2/(1+a*x)-q*a*x/(2*(1+q)) =
      a*x*(a*(q+2)*x-q)/(2*(1+q)*(1+a*x)) := by
    field_simp [hd1.ne',hd2.ne']
    <;> ring
  have hh : 0 < (a*x)^2/(1+a*x)-q*a*x/(2*(1+q)) := by
    rw [he]
    positivity
  linarith

/-- Universal scalar choice for arbitrary endpoint/team load ratio q.
The graph routing theorem itself is still a separate formalization task. -/
theorem general_router_choice {q a x : ℝ} (hq : 0 < q) (ha : 0 < a) (ha1 : a < 1)
    (hgap : 1+q+a*q < 2*a^2*(q+2)) (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ z τ : ℝ, 0 < z ∧ z < 1 ∧ 0 < τ ∧
      1-z-τ=1-a ∧ q*x/z+(1-x)/τ=(1+q)/a ∧
      q*a*x/(2*(1+q)) < z^2/(1+z) := by
  have hg := pruning_cutoffs hq ha ha1 hgap
  have hd : 0 < 1+q := by positivity
  let mid := (q/(a*(q+2))+2*a*q/(1+q+a*q))/2
  by_cases hm : x ≤ mid
  · have hxu : x < 2*a*q/(1+q+a*q) := by dsimp [mid] at hm; linarith [hg.1]
    refine ⟨a*q/(1+q),a/(1+q),by positivity,?_,by positivity,?_,?_,
      pruning_constant_branch hq ha hxu⟩
    · apply (div_lt_one hd).mpr
      nlinarith [mul_pos hq (sub_pos.mpr ha1)]
    · field_simp [hd.ne']
      <;> ring
    · field_simp [ha.ne',hq.ne',hd.ne']
      <;> ring
  · have hxl : q/(a*(q+2)) < x := by dsimp [mid] at hm; linarith [hg.1]
    have hx0 : 0 < x := lt_trans (by positivity : 0 < q/(a*(q+2))) hxl
    have hn : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
    refine ⟨a*x,a*(1-x),by positivity,?_,by positivity,by ring,?_,
      pruning_variable_branch hq ha hxl⟩
    · nlinarith [mul_pos (sub_pos.mpr ha1) hx0]
    · field_simp [ha.ne',hx0.ne',hn]
      <;> ring

end Cycle12
