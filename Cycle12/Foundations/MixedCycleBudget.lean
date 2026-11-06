import Cycle12.Foundations.MixedCoverBudget
import Mathlib.Analysis.Convex.Piecewise
import Mathlib.Analysis.Convex.Deriv

namespace Cycle13.MixedSample
open Real Set
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The mixed-cover cycle factor, in units of the average-degree threshold 864. -/
def cycleFactor (u : ℝ) : ℝ :=
  if u ≤ 1 then (53/200)*u else 1/2-(47/200)*u^(-(1/3:ℝ))

def cycleBudget (n m : ℝ) : ℝ := n*cycleFactor (m/(432*n))

private def shiftedCycleFactor (u : ℝ) : ℝ :=
  1/2-(47/200)*u^(-(1/3:ℝ))-(53/200)*u

private def shiftedCycleDeriv (u : ℝ) : ℝ :=
  (47/600)*u^(-(4/3:ℝ))-53/200

private theorem shiftedCycle_hasDeriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt shiftedCycleFactor (shiftedCycleDeriv u) u := by
  have hp := hasDerivAt_rpow_const (p:=-(1/3:ℝ)) (Or.inl hu.ne')
  have hh := ((hasDerivAt_const u (1/2:ℝ)).sub (hp.const_mul (47/200))).sub
    ((hasDerivAt_id u).const_mul (53/200))
  unfold shiftedCycleFactor shiftedCycleDeriv
  convert hh using 1 <;> norm_num
  all_goals first | (funext y; simp only [Pi.sub_apply,id_eq] <;> ring) | ring

private theorem shiftedCycle_continuous : ContinuousOn shiftedCycleFactor (Ici 1) := by
  intro u hu
  have hu₁ : 1 ≤ u := hu
  exact (shiftedCycle_hasDeriv (by linarith : 0 < u)).continuousAt.continuousWithinAt

private theorem shiftedCycle_differentiable : DifferentiableOn ℝ shiftedCycleFactor (interior (Ici 1)) := by
  intro u hu
  have hh : 1 ≤ u := interior_subset hu
  exact (shiftedCycle_hasDeriv (by linarith : 0 < u)).differentiableAt.differentiableWithinAt

private theorem shiftedCycle_concave : ConcaveOn ℝ (Ici 1) shiftedCycleFactor := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 1) shiftedCycle_continuous shiftedCycle_differentiable
  intro x hx y hy hxy
  have hx₁ : 1 ≤ x := interior_subset hx
  have hy₁ : 1 ≤ y := interior_subset hy
  rw [(shiftedCycle_hasDeriv (by linarith : 0 < x)).deriv,
    (shiftedCycle_hasDeriv (by linarith : 0 < y)).deriv]
  have hh := rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxy (by norm_num : -(4/3:ℝ) ≤ 0)
  unfold shiftedCycleDeriv
  linarith

private theorem shiftedCycle_antitone : AntitoneOn shiftedCycleFactor (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1) shiftedCycle_continuous shiftedCycle_differentiable
  intro u hu
  have hu₁ : 1 ≤ u := interior_subset hu
  rw [(shiftedCycle_hasDeriv (by linarith : 0 < u)).deriv]
  have hh := rpow_le_one_of_one_le_of_nonpos hu₁ (by norm_num : -(4/3:ℝ) ≤ 0)
  unfold shiftedCycleDeriv
  linarith

/-- Concavity includes the junction at average degree 864. Subtracting the
linear branch reduces the gluing argument to a constant and a decreasing branch. -/
theorem cycleFactor_concave : ConcaveOn ℝ univ cycleFactor := by
  have hc := concaveOn_univ_piecewise_Iic_of_monotoneOn_Iic_antitoneOn_Ici
    (concaveOn_const (c:=(0:ℝ)) (convex_Iic (1:ℝ))) shiftedCycle_concave
    (show MonotoneOn (fun _ : ℝ => (0:ℝ)) (Iic 1) from fun _ _ _ _ _ => le_rfl)
    shiftedCycle_antitone (by norm_num [shiftedCycleFactor])
  have hl : ConcaveOn ℝ univ (fun u : ℝ => (53/200:ℝ)*u) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b _ _ _
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  have he : cycleFactor = (fun u => (Iic (1:ℝ)).piecewise (fun _ => (0:ℝ)) shiftedCycleFactor u+
      (53/200)*u) := by
    funext u
    by_cases hu : u ≤ 1 <;> simp [cycleFactor,Set.piecewise,hu,shiftedCycleFactor]
  rw [he]
  exact hc.add hl

theorem cycleFactor_zero : cycleFactor 0=0 := by norm_num [cycleFactor]

theorem cycleFactor_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ cycleFactor u := by
  unfold cycleFactor
  split_ifs with h
  · positivity
  · have hh := rpow_le_one_of_one_le_of_nonpos (le_of_lt (lt_of_not_ge h))
      (by norm_num : -(1/3:ℝ) ≤ 0)
    linarith

theorem cycleFactor_le_half {u : ℝ} (hu : 0 ≤ u) : cycleFactor u ≤ 1/2 := by
  unfold cycleFactor
  split_ifs with h
  · linarith
  · have hh := rpow_nonneg hu (-(1/3:ℝ))
    linarith

theorem cycleFactor_monotone : MonotoneOn cycleFactor (Ici 0) := by
  intro x hx y hy hxy
  by_cases hx₁ : x ≤ 1
  · by_cases hy₁ : y ≤ 1
    · simp only [cycleFactor,hx₁,hy₁,ite_true]
      linarith
    · have hh := rpow_le_one_of_one_le_of_nonpos (le_of_lt (lt_of_not_ge hy₁))
        (by norm_num : -(1/3:ℝ) ≤ 0)
      simp only [cycleFactor,hx₁,hy₁,ite_true,ite_false]
      linarith
  · have hy₁ : ¬y ≤ 1 := fun h => hx₁ (hxy.trans h)
    have hh := rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxy (by norm_num : -(1/3:ℝ) ≤ 0)
    simp only [cycleFactor,hx₁,hy₁,ite_false]
    linarith

theorem cycleBudget_nonneg {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) : 0 ≤ cycleBudget n m :=
  mul_nonneg hn (cycleFactor_nonneg (div_nonneg hm (by positivity)))

theorem cycleBudget_zero (n : ℝ) : cycleBudget n 0=0 := by simp [cycleBudget,cycleFactor_zero]

theorem cycleBudget_superadditive {n₁ n₂ m₁ m₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    cycleBudget n₁ m₁+cycleBudget n₂ m₂ ≤ cycleBudget (n₁+n₂) (m₁+m₂) := by
  have hn : 0 < n₁+n₂ := add_pos hn₁ hn₂
  have ha : 0 ≤ n₁/(n₁+n₂) := by positivity
  have hb : 0 ≤ n₂/(n₁+n₂) := by positivity
  have hab : n₁/(n₁+n₂)+n₂/(n₁+n₂)=1 := by field_simp
  have hh := cycleFactor_concave.2 (mem_univ (m₁/(432*n₁))) (mem_univ (m₂/(432*n₂))) ha hb hab
  simp only [smul_eq_mul] at hh
  have he : n₁/(n₁+n₂)*(m₁/(432*n₁))+n₂/(n₁+n₂)*(m₂/(432*n₂))=
      (m₁+m₂)/(432*(n₁+n₂)) := by field_simp <;> ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh hn.le
  unfold cycleBudget
  convert hm using 1 <;> field_simp <;> ring

theorem cycleBudget_mono_edges {n m₁ m₂ : ℝ} (hn : 0 ≤ n) (hm₁ : 0 ≤ m₁) (hmm : m₁ ≤ m₂) :
    cycleBudget n m₁ ≤ cycleBudget n m₂ := by
  apply mul_le_mul_of_nonneg_left _ hn
  apply cycleFactor_monotone (by simp only [mem_Ici]; positivity)
    (by simp only [mem_Ici]; positivity [hm₁.trans hmm])
  exact div_le_div_of_nonneg_right hmm (by positivity)

theorem cycleBudget_mono_order {n₁ n₂ m : ℝ} (hn₁ : 0 < n₁) (hn : n₁ ≤ n₂) :
    cycleBudget n₁ m ≤ cycleBudget n₂ m := by
  rcases eq_or_lt_of_le hn with he | hl
  · rw [he]
  · have hh := cycleBudget_superadditive (m₁:=m) (m₂:=0) hn₁ (sub_pos.mpr hl)
    simpa only [cycleBudget_zero,add_zero,add_sub_cancel] using hh

theorem normalized_density_coordinates {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    edgeCount x s/(432*(s^2*order x))=s/(w x)^3 := by
  have hw := (w_pos hx).ne'
  unfold edgeCount order
  field_simp <;> ring

theorem coordinate_deficit_le_w {x s : ℝ} (hx : 0 < x) (hs : 1 ≤ s) :
    (s/(w x)^3)^(-(1/3:ℝ)) ≤ w x := by
  have hsp : 0 < s := by linarith
  have hw := w_pos hx
  have hu : 0 < s/(w x)^3 := by positivity
  have hp := rpow_nonneg hu.le (-(1/3:ℝ))
  apply (pow_le_pow_iff_left₀ hp hw.le (by norm_num : (3:ℕ) ≠ 0)).mp
  have he : ((s/(w x)^3)^(-(1/3:ℝ)))^3=(w x)^3/s := by
    rw [← rpow_mul_natCast hu.le]
    norm_num only [Nat.cast_ofNat,neg_div,neg_mul]
    rw [rpow_neg_one]
    field_simp
  rw [he]
  exact (div_le_iff₀ hsp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg hw.le 3)])

theorem hard_cycleBudget_lower {x s : ℝ} (hx : 0 < x) (hxm : x ≤ xmax) (hs : 1 ≤ s) :
    (1/2-(47/200)*w x)*(s^2*order x) ≤ cycleBudget (s^2*order x) (edgeCount x s) := by
  have hsp : 0 < s := by linarith
  have hw := w_pos hx
  have hwh : w x < 1 := (w_mono hx.le hxm).trans_lt (by norm_num [w,xmax])
  have hw₃ : (w x)^3 < 1 := by nlinarith [sq_nonneg (w x),mul_nonneg hw.le (sub_nonneg.mpr hwh.le)]
  have hu : 1 < s/(w x)^3 := (one_lt_div (pow_pos hw 3)).mpr (by linarith)
  unfold cycleBudget cycleFactor
  rw [normalized_density_coordinates hx hsp,if_neg (not_le_of_gt hu)]
  rw [mul_comm (s^2*order x)]
  apply mul_le_mul_of_nonneg_right _ (by positivity [order_pos hx])
  linarith [coordinate_deficit_le_w hx hs]

end
end Cycle13.MixedSample
