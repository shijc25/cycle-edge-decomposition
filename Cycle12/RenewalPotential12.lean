import Mathlib

namespace Cycle12
open Real Set
noncomputable section

def renewalLoss (H : ℝ → ℝ) (b x : ℝ) : ℝ := ∑' j : ℕ,H (x/b^(j+1))

theorem renewal_argument_mem {b w x : ℝ} (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (hx : b*w≤x) (j : ℕ) : w ≤ x/b^(j+1) := by
  apply (le_div_iff₀ (pow_pos hb _)).mpr
  have hp : b^(j+1) ≤ b := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ (n:=j) hb.le hb1) hb.le
  have hh := mul_le_mul_of_nonneg_left hp hw
  linarith only [hh,hx]

theorem renewal_summable {H : ℝ → ℝ} {b w x : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (hH : AntitoneOn H (Ici w)) (h0 : ∀ y∈Ici w,0≤H y)
    (hs : Summable (fun j : ℕ => H ((b*w)/b^(j+1)))) (hx : b*w≤x) :
    Summable (fun j : ℕ => H (x/b^(j+1))) := by
  apply Summable.of_nonneg_of_le (fun j => h0 _ (renewal_argument_mem hb hb1 hw hx j))
    (fun j => ?_) hs
  exact hH (renewal_argument_mem hb hb1 hw le_rfl j)
    (renewal_argument_mem hb hb1 hw hx j) (div_le_div_of_nonneg_right hx (pow_nonneg hb.le _))

theorem renewalLoss_nonneg {H : ℝ → ℝ} {b w x : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (h0 : ∀ y∈Ici w,0≤H y) (hx : b*w≤x) : 0≤renewalLoss H b x :=
  tsum_nonneg (fun j => h0 _ (renewal_argument_mem hb hb1 hw hx j))

theorem renewalLoss_antitone {H : ℝ → ℝ} {b w : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (hH : AntitoneOn H (Ici w)) (h0 : ∀ y∈Ici w,0≤H y)
    (hs : Summable (fun j : ℕ => H ((b*w)/b^(j+1)))) :
    AntitoneOn (renewalLoss H b) (Ici (b*w)) := by
  intro x hx y hy hxy
  apply Summable.tsum_le_tsum (fun j => ?_)
    (renewal_summable hb hb1 hw hH h0 hs hy) (renewal_summable hb hb1 hw hH h0 hs hx)
  exact hH (renewal_argument_mem hb hb1 hw hx j)
    (renewal_argument_mem hb hb1 hw hy j) (div_le_div_of_nonneg_right hxy (pow_nonneg hb.le _))

theorem renewalLoss_step {H : ℝ → ℝ} {b x : ℝ} (hb : b≠0)
    (hs : Summable (fun j : ℕ => H ((b*x)/b^(j+1)))) :
    renewalLoss H b (b*x)=H x+renewalLoss H b x := by
  have harg (j : ℕ) : b*x/b^(j+1)=x/b^j := by
    rw [pow_succ]
    field_simp
  unfold renewalLoss
  simp_rw [harg] at hs ⊢
  have hh := hs.tsum_eq_zero_add
  simpa only [pow_zero,div_one] using hh

def renewalPhi (H : ℝ → ℝ) (b w phi0 x : ℝ) : ℝ :=
  if x<b*w then phi0 else 1-renewalLoss H b x

theorem renewalPhi_bounds {H : ℝ → ℝ} {b w phi0 : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (hH : AntitoneOn H (Ici w)) (h0 : ∀ y∈Ici w,0≤H y)
    (hs : Summable (fun j : ℕ => H ((b*w)/b^(j+1))))
    (hp : 0<phi0) (hbase : phi0≤1-renewalLoss H b (b*w)) (x : ℝ) :
    0<renewalPhi H b w phi0 x ∧ renewalPhi H b w phi0 x≤1 := by
  have hzero := renewalLoss_nonneg hb hb1 hw h0 (le_refl (b*w))
  by_cases hx : x<b*w
  · simp only [renewalPhi,if_pos hx]
    exact ⟨hp,by linarith only [hbase,hzero]⟩
  · have hx' := le_of_not_gt hx
    have hm := renewalLoss_antitone hb hb1 hw hH h0 hs (show b*w∈Ici (b*w) from Set.mem_Ici.mpr le_rfl) hx' hx'
    have hn := renewalLoss_nonneg hb hb1 hw h0 hx'
    simp only [renewalPhi,if_neg hx]
    constructor <;> linarith

theorem renewalPhi_monotone {H : ℝ → ℝ} {b w phi0 : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (hH : AntitoneOn H (Ici w)) (h0 : ∀ y∈Ici w,0≤H y)
    (hs : Summable (fun j : ℕ => H ((b*w)/b^(j+1))))
    (hbase : phi0≤1-renewalLoss H b (b*w)) : Monotone (renewalPhi H b w phi0) := by
  intro x y hxy
  by_cases hy : y<b*w
  · simp only [renewalPhi,if_pos hy,if_pos (hxy.trans_lt hy)]
    exact le_rfl
  · by_cases hx : x<b*w
    · simp only [renewalPhi,if_pos hx,if_neg hy]
      have hm := renewalLoss_antitone hb hb1 hw hH h0 hs
        (show b*w∈Ici (b*w) from Set.mem_Ici.mpr le_rfl) (le_of_not_gt hy) (le_of_not_gt hy)
      linarith only [hm,hbase]
    · simp only [renewalPhi,if_neg hx,if_neg hy]
      have hm := renewalLoss_antitone hb hb1 hw hH h0 hs (le_of_not_gt hx) (le_of_not_gt hy) hxy
      linarith only [hm]

/-- The telescoping loss is exactly the amount paid when a batch of
order at most 2^(b*x) is used inside a graph of log-order at least x. -/
theorem renewalPhi_fold_budget {H : ℝ → ℝ} {b w phi0 x y : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hw : 0≤w)
    (hH : AntitoneOn H (Ici w)) (h0 : ∀ z∈Ici w,0≤H z)
    (hs : Summable (fun j : ℕ => H ((b*w)/b^(j+1))))
    (hx : w≤x) (hy : x≤y) :
    H x ≤ renewalPhi H b w phi0 y-renewalPhi H b w phi0 (b*x) := by
  have hbw : b*w≤w := by nlinarith only [mul_le_mul_of_nonneg_right hb1 hw]
  have hx' : b*w≤x := hbw.trans hx
  have hy' : b*w≤y := hx'.trans hy
  have hbx : b*w≤b*x := mul_le_mul_of_nonneg_left hx hb.le
  have hstep := renewalLoss_step (H:=H) hb.ne'
    (renewal_summable hb hb1 hw hH h0 hs hbx)
  have hm := renewalLoss_antitone hb hb1 hw hH h0 hs hx' hy' hy
  simp only [renewalPhi,if_neg (not_lt.mpr hy'),if_neg (not_lt.mpr hbx)]
  linarith only [hstep,hm]

end
end Cycle12
