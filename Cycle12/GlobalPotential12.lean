import Cycle12.RenewalAnchorBound12

namespace Cycle12.Global12
open Real Set
noncomputable section

def globalPhi (x : ℝ) : ℝ := renewalPhi lossH b wA phi0 x
def orderPotential (n : ℕ) : ℝ := globalPhi (logb 2 n)

theorem globalPhi_bounds (x : ℝ) : 0<globalPhi x ∧ globalPhi x≤1 :=
  renewalPhi_bounds (by norm_num [b]) (by norm_num [b]) (by norm_num [wA])
    lossH_antitone (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (globalLoss_summable le_rfl) (by norm_num [phi0]) globalLoss_floor x

theorem globalPhi_monotone : Monotone globalPhi :=
  renewalPhi_monotone (by norm_num [b]) (by norm_num [b]) (by norm_num [wA])
    lossH_antitone (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (globalLoss_summable le_rfl) globalLoss_floor

theorem globalPhi_small {x : ℝ} (hx : x<b*wA) : globalPhi x=phi0 := by
  simp only [globalPhi,renewalPhi,ite_eq_left hx]

theorem globalPhi_large {x : ℝ} (hx : b*wA≤x) : globalPhi x=1-globalLoss x := by
  simp only [globalPhi,renewalPhi,ite_eq_right (not_lt.mpr hx),globalLoss]

theorem globalPhi_lower (x : ℝ) : phi0≤globalPhi x := by
  by_cases hx : x<b*wA
  · exact le_of_eq (globalPhi_small hx).symm
  · have hx' := le_of_not_gt hx
    rw [globalPhi_large hx']
    have hh := globalLoss_antitone (Set.mem_Ici.mpr le_rfl) hx' hx'
    linarith only [hh,globalLoss_floor]

theorem globalPhi_fold_budget {w x : ℝ} (hw : wA≤w) (hx : w≤x) :
    lossH w≤globalPhi x-globalPhi (b*w) :=
  renewalPhi_fold_budget (by norm_num [b]) (by norm_num [b]) (by norm_num [wA])
    lossH_antitone (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (globalLoss_summable le_rfl) hw hx

theorem orderPotential_bounds (n : ℕ) : 0<orderPotential n ∧ orderPotential n≤1 :=
  globalPhi_bounds _

theorem orderPotential_lower (n : ℕ) : phi0≤orderPotential n := globalPhi_lower _

theorem orderPotential_zero : orderPotential 0=phi0 := by
  unfold orderPotential
  simp only [Nat.cast_zero,logb_zero]
  exact globalPhi_small (by norm_num [b,wA])

theorem orderPotential_monotone : Monotone orderPotential := by
  intro n m hnm
  by_cases hn : n=0
  · subst n
    rw [orderPotential_zero]
    exact orderPotential_lower m
  · apply globalPhi_monotone
    exact logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (Nat.cast_le.mpr hnm)

theorem orderPotential_upper_at_scale {n : ℕ} {x : ℝ} (hn : (n:ℝ)≤(2:ℝ)^x) :
    orderPotential n≤globalPhi x := by
  by_cases hz : n=0
  · subst n
    rw [orderPotential_zero]
    exact globalPhi_lower x
  · apply globalPhi_monotone
    exact (logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2)
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))).mpr hn

theorem orderPotential_lower_at_scale {n : ℕ} {x : ℝ} (hn : (2:ℝ)^x≤n) :
    globalPhi x≤orderPotential n := by
  have hp : (0:ℝ)<n := (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) x).trans_le hn
  apply globalPhi_monotone
  exact (le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hp).mpr hn

theorem orderPotential_fold_budget {n : ℕ} {w : ℝ} (hw : wA≤w) (hn : (2:ℝ)^w≤n) :
    lossH w≤orderPotential n-globalPhi (b*w) := by
  have hh := globalPhi_fold_budget hw le_rfl
  have hn' := orderPotential_lower_at_scale hn
  linarith only [hh,hn']

end
end Cycle12.Global12
