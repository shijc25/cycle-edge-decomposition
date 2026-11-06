import Cycle12.GlobalLossFunctions12
import Cycle12.PowerRenewal12

namespace Cycle12.Global12
open Real Set
noncomputable section

def globalLoss (x : ℝ) : ℝ := renewalLoss lossH b x

theorem globalLoss_summable {x : ℝ} (hx : b*wA≤x) :
    Summable (fun j : ℕ => lossH (x/b^(j+1))) :=
  lossH_decay.renewal_summable (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (by norm_num [wA]) loss_rate_bounds.1 (by norm_num [b]) (by norm_num [b]) hx

theorem globalLoss_nonneg {x : ℝ} (hx : b*wA≤x) : 0≤globalLoss x :=
  renewalLoss_nonneg (by norm_num [b]) (by norm_num [b]) (by norm_num [wA])
    (fun _ hw => (losses_nonneg hw).2.2.2.2.2) hx

theorem globalLoss_antitone : AntitoneOn globalLoss (Ici (b*wA)) :=
  renewalLoss_antitone (by norm_num [b]) (by norm_num [b]) (by norm_num [wA])
    lossH_antitone (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (globalLoss_summable le_rfl)

theorem globalLoss_step {w : ℝ} (hw : wA≤w) : globalLoss (b*w)=lossH w+globalLoss w :=
  renewalLoss_step (by norm_num [b])
    (globalLoss_summable (mul_le_mul_of_nonneg_left hw (by norm_num [b])))

theorem globalLoss_scaled (w : ℝ) : globalLoss (b*w)=∑' j : ℕ,lossH (w/b^j) := by
  unfold globalLoss renewalLoss
  congr 1
  funext j
  congr 1
  rw [pow_succ]
  have hb : b≠0 := by norm_num [b]
  field_simp

theorem globalLoss_decay : PowerDecay globalLoss (b*wA) (lossRate/b) :=
  lossH_decay.renewal_decay (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (by norm_num [wA]) loss_rate_bounds.1 (by norm_num [b]) (by norm_num [b])

theorem globalLoss_two_step {x : ℝ} (hx : b*wA≤x) :
    globalLoss (x/theta2^2)≤(2:ℝ)^(-(lossRate/b)*x*(theta2⁻¹^2-1))*globalLoss x := by
  have hx0 : 0≤x := (show 0≤b*wA by norm_num [b,wA]).trans hx
  have hxx : x≤x/theta2^2 := geometric_argument_lower
    (by norm_num [theta2]) (by norm_num [theta2]) hx0 2
  have hh := globalLoss_decay hx hxx
  convert hh using 1
  congr 2
  simp only [div_eq_mul_inv,inv_pow]
  ring

theorem globalLoss_half_tail {w : ℝ} (hw : wA≤w) (N : ℕ)
    (hstep : 1≤lossRate*(w/b^N)*(b⁻¹-1)) :
    globalLoss (b*w)≤(∑ j∈Finset.range N,lossH (w/b^j))+2*lossH (w/b^N) := by
  rw [globalLoss_scaled]
  exact lossH_decay.series_half_tail (fun _ hw => (losses_nonneg hw).2.2.2.2.2)
    (by norm_num [wA]) loss_rate_bounds.1 (by norm_num [b]) (by norm_num [b]) hw N hstep

end
end Cycle12.Global12
