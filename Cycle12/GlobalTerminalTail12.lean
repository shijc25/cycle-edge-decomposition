import Cycle12.PotentialPayment12
import Cycle12.InfinitePrefix
import Cycle12.Foundations.TailAbsorption

namespace Cycle12
open Real Finset
noncomputable section

theorem splice_recurrence_from {r : ℝ} {N n : ℕ} {u : ℕ → ℝ}
    (hN : 2≤N) (hn : N-2≤n) :
    splice r N u (n+2)=(1-r)*splice r N u (n+1)+r*(1-r)*splice r N u n := by
  have h0 := splice_shift r hN u (n-(N-2))
  have h1 := splice_shift r hN u (n-(N-2)+1)
  have h2 := splice_shift r hN u (n-(N-2)+2)
  have e0 : n-(N-2)+(N-2)=n := by omega
  have e1 : n-(N-2)+1+(N-2)=n+1 := by omega
  have e2 : n-(N-2)+2+(N-2)=n+2 := by omega
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [h0,h1,h2]
  exact Cycle122.tailTerm_recurrence _ _ _ _

theorem sequenceTail_two_step {u : ℕ → ℝ} {beta : ℝ} {N k : ℕ}
    (hs : Summable u) (hstep : ∀ n,N≤n → beta*u n≤u (n+2)) (hk : N≤k) :
    beta*sequenceTail u k ≤ sequenceTail u (k+2) := by
  unfold sequenceTail
  rw [←tsum_mul_left]
  apply Summable.tsum_le_tsum (fun j => ?_)
    (((summable_nat_add_iff k).mpr hs).mul_left beta) ((summable_nat_add_iff (k+2)).mpr hs)
  simpa only [Nat.add_assoc] using hstep (j+k) (by omega)

theorem splice_tail_two_step {r : ℝ} {N k : ℕ} {u : ℕ → ℝ}
    (hN : 2≤N) (hr : r≤1) (hs : Summable (splice r N u))
    (hu : ∀ n,0 ≤ splice r N u n) (hk : N-2≤k) :
    r*(1-r)*sequenceTail (splice r N u) k ≤ sequenceTail (splice r N u) (k+2) := by
  apply sequenceTail_two_step hs (N:=N-2) (fun n hn => ?_) hk
  rw [splice_recurrence_from hN hn]
  have hh := mul_nonneg (sub_nonneg.mpr hr) (hu (n+1))
  linarith only [hh]

end
end Cycle12

namespace Cycle12.Global12
open Real Finset
noncomputable section

theorem globalLoss_geometric_contraction {A beta : ℝ} {N n : ℕ}
    (hA : wA≤A) (hn : N≤n)
    (hbase : (2:ℝ)^(-(lossRate/b)*(A/theta2^N)*(theta2⁻¹^2-1))≤beta) :
    globalLoss (A/theta2^(n+2))≤beta*globalLoss (A/theta2^n) := by
  have ht : 0<theta2 := by norm_num [theta2]
  have hA0 := (show 0<wA by norm_num [wA]).trans_le hA
  have hx0 := hA.trans (geometric_argument_lower ht (by norm_num [theta2]) hA0.le n)
  have hx : b*wA≤A/theta2^n := (show b*wA≤wA by norm_num [b,wA]).trans hx0
  have hh := globalLoss_two_step hx
  have hnN : A/theta2^N≤A/theta2^n := div_le_div_of_nonneg_left hA0.le (pow_pos ht n)
    (pow_le_pow_of_le_one ht.le (by norm_num [theta2]) hn)
  have hz : 0≤(lossRate/b)*(theta2⁻¹^2-1) := by norm_num [lossRate,eps,theta2,b]
  have hmul := mul_le_mul_of_nonneg_left hnN hz
  have hp : (2:ℝ)^(-(lossRate/b)*(A/theta2^n)*(theta2⁻¹^2-1))≤beta :=
    (rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hmul])).trans hbase
  have he : (A/theta2^n)/theta2^2=A/theta2^(n+2) := by rw [pow_add]; field_simp
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hp (globalLoss_nonneg hx))

/-- Two starting tail payments and the actual recurrence pay every later
terminal index, not merely a finite checked prefix. -/
theorem infinite_terminal_tail_payment {A beta K : ℝ} (u : ℕ → ℝ)
    (hA : wA≤A) (hb : 0≤beta) (hK : 0≤K)
    (hdec : (2:ℝ)^(-(lossRate/b)*(A/theta2^12)*(theta2⁻¹^2-1))≤beta)
    (hu : ∀ k,15≤k → beta*sequenceTail u k ≤ sequenceTail u (k+2))
    (h0 : C*globalLoss (A/theta2^12)≤K*sequenceTail u 16)
    (h1 : C*globalLoss (A/theta2^13)≤K*sequenceTail u 17)
    {m : ℕ} (hm : 15 ≤ m) :
    C*globalLoss (A/theta2^(m-3))≤K*sequenceTail u (m+1) := by
  have hcomp : ∀ n : ℕ,C*globalLoss (A/theta2^(n+12))≤K*sequenceTail u (n+16) := by
    apply Cycle124.two_step_comparison hb h0 h1
    · intro n
      have hh := mul_le_mul_of_nonneg_left
        (globalLoss_geometric_contraction hA (show 12≤n+12 by omega) hdec)
        (show 0≤C by norm_num [C])
      simpa only [show n+2+12=n+12+2 by omega,mul_assoc,mul_left_comm] using hh
    · intro n
      have hh := mul_le_mul_of_nonneg_left (hu (n+16) (by omega)) hK
      simpa only [show n+16+2=n+2+16 by omega,mul_assoc,mul_left_comm] using hh
  have hh := hcomp (m-15)
  simpa only [show m-15+12=m-3 by omega,show m-15+16=m+1 by omega] using hh

theorem terminal_potential_payment {A f J beta : ℝ} (u : ℕ → ℝ)
    (hA : wA≤A) (hb : 0≤beta)
    (hbudget : f+(1+C*eta)*sequenceTail u 3+J≤C)
    (hfinite : ∀ m,3 ≤ m → m<15 →
      C*globalLoss (A/theta2^(m-3))+f+(1+C*eta)*sequenceTail u 3+J≤
        C+(1+C*eta)*sequenceTail u (m+1))
    (hdec : (2:ℝ)^(-(lossRate/b)*(A/theta2^12)*(theta2⁻¹^2-1))≤beta)
    (hu : ∀ k,15≤k → beta*sequenceTail u k ≤ sequenceTail u (k+2))
    (h0 : C*globalLoss (A/theta2^12)≤(1+C*eta)*sequenceTail u 16)
    (h1 : C*globalLoss (A/theta2^13)≤(1+C*eta)*sequenceTail u 17)
    {m : ℕ} (hm : 3 ≤ m) :
    f+(1+C*eta)*(sequenceTail u 3-sequenceTail u (m+1))+J≤
      C*globalPhi (A/theta2^(m-3)) := by
  have hA0 := (show 0≤wA by norm_num [wA]).trans hA
  have hx : b*wA≤A/theta2^(m-3) := (show b*wA≤wA by norm_num [b,wA]).trans
    (hA.trans (geometric_argument_lower (by norm_num [theta2]) (by norm_num [theta2]) hA0 (m-3)))
  rw [globalPhi_large hx]
  by_cases hsmall : m<15
  · have hh := hfinite m hm hsmall
    nlinarith only [hh]
  · have hh := infinite_terminal_tail_payment u hA hb (show 0≤1+C*eta by norm_num [C,eta])
      hdec hu h0 h1 (le_of_not_gt hsmall)
    nlinarith only [hh,hbudget]

end
end Cycle12.Global12
