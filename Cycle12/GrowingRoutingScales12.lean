import Cycle12.RoutingScaleEndpoint12
import Cycle12.GlobalBankPreparation12

namespace Cycle12.Global12
open Cycle13 Real
noncomputable section

def teamGrowth (w : ℝ) : ℝ := (2:ℝ)^(growth*(w-wA))
def routingAllowance (w : ℝ) : ℝ := (2:ℝ)^(alpha*w)
def routingTeamSize (w : ℝ) : ℕ := ⌈c*teamGrowth w*routingAllowance w⌉₊
def routingExpansion (w : ℝ) : ℝ := router_bank*(2:ℝ)^(s*w)
def comparisonExpansion (w : ℝ) : ℝ := comparison_bank*(2:ℝ)^(s*w)
def roundingFactor : ℝ := c+1/17592186044416

theorem teamGrowth_pos (w : ℝ) : 0 < teamGrowth w := rpow_pos_of_pos (by norm_num) _
theorem routingAllowance_pos (w : ℝ) : 0 < routingAllowance w := rpow_pos_of_pos (by norm_num) _
theorem routingExpansion_pos (w : ℝ) : 0 < routingExpansion w :=
  mul_pos (by norm_num [router_bank]) (rpow_pos_of_pos (by norm_num) _)
theorem comparisonExpansion_pos (w : ℝ) : 0 < comparisonExpansion w :=
  mul_pos (by norm_num [comparison_bank]) (rpow_pos_of_pos (by norm_num) _)

theorem teamGrowth_one_le {w : ℝ} (hw : wA ≤ w) : 1 ≤ teamGrowth w := by
  exact Real.one_le_rpow (by norm_num) (mul_nonneg routing_parameter_identities.1.le (sub_nonneg.mpr hw))

theorem allowance_large {w : ℝ} (hw : wA ≤ w) : 17592186044416 ≤ routingAllowance w := by
  have he : (44:ℝ) ≤ alpha*w :=
    (show (44:ℝ) ≤ alpha*wA by norm_num [alpha,wA]).trans
      (mul_le_mul_of_nonneg_left hw (by norm_num [alpha]))
  exact (show (17592186044416:ℝ)=(2:ℝ)^(44:ℝ) by norm_num).trans_le
    (rpow_le_rpow_of_exponent_le (by norm_num) he)

theorem growing_rounding_bounds {w : ℝ} (hw : wA ≤ w) :
    0 < routingTeamSize w ∧ c*routingAllowance w ≤ routingTeamSize w ∧
    (routingTeamSize w:ℝ) ≤ roundingFactor*teamGrowth w*routingAllowance w := by
  have ha := routingAllowance_pos w
  have hg := teamGrowth_pos w
  have hc : 0 < c := by norm_num [c]
  have hca := mul_pos (mul_pos hc hg) ha
  have hlo : c*teamGrowth w*routingAllowance w ≤ routingTeamSize w := Nat.le_ceil _
  have hhi : (routingTeamSize w:ℝ) < c*teamGrowth w*routingAllowance w+1 := Nat.ceil_lt_add_one hca.le
  have hg1 := teamGrowth_one_le hw
  have halarge := allowance_large hw
  have hprod : routingAllowance w ≤ teamGrowth w*routingAllowance w := by nlinarith only [hg1,ha]
  refine ⟨Nat.ceil_pos.mpr hca,?_,?_⟩
  · have hcA := mul_pos hc ha
    nlinarith only [hg1,hlo,hcA]
  · unfold roundingFactor
    nlinarith only [halarge,hprod,hhi]

theorem growing_cubic_capacity {w n : ℝ} (hw : wA ≤ w)
    (hn : 0 ≤ n) (horder : n ≤ (2:ℝ)^(rho*w)) :
    router_constant*(routingTeamSize w:ℝ)^2*n ≤ (routingExpansion w)^3 := by
  have hu : 0 < router_bank := by norm_num [router_bank]
  have hc := (div_le_iff₀ (pow_pos hu 3)).mp cubic_scale_base
  have hg := teamGrowth_pos w
  have ha := routingAllowance_pos w
  have hr := rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (rho*w)
  have hB := (growing_rounding_bounds hw).2.2
  have hround : 0 ≤ roundingFactor := by norm_num [roundingFactor,c]
  have hcoeff : 0 ≤ router_constant := by norm_num [router_constant]
  have hfirst : router_constant*(routingTeamSize w:ℝ)^2*n ≤
      router_constant*(roundingFactor*teamGrowth w*routingAllowance w)^2*(2:ℝ)^(rho*w) := by
    gcongr
  have hmult := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (teamGrowth w)^2*(routingAllowance w)^2*(2:ℝ)^(rho*w) by positivity)
  have he : (2:ℝ)^(2*growth*wA)*(teamGrowth w)^2*(routingAllowance w)^2*(2:ℝ)^(rho*w)=
      ((2:ℝ)^(s*w))^3 := by
    unfold teamGrowth routingAllowance
    rw [←rpow_mul_natCast (by norm_num : (0:ℝ)≤2),
      ←rpow_mul_natCast (by norm_num : (0:ℝ)≤2),
      ←rpow_mul_natCast (by norm_num : (0:ℝ)≤2),
      ←rpow_add (by norm_num : (0:ℝ)<2),
      ←rpow_add (by norm_num : (0:ℝ)<2),
      ←rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    unfold growth
    ring
  apply hfirst.trans
  calc
    _ = (router_constant*roundingFactor^2)*
      ((teamGrowth w)^2*(routingAllowance w)^2*(2:ℝ)^(rho*w)) := by ring
    _ ≤ ((2:ℝ)^(2*growth*wA)*router_bank^3)*
      ((teamGrowth w)^2*(routingAllowance w)^2*(2:ℝ)^(rho*w)) := hmult
    _ = (routingExpansion w)^3 := by unfold routingExpansion; rw [mul_pow,←he]; ring

/-- Comparison-bank capacity includes the larger small-ratio team size. -/
theorem growing_comparison_capacity {w : ℝ} (hw : wA ≤ w) :
    16384*max (routingTeamSize w:ℝ) ((6/5)*routingAllowance w) ≤ comparisonExpansion w := by
  let d : ℝ := (6/5)+1/17592186044416
  have hd : 0 < d := by norm_num [d]
  have hu : 0 < comparison_bank := by norm_num [comparison_bank]
  have hbase : 16384*d/comparison_bank ≤ (2:ℝ)^((s-alpha)*wA) := by
    have hl : (16384*d/comparison_bank:ℝ) ≤ (2:ℝ)^(32:ℝ) := by norm_num [d,comparison_bank]
    exact hl.trans (rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [s,alpha,wA]))
  have heg : (s-alpha)*wA ≤ (s-alpha)*w-growth*(w-wA) := by
    have hh := mul_nonneg routing_parameter_identities.2.1.le (sub_nonneg.mpr hw)
    nlinarith only [hh]
  have hp := hbase.trans (rpow_le_rpow_of_exponent_le (by norm_num) heg)
  have hcap := (div_le_iff₀ hu).mp hp
  have ha := routingAllowance_pos w
  have hg := teamGrowth_pos w
  have hg1 := teamGrowth_one_le hw
  have hb := (growing_rounding_bounds hw).2.2
  have hround : roundingFactor ≤ d := by norm_num [roundingFactor,c,d]
  have hB : (routingTeamSize w:ℝ) ≤ d*teamGrowth w*routingAllowance w :=
    hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hround hg.le) ha.le)
  have hK : (6/5)*routingAllowance w ≤ d*teamGrowth w*routingAllowance w := by
    have hd1 : (6/5:ℝ) ≤ d := by norm_num [d]
    have hhh := mul_le_mul_of_nonneg_left hg1 hd.le
    exact mul_le_mul_of_nonneg_right (hd1.trans (by simpa only [mul_one] using hhh)) ha.le
  have hmax := max_le hB hK
  have hprod := mul_le_mul_of_nonneg_right hcap (mul_nonneg hg.le ha.le)
  have he : (2:ℝ)^((s-alpha)*w-growth*(w-wA))*teamGrowth w*routingAllowance w=(2:ℝ)^(s*w) := by
    unfold teamGrowth routingAllowance
    rw [←rpow_add (by norm_num : (0:ℝ)<2),←rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hlin : 16384*(d*teamGrowth w*routingAllowance w) ≤ comparisonExpansion w := by
    unfold comparisonExpansion
    calc
      _ = (16384*d)*(teamGrowth w*routingAllowance w) := by ring
      _ ≤ ((2:ℝ)^((s-alpha)*w-growth*(w-wA))*comparison_bank)*
        (teamGrowth w*routingAllowance w) := hprod
      _ = _ := by rw [←he]; ring
  exact (mul_le_mul_of_nonneg_left hmax (by norm_num)).trans hlin

theorem growing_hard_port_capacity {w : ℝ} (hw : wA ≤ w) :
    2*(routingTeamSize w:ℝ) ≤ comparisonExpansion w/128 := by
  have hb := growing_comparison_capacity hw
  have hm : (routingTeamSize w:ℝ) ≤ max (routingTeamSize w:ℝ) ((6/5)*routingAllowance w) := le_max_left _ _
  have hn : (0:ℝ) ≤ routingTeamSize w := Nat.cast_nonneg _
  linarith only [hb,hm,hn]

end
end Cycle12.Global12
