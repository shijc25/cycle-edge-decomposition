import Cycle12.SampledEulerianCompletion12
import Cycle12.BalancedCompletionBanks12
import Cycle12.ReservoirScaleGates12
import Cycle12.Foundations.ExpanderOrderBound

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

set_option maxHeartbeats 2000000

/-- The balanced cut of a simple graph supplies the sampler's order ratio;
it is derived from expansion rather than added as a new global premise. -/
theorem balanced_sample_order_ratio (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hh : 512 ≤ h)
    (hexp : OAI.ErdosGallai.CutExpansion G h) :
    4*((511/1024)*h) ≤ (Fintype.card V:ℝ) := by
  have hb := cutExpansion_twice_le_order_add_one G hn hexp
  linarith only [hb,hh]

/-- At every required global scale the completion is a real graph
construction, with all sample/router inequalities discharged and residue
order strictly below eta*n. -/
theorem even_completion_at_scale [Nonempty V] (G : SimpleGraph V) {w : ℝ}
    (hn : 2 ≤ Fintype.card V) (hw : w0 ≤ w)
    (horder : (Fintype.card V:ℝ) ≤ (2:ℝ)^(rho*w))
    (hexp : OAI.ErdosGallai.CutExpansion G ((1023/1024)*(2:ℝ)^(s*w)))
    (heven : ∀ v, Even (G.degree v)) :
    ∃ U : Finset V, (U.card:ℝ) < eta*Fintype.card V ∧
      ∃ P : CyclePacking G, P.count ≤ Fintype.card V ∧
        ∀ x y, P.residue.Adj x y → x ∈ U ∧ y ∈ U := by
  have hn0 : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  obtain ⟨hpow,_,hbanklog⟩ := bank_preparation_scale_bounds hw hn0 horder
  have hh : 512 ≤ (1023/1024)*(2:ℝ)^(s*w) := by linarith only [hpow]
  have hh0 : 0 < (1023/1024)*(2:ℝ)^(s*w) := by linarith only [hh]
  obtain ⟨H₁,H₂,h₁,h₂,hdis,hexp₁,hexp₂⟩ := balanced_completion_banks G hn hh0 hexp hbanklog
  have hbank : (511/1024)*((1023/1024)*(2:ℝ)^(s*w)) = comparison_bank*(2:ℝ)^(s*w) := by
    norm_num only [comparison_bank]
    ring
  rw [hbank] at hexp₁ hexp₂
  have hratio := balanced_sample_order_ratio G hn hh hexp
  rw [hbank] at hratio
  obtain ⟨hz,hl,_,hsq,hscale⟩ := balanced_reservoir_scale_gates hw hn0 horder
  let prob : unitInterval := ⟨p,by norm_num [p]⟩
  have hp : 0 < (prob:ℝ) := by norm_num [prob,p]
  have hp3 : 3*(prob:ℝ) ≤ 1 := by norm_num [prob,p]
  obtain ⟨U,hU,P,hP,hres⟩ := sampled_eulerian_completion G H₁ H₂ h₁ h₂ hdis heven
    (p:=prob) hp hp3 (mul_pos (by norm_num [comparison_bank] : (0:ℝ) < comparison_bank) (rpow_pos_of_pos (by norm_num) _)) hn hratio
    (by simpa only [prob] using hscale)
    (by simpa only [prob,mul_assoc] using hz)
    (by simpa only [prob,mul_assoc] using hl)
    (by simpa only [prob,mul_assoc] using hsq) hexp₁ hexp₂
  refine ⟨U,?_,P,hP,hres⟩
  convert hU using 1
  norm_num [prob,p,eta]

end
end Cycle12.Global12
