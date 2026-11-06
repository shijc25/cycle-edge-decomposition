import Cycle12.BiasedBankSplit
import Cycle12.ScaleHalflines12

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A generous linear lower envelope pays the biased all-cut union bound. -/
theorem bank_linear_halfline {w : ℝ} (hw : w0 ≤ w) :
    33554432*w ≤ (2:ℝ)^(s*w) := by
  have he : (2:ℝ)^(40:ℝ) ≤ (2:ℝ)^(s*w0) :=
    rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [s,w0])
  have hb : (0:ℝ)+33554432*w0 ≤ (2:ℝ)^(s*w0) :=
    (show (0:ℝ)+33554432*w0 ≤ (2:ℝ)^(40:ℝ) by norm_num [w0]).trans he
  have hl := log_two_lower
  have hs : (33554432:ℝ) ≤ log 2*s*(0+33554432*w0) := by
    norm_num [s,w0]
    nlinarith only [hl]
  simpa only [zero_add] using linear_power_envelope (by norm_num [w0]) hb hs hw

theorem bank_preparation_scale_bounds {w n : ℝ} (hw : w0 ≤ w)
    (hn : 0 < n) (horder : n ≤ (2:ℝ)^(rho*w)) :
    4096 < (2:ℝ)^(s*w) ∧
    2048*n < ((2:ℝ)^(s*w))^2 ∧
    4*log n+8 ≤ ((1023/1024)*(2:ℝ)^(s*w))/524288 := by
  have hw1 : 1 ≤ w := (show (1:ℝ) ≤ w0 by norm_num [w0]).trans hw
  have hlin := bank_linear_halfline hw
  have hExp : (12:ℝ) ≤ (2*s-rho)*w := by
    have hp := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*s-rho by norm_num [s,rho])
    have hbase : (12:ℝ) ≤ (2*s-rho)*w0 := by norm_num [s,rho,w0]
    exact hbase.trans hp
  have hpow : (2048:ℝ) < (2:ℝ)^((2*s-rho)*w) :=
    (show (2048:ℝ) < (2:ℝ)^(12:ℝ) by norm_num).trans_le
      (rpow_le_rpow_of_exponent_le (by norm_num) hExp)
  have hp := mul_lt_mul_of_pos_right hpow (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (rho*w))
  have he : (2:ℝ)^((2*s-rho)*w)*(2:ℝ)^(rho*w)=((2:ℝ)^(s*w))^2 := by
    rw [←rpow_add (by norm_num : (0:ℝ)<2),←rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  rw [he] at hp
  have hlog := log_le_log hn horder
  rw [log_rpow (by norm_num : (0:ℝ)<2)] at hlog
  have hl : log 2 ≤ 1 := by have hh := Cycle13.log_two_24_digits.2; linarith only [hh]
  have hcoef : 0 ≤ rho*w := mul_nonneg (by norm_num [rho]) (by linarith only [hw1])
  have hm := mul_le_mul_of_nonneg_left hl hcoef
  have hr : rho*w ≤ 2*w := mul_le_mul_of_nonneg_right (by norm_num [rho] : rho ≤ 2) (by linarith only [hw1])
  refine ⟨by linarith only [hlin,hw1],by linarith only [hp,horder],?_⟩
  nlinarith only [hlog,hm,hr,hlin,hw1]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual unequal banks at every coefficient-12 scale. -/
theorem prepare_banks_at_scale [Nonempty V] (G : SimpleGraph V)
    {w : ℝ} (hn : 2 ≤ Fintype.card V) (hw : w0 ≤ w)
    (horder : (Fintype.card V:ℝ) ≤ (2:ℝ)^(rho*w))
    (hexp : OAI.ErdosGallai.CutExpansion G ((2:ℝ)^(s*w))) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V-componentCount G ∧
      (∀ v, (F.degree v:ℝ) < (2:ℝ)^(s*w)/1024) ∧
      (∀ v, Even ((G\F).degree v)) ∧
      ∃ ω : Sym2 V → Bool,
        OAI.ErdosGallai.CutExpansion (splitBank (G\F) ω true) (router_bank*(2:ℝ)^(s*w)) ∧
        OAI.ErdosGallai.CutExpansion (splitBank (G\F) ω false) (completion_bank*(2:ℝ)^(s*w)) ∧
        Disjoint (splitBank (G\F) ω true) (splitBank (G\F) ω false) ∧
        splitBank (G\F) ω true ⊔ splitBank (G\F) ω false=G\F := by
  have hn0 : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  obtain ⟨hlin,hquad,hlog⟩ := bank_preparation_scale_bounds hw hn0 horder
  exact prepare_biased_expander_banks G hn hlin hquad hexp hlog

end
end Cycle12.Global12
