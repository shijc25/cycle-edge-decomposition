import Cycle12.FoldPotentialPayments.Phase00
import Cycle12.FoldPotentialPayments.Phase01
import Cycle12.FoldPotentialPayments.Phase02
import Cycle12.FoldPotentialPayments.Phase03
import Cycle12.FoldPotentialPayments.Phase04
import Cycle12.FoldPotentialPayments.Phase05
import Cycle12.FoldPotentialPayments.Phase06
import Cycle12.FoldPotentialPayments.Phase07
import Cycle12.FoldPotentialPayments.Phase08
import Cycle12.FoldPotentialPayments.Phase09
import Cycle12.FoldPotentialPayments.Phase10
import Cycle12.FoldPotentialPayments.Phase11
import Cycle12.FoldPotentialPayments.Phase12
import Cycle12.FoldPotentialPayments.Phase13
import Cycle12.FoldPotentialPayments.Phase14
import Cycle12.FoldPotentialPayments.Phase15
import Cycle12.FoldPotentialPayments.Phase16
import Cycle12.FoldPotentialPayments.Phase17
import Cycle12.FoldPotentialPayments.Phase18
import Cycle12.FoldPotentialPayments.Phase19
import Cycle12.FoldPotentialPayments.Phase20
import Cycle12.FoldPotentialPayments.Phase21
import Cycle12.FoldPotentialPayments.Phase22
import Cycle12.FoldPotentialPayments.Phase23
import Cycle12.FoldPotentialPayments.Phase24
import Cycle12.FoldPotentialPayments.Phase25
import Cycle12.FoldPotentialPayments.Phase26
import Cycle12.FoldPotentialPayments.Phase27
import Cycle12.FoldPotentialPayments.Phase28
import Cycle12.FoldPotentialPayments.Phase29
import Cycle12.FoldPotentialPayments.Phase30
import Cycle12.FoldPotentialPayments.Phase31
import Cycle12.FoldPotentialPayments.Phase32
import Cycle12.FoldPotentialPayments.Phase33
import Cycle12.FoldPotentialPayments.Phase34
import Cycle12.FoldPotentialPayments.Phase35
import Cycle12.FoldPotentialPayments.Phase36
import Cycle12.FoldPotentialPayments.Phase37
import Cycle12.FoldPotentialPayments.Phase38
import Cycle12.FoldPotentialPayments.Phase39
import Cycle12.ActiveFoldScale12
import Cycle12.GlobalFoldLedger12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 Real Finset
open OAI.ErdosGallai.Scale
noncomputable section
set_option maxHeartbeats 2000000

/-- All forty phases, every finite row, and the infinite constant-threshold tails. -/
theorem all_phase_fold_coefficients (p : Fin 40) {t : ℕ} (ht : 3≤t) {w : ℝ}
    (hw : phaseLower p/theta2^(t-3)≤w) :
    foldMassCoefficient (foldingThreshold p t) w≤0 := by
  fin_cases p
  · change foldMassCoefficient (Cycle12.Phase00.threshold t) w≤0
    apply FoldPayment00.all_scales ht
    norm_num [phaseLower,PhaseMass00.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase01.threshold t) w≤0
    apply FoldPayment01.all_scales ht
    norm_num [phaseLower,PhaseMass01.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase02.threshold t) w≤0
    apply FoldPayment02.all_scales ht
    norm_num [phaseLower,PhaseMass02.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase03.threshold t) w≤0
    apply FoldPayment03.all_scales ht
    norm_num [phaseLower,PhaseMass03.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase04.threshold t) w≤0
    apply FoldPayment04.all_scales ht
    norm_num [phaseLower,PhaseMass04.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase05.threshold t) w≤0
    apply FoldPayment05.all_scales ht
    norm_num [phaseLower,PhaseMass05.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase06.threshold t) w≤0
    apply FoldPayment06.all_scales ht
    norm_num [phaseLower,PhaseMass06.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase07.threshold t) w≤0
    apply FoldPayment07.all_scales ht
    norm_num [phaseLower,PhaseMass07.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase08.threshold t) w≤0
    apply FoldPayment08.all_scales ht
    norm_num [phaseLower,PhaseMass08.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase09.threshold t) w≤0
    apply FoldPayment09.all_scales ht
    norm_num [phaseLower,PhaseMass09.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase10.threshold t) w≤0
    apply FoldPayment10.all_scales ht
    norm_num [phaseLower,PhaseMass10.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase11.threshold t) w≤0
    apply FoldPayment11.all_scales ht
    norm_num [phaseLower,PhaseMass11.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase12.threshold t) w≤0
    apply FoldPayment12.all_scales ht
    norm_num [phaseLower,PhaseMass12.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase13.threshold t) w≤0
    apply FoldPayment13.all_scales ht
    norm_num [phaseLower,PhaseMass13.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase14.threshold t) w≤0
    apply FoldPayment14.all_scales ht
    norm_num [phaseLower,PhaseMass14.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase15.threshold t) w≤0
    apply FoldPayment15.all_scales ht
    norm_num [phaseLower,PhaseMass15.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase16.threshold t) w≤0
    apply FoldPayment16.all_scales ht
    norm_num [phaseLower,PhaseMass16.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase17.threshold t) w≤0
    apply FoldPayment17.all_scales ht
    norm_num [phaseLower,PhaseMass17.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase18.threshold t) w≤0
    apply FoldPayment18.all_scales ht
    norm_num [phaseLower,PhaseMass18.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase19.threshold t) w≤0
    apply FoldPayment19.all_scales ht
    norm_num [phaseLower,PhaseMass19.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase20.threshold t) w≤0
    apply FoldPayment20.all_scales ht
    norm_num [phaseLower,PhaseMass20.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase21.threshold t) w≤0
    apply FoldPayment21.all_scales ht
    norm_num [phaseLower,PhaseMass21.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase22.threshold t) w≤0
    apply FoldPayment22.all_scales ht
    norm_num [phaseLower,PhaseMass22.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase23.threshold t) w≤0
    apply FoldPayment23.all_scales ht
    norm_num [phaseLower,PhaseMass23.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase24.threshold t) w≤0
    apply FoldPayment24.all_scales ht
    norm_num [phaseLower,PhaseMass24.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase25.threshold t) w≤0
    apply FoldPayment25.all_scales ht
    norm_num [phaseLower,PhaseMass25.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase26.threshold t) w≤0
    apply FoldPayment26.all_scales ht
    norm_num [phaseLower,PhaseMass26.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase27.threshold t) w≤0
    apply FoldPayment27.all_scales ht
    norm_num [phaseLower,PhaseMass27.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase28.threshold t) w≤0
    apply FoldPayment28.all_scales ht
    norm_num [phaseLower,PhaseMass28.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase29.threshold t) w≤0
    apply FoldPayment29.all_scales ht
    norm_num [phaseLower,PhaseMass29.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase30.threshold t) w≤0
    apply FoldPayment30.all_scales ht
    norm_num [phaseLower,PhaseMass30.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase31.threshold t) w≤0
    apply FoldPayment31.all_scales ht
    norm_num [phaseLower,PhaseMass31.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase32.threshold t) w≤0
    apply FoldPayment32.all_scales ht
    norm_num [phaseLower,PhaseMass32.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase33.threshold t) w≤0
    apply FoldPayment33.all_scales ht
    norm_num [phaseLower,PhaseMass33.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase34.threshold t) w≤0
    apply FoldPayment34.all_scales ht
    norm_num [phaseLower,PhaseMass34.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase35.threshold t) w≤0
    apply FoldPayment35.all_scales ht
    norm_num [phaseLower,PhaseMass35.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase36.threshold t) w≤0
    apply FoldPayment36.all_scales ht
    norm_num [phaseLower,PhaseMass36.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase37.threshold t) w≤0
    apply FoldPayment37.all_scales ht
    norm_num [phaseLower,PhaseMass37.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase38.threshold t) w≤0
    apply FoldPayment38.all_scales ht
    norm_num [phaseLower,PhaseMass38.lo] at hw ⊢
    exact hw
  · change foldMassCoefficient (Cycle12.Phase39.threshold t) w≤0
    apply FoldPayment39.all_scales ht
    norm_num [phaseLower,PhaseMass39.lo] at hw ⊢
    exact hw

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Once the actual packing supplies its physical cost, every numerical
and scale requirement of the active fold is discharged. This does not
assume or claim that the remaining physical graph construction is proved. -/
theorem actual_fold_ledger_payment {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) (F : ActualFoldStage12 L i) (p : Fin 40)
    (hscale : phaseLower p/theta2^((L.stopIndex+3-i)-3)≤logScale (originalLog V) L.stopIndex i)
    (hfold : (∑ j : Fin (L.stopIndex+3) with j.val ≤ i+2, L.coreMass j.val)≤
      foldingThreshold p (L.stopIndex+3-i)*L.coreMass i)
    {cost : ℝ}
    (hcost : let w := logScale (originalLog V) L.stopIndex i
      cost≤(1+C*eta)*(∑ j : Fin (L.stopIndex+3) with j.val ≤ i+2, L.coreMass j.val)+
        sigma*L.coreMass i+(1/2048:ℝ)*L.coreMass i+
        (batchFee w+groupFee w)*F.activeMass+
        C*globalPhi (b*w)*(F.batchMass-kappa*F.activeMass)+(lossJ w+lossV w)*Fintype.card V) :
    cost≤C*orderPotential (Fintype.card V)*Fintype.card V := by
  have hw := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hpaid := physical_fold_ledger_payment hw (Nat.cast_nonneg (Fintype.card V))
    (F.activeMass_lower hi) (F.activeMass_upper hi) (F.batchMass_upper hi) hfold hcost
  have hcoef := all_phase_fold_coefficients p (by omega : 3≤L.stopIndex+3-i) hscale
  have hh := folding_potential_payment hw (Nat.cast_nonneg (Fintype.card V))
    (L.coreMass_nonneg i) (L.active_log_upper hi) hcoef hpaid
  simpa only [orderPotential,originalLog] using hh

end
end Cycle12.Even12
