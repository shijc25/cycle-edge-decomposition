import Cycle12.EvenTerminalPacking12
import Cycle12.FiniteCutoffBounds
import Cycle12.PhaseMassCertificates.Phase05

namespace Cycle12.Even12.Phase05
open Cycle12.Global12 Cycle12.Global12.PhaseMass05 Cycle13 Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

variable {V : Type} [Fintype V] [DecidableEq V]

theorem actual_kept_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (hphase : lo ≤ theta2^L.stopIndex*originalLog V)
    (hfold : ¬∃ i : Fin (L.stopIndex+3), 0 < L.coreMass i.val ∧ i.val+2 < L.stopIndex+3 ∧
      (∑ j : Fin (L.stopIndex+3) with j.val ≤ i.val+2, L.coreMass j.val) ≤
        Cycle12.Phase05.threshold (L.stopIndex+3-i.val)*L.coreMass i.val) :
    vertexMass (pastPieces L.splitter 0 (L.stopIndex+1) [originalPiece G]) ≤
      (Fintype.card V:ℝ)*(sequenceTail Cycle12.Phase05.sequence 3-
        sequenceTail Cycle12.Phase05.sequence (L.stopIndex+4)) := by
  apply L.kept_mass_of_no_fold (by norm_num [lo]) hphase masses.1 masses.2.2.1
    Cycle12.Phase05.sequence Cycle12.Phase05.threshold
  · have he : Cycle12.Phase05.sequence 1=mass1 := by
      norm_num [Cycle12.Phase05.sequence,splice,Cycle12.Phase05.initial,mass1]
    rw [he]
    exact masses.2.1
  · have he : Cycle12.Phase05.sequence 2=mass2 := by
      norm_num [Cycle12.Phase05.sequence,splice,Cycle12.Phase05.initial,mass2]
    rw [he]
    exact masses.2.2.2.1
  · exact fun n => (Cycle12.Phase05.positive n).le
  · exact fun n _ => Cycle12.Phase05.positive n
  · exact Cycle12.Phase05.summable
  · exact Cycle12.Phase05.infinite_majorant
  · exact hfold

theorem actual_degree {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (hphase : lo ≤ theta2^L.stopIndex*originalLog V)
    (hupper : theta2^L.stopIndex*originalLog V ≤ hi) :
    2*(edgeCount (stoppedRemainder L):ℝ) ≤ (2:ℝ)^cutoff*Fintype.card V := by
  have hh := stopped_phase_degree L (by norm_num [lo]) hphase hupper masses.2.2.2.2.1
  have hm := mul_le_mul_of_nonneg_right masses.2.2.2.2.2
    (rpow_nonneg (by norm_num : (0:ℝ)≤2) (theta2*hi))
  exact hh.trans (mul_le_mul_of_nonneg_right (hm.trans phase_degree_cap) (Nat.cast_nonneg _))

theorem actual_cycle_fee {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (hphase : lo ≤ theta2^L.stopIndex*originalLog V) :
    ((pastCycles L.splitter 0 (L.stopIndex+1) [originalPiece G]).length:ℝ) ≤
      cycleFee*Fintype.card V := by
  exact (kept_long_cycles_phase_bound L (by norm_num [lo]) hphase masses.2.2.2.2.1).trans
    (mul_le_mul_of_nonneg_right phase_cycle_cap (Nat.cast_nonneg _))

/-- The finite-average theorem is applied to the actual parity-corrected remainder. -/
theorem stopped_packing {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (hphase : lo≤theta2^L.stopIndex*originalLog V)
    (hupper : theta2^L.stopIndex*originalLog V≤hi) :
    ∃ P : CyclePacking (stoppedRemainder L),
      P.weight≤(FiniteChains.Chain071.costBound:ℝ)*Fintype.card V := by
  have hd := actual_degree L hphase hupper
  have he : edgeCount (stoppedRemainder L)=(stoppedRemainder L).edgeSet.ncard := by
    simp only [edgeCount,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']
  rw [he] at hd
  exact FiniteAverageBounds.cutoff071 (stoppedRemainder L) (by
    simpa only [cutoff,Rat.cast_div,Rat.cast_ofNat] using hd)

theorem terminal_no_fold {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (ih : ∀ m, m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight≤C*m)
    (hphase : lo≤theta2^L.stopIndex*originalLog V)
    (hupper : theta2^L.stopIndex*originalLog V≤hi)
    (hfold : ¬∃ i : Fin (L.stopIndex+3), 0<L.coreMass i.val ∧ i.val+2<L.stopIndex+3 ∧
      (∑ j : Fin (L.stopIndex+3) with j.val ≤ i.val+2, L.coreMass j.val)≤
        Cycle12.Phase05.threshold (L.stopIndex+3-i.val)*L.coreMass i.val) :
    ∃ Q : CyclePacking G, Q.weight≤
      ((FiniteChains.Chain071.costBound:ℝ)+
        (1+C*eta)*(sequenceTail Cycle12.Phase05.sequence 3-
          sequenceTail Cycle12.Phase05.sequence (L.stopIndex+4))+cycleFee)*Fintype.card V := by
  obtain ⟨PH,hPH⟩ := stopped_packing L hphase hupper
  obtain ⟨Q,hQ⟩ := L.terminal_packing_from_ih ih PH hPH
  have hm := mul_le_mul_of_nonneg_left (actual_kept_mass L hphase hfold)
    (by norm_num [C,eta] : (0:ℝ)≤1+C*eta)
  have hj := actual_cycle_fee L hphase
  exact ⟨Q,by nlinarith only [hQ,hm,hj]⟩

end
end Cycle12.Even12.Phase05
