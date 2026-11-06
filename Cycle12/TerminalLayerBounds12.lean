import Cycle12.PhaseLayerMass12

namespace Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def stoppedRemainder {G : SimpleGraph V} (L : ScaleLayers12 G) : SimpleGraph V :=
  graphUnion ((advance L.splitter 0 (L.stopIndex+1) [originalPiece G]).map AssignedPiece.graph)

theorem stopped_phase_degree {G : SimpleGraph V} (L : ScaleLayers12 G)
    {A H : ℝ} (hA : 0<A) (hphase : A≤theta2^L.stopIndex*originalLog V)
    (hupper : theta2^L.stopIndex*originalLog V ≤ H) (hZ : phaseOverlap3 A<1) :
    2*(edgeCount (stoppedRemainder L):ℝ) ≤ phaseMass3 A*(2:ℝ)^(theta2*H)*Fintype.card V := by
  have hlog : logScale (originalLog V) L.stopIndex (L.stopIndex+1) ≤ theta2*H := by
    unfold logScale
    rw [three_rate_regular _ _ _ _ le_rfl,pow_succ]
    have hh := mul_le_mul_of_nonneg_left hupper (by norm_num [theta2] : 0≤theta2)
    nlinarith only [hh]
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hlog
  have hdeg : ∀ P∈advance L.splitter 0 (L.stopIndex+1) [originalPiece G],
      2*(edgeCount P.graph:ℝ) ≤ (2:ℝ)^(theta2*H)*P.vertices.card := by
    intro P hP
    exact (L.degrees _ (by omega) P hP).trans
      (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  have hm := phase_layer_mass3 L hA hphase hZ (i:=L.stopIndex+1) le_rfl
  have hh := stopped_remainder_degree L.splitter 0 (L.stopIndex+1) (originalPiece G)
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (theta2*H)) hdeg hm
  simpa only [stoppedRemainder,originalPiece,Finset.card_univ,mul_comm (phaseMass3 A)] using hh

theorem kept_long_cycles_phase_bound {G : SimpleGraph V} (L : ScaleLayers12 G)
    {A : ℝ} (hA : 0<A) (hphase : A≤theta2^L.stopIndex*originalLog V)
    (hZ : phaseOverlap3 A<1) :
    ((pastCycles L.splitter 0 (L.stopIndex+1) [originalPiece G]).length:ℝ) ≤
      phaseMass3 A*scaleMassSeries theta2 (eps*A)/2*Fintype.card V := by
  let d := scaleData (originalLog V) L.stopIndex L.initial_log_pos.le L.phase_lower
  let mass := phaseMass3 A*Fintype.card V
  have hvalid : ∀ j < L.stopIndex+1, d.valid (0+j) := by
    intro j hj
    change 0+j<L.stopIndex+3
    omega
  have hdegree : ∀ j < L.stopIndex+1, 0≤d.degree (0+j) := by
    intro j _
    exact Real.rpow_nonneg (by norm_num) _
  have hbounds : ∀ j < L.stopIndex+1, ∀ P∈advance L.splitter 0 j [originalPiece G],
      EntropyStageBounds (L.splitter (0+j) P) (d.degree (0+j)) (d.cycleLength (0+j))
        (d.boxOrder (0+j)) (d.expansion (0+j)) := by
    intro j hj
    simpa only [d,scaleData,Nat.zero_add] using L.bounds j (by omega)
  have hmass : ∀ j < L.stopIndex+1, vertexMass (advance L.splitter 0 j [originalPiece G]) ≤ mass :=
    fun j hj => phase_layer_mass3 L hA hphase hZ (by omega)
  have hc := past_cycles_payment d L.splitter 0 (L.stopIndex+1) [originalPiece G]
    hvalid hdegree hbounds hmass
  have he : (∑ j∈Finset.range (L.stopIndex+1), d.degree (0+j)/(2*d.cycleLength (0+j))) =
      (∑ j∈Finset.range (L.stopIndex+1), (2:ℝ)^(-eps*(theta2^j*originalLog V)))/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [d,scaleData,Nat.zero_add]
    rw [power_cycle_charge]
    unfold logScale
    rw [three_rate_regular _ _ _ _ (by have := Finset.mem_range.mp hj; omega)]
  rw [he] at hc
  have hs := geometric_scale_sum_bound (by norm_num [theta2]) (by norm_num [theta2])
    hA (show 0<eps by norm_num [eps]) L.stopIndex hphase
  have hm0 : 0 ≤ mass := mul_nonneg
    (by unfold phaseMass3; positivity [sub_pos.mpr hZ]) (Nat.cast_nonneg _)
  have hp := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ)≤2)) hm0
  apply hc.trans
  convert hp using 1 <;> dsimp [mass] <;> ring

end
end Cycle12.Global12
