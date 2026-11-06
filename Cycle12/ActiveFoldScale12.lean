import Cycle12.GlobalNoFoldBranch12
import Cycle12.ActualBatchPotential12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 Real Finset
open OAI.ErdosGallai.Scale
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The actual scale at a selected fold satisfies the exact phase
lower bound used by the numerical half-line certificates. -/
theorem EvenScaleLayers12.active_phase_scale {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) (p : Fin 40)
    (hp : phaseLower p≤theta2^L.stopIndex*originalLog V) :
    phaseLower p/theta2^((L.stopIndex+3-i)-3)≤logScale (originalLog V) L.stopIndex i := by
  have hexp : (L.stopIndex+3-i)-3=L.stopIndex-i := by omega
  rw [hexp]
  apply (div_le_iff₀ (pow_pos (by norm_num [theta2]) _)).mpr
  unfold logScale
  rw [three_rate_regular _ _ _ _ (by omega)]
  have he : (theta2^i*originalLog V)*theta2^(L.stopIndex-i)=theta2^L.stopIndex*originalLog V := by
    rw [mul_right_comm,←pow_add,Nat.add_sub_of_le hi]
  rwa [he]

/-- Selecting a fold exposes the actual prefix inequality and scale
without imposing any new graph or numerical hypothesis. -/
theorem EvenScaleLayers12.active_fold_witness {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    (hf : hasActiveFold L) :
    ∃ (p : Fin 40) (i : ℕ),i≤L.stopIndex ∧ 0<L.coreMass i ∧
      phaseLower p/theta2^((L.stopIndex+3-i)-3)≤logScale (originalLog V) L.stopIndex i ∧
      (∑ j : Fin (L.stopIndex+3) with j.val ≤ i+2, L.coreMass j.val)≤
        foldingThreshold p (L.stopIndex+3-i)*L.coreMass i := by
  obtain ⟨p,hp,_,j,hpos,hj,hfold⟩ := hf
  have hi : j.val≤L.stopIndex := by omega
  exact ⟨p,j.val,hi,hpos,L.active_phase_scale hi p hp,hfold⟩

end
end Cycle12.Even12
