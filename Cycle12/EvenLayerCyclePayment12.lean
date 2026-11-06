import Cycle12.EvenVariableLayers12
import Cycle12.LayerCyclePayment
import Cycle12.OverlapProduct

namespace Cycle12
open Finset SimpleGraph Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem even_past_cycles_payment (d : EvenEntropyScaleData) (s : SplitSystem V)
    (j k : ℕ) (L : List (AssignedPiece V)) {mass : ℝ}
    (hvalid : ∀ i<k, d.valid (j+i))
    (hdegree : ∀ i<k, 0≤d.degree (j+i))
    (hbound : ∀ i<k, ∀ P∈advance s j i L, EvenEntropyStageBounds (s (j+i) P)
      (d.degree (j+i)) (d.cycleLength (j+i)) (d.boxOrder (j+i)) (d.expansion (j+i)))
    (hmass : ∀ i<k, vertexMass (advance s j i L) ≤ mass) :
    ((pastCycles s j k L).length:ℝ)≤
      mass*∑ i∈Finset.range k, d.degree (j+i)/(2*d.cycleLength (j+i)) := by
  rw [past_cycles_length,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hik := Finset.mem_range.mp hi
  have hpos : 0≤d.degree (j+i)/(2*d.cycleLength (j+i)) :=
    div_nonneg (hdegree i hik) (by have := d.cycle_pos (j+i) (hvalid i hik); linarith)
  have hh := even_variable_level_cycles d s (j+i) (advance s j i L) (hvalid i hik) (hbound i hik)
  exact hh.trans (by simpa only [mul_comm mass] using
    mul_le_mul_of_nonneg_left (hmass i hik) hpos)

end
end Cycle12
