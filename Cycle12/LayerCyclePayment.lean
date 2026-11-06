import Cycle12.VariableScaleLayers
import Cycle12.OverlapProduct

namespace Cycle12
open Finset SimpleGraph Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem past_cycles_length (s : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V)) :
    ((pastCycles s j k L).length:ℝ)=
      ∑ i∈Finset.range k, ((levelCycles s (j+i) (advance s j i L)).length:ℝ) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih => simp only [pastCycles,List.length_append,Nat.cast_add,Finset.sum_range_succ,ih]

theorem past_cycles_payment (d : EntropyScaleData) (s : SplitSystem V)
    (j k : ℕ) (L : List (AssignedPiece V)) {mass : ℝ}
    (hvalid : ∀ i<k, d.valid (j+i))
    (hdegree : ∀ i<k, 0≤d.degree (j+i))
    (hbound : ∀ i<k, ∀ P∈advance s j i L, EntropyStageBounds (s (j+i) P)
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
  have hh := variable_level_cycles d s (j+i) (advance s j i L) (hvalid i hik) (hbound i hik)
  exact hh.trans (by simpa only [mul_comm mass] using
    mul_le_mul_of_nonneg_left (hmass i hik) hpos)

theorem variable_mass_of_overlap_sum (s : SplitSystem V) (j k : ℕ)
    (L : List (AssignedPiece V)) (a : ℕ → ℝ) {Z : ℝ}
    (ha : ∀ i<k, 0≤a (j+i))
    (hsum : ∑ i∈Finset.range k, a (j+i)≤Z) (hZ : Z<1)
    (hb : ∀ i<k, ∀ P∈advance s j i L,
      vertexMass (s (j+i) P).boxes≤(1+a (j+i))*P.vertices.card) :
    vertexMass (advance s j k L)≤vertexMass L/(1-Z) := by
  have hp := overlap_product_bound (Finset.range k) (fun i => a (j+i))
    (fun i hi => ha i (Finset.mem_range.mp hi)) hsum hZ
  have hh := variable_advance_mass s j k L (fun i => 1+a i)
    (fun i hi => by linarith [ha i hi]) hb
  exact hh.trans (by simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left hp (vertexMass_nonneg L))

end
end Cycle12
