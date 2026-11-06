import Cycle12.TerminalPackingAssembly
import Cycle12.InfinitePrefix

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def ScaleLayers12.coreMass {G : SimpleGraph V} (L : ScaleLayers12 G) (i : ℕ) : ℝ :=
  vertexMass (levelPieces L.splitter i (advance L.splitter 0 i [originalPiece G]))

theorem ScaleLayers12.coreMass_nonneg {G : SimpleGraph V} (L : ScaleLayers12 G) (i : ℕ) :
    0 ≤ L.coreMass i := vertexMass_nonneg _

theorem ScaleLayers12.coreMass_le_frontier {G : SimpleGraph V} (L : ScaleLayers12 G) (i : ℕ) :
    L.coreMass i ≤ vertexMass (advance L.splitter 0 (i+1) [originalPiece G]) := by
  simpa only [ScaleLayers12.coreMass,advance_succ,Nat.zero_add] using
    levelPieces_mass L.splitter i (advance L.splitter 0 i [originalPiece G])

theorem ScaleLayers12.kept_mass_sum {G : SimpleGraph V} (L : ScaleLayers12 G) :
    vertexMass (pastPieces L.splitter 0 (L.stopIndex+1) [originalPiece G]) =
      ∑ i : Fin (L.stopIndex+3) with i.val+2 < L.stopIndex+3, L.coreMass i.val := by
  rw [pastPieces_mass]
  simp only [Nat.zero_add]
  change (∑ i∈range (L.stopIndex+1), L.coreMass i) = _
  symm
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj he
    exact Fin.ext he
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨j,by omega⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp; omega⟩
  · intro i hi
    rfl


/-- The unequal two terminal bounds are attached to actual extracted cores. -/
theorem ScaleLayers12.core_boundary {G : SimpleGraph V} (L : ScaleLayers12 G)
    {A : ℝ} (hA : 0 < A) (hphase : A ≤ theta2^L.stopIndex*originalLog V)
    (hZ1 : phaseOverlap1 A < 1) (hZ2 : phaseOverlap2 A < 1)
    (u : ℕ → ℝ) (hu1 : phaseMass1 A ≤ u 1) (hu2 : phaseMass2 A ≤ u 2) :
    ∀ i : Fin (L.stopIndex+3), L.stopIndex+3 ≤ i.val+2 →
      L.coreMass i.val ≤ (Fintype.card V:ℝ)*u (L.stopIndex+3-i.val) := by
  intro i hi
  have hcases : i.val=L.stopIndex+1 ∨ i.val=L.stopIndex+2 := by have := i.isLt; omega
  rcases hcases with he | he
  · have hm := phase_layer_mass2 L hA hphase hZ2 (i:=i.val+1) (by omega)
    have hh := (L.coreMass_le_frontier i.val).trans hm
    have hup := mul_le_mul_of_nonneg_right hu2 (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
    have hind : L.stopIndex+3-i.val=2 := by omega
    rw [hind]
    exact hh.trans (by simpa only [mul_comm] using hup)
  · have hm := phase_layer_mass1 L hA hphase hZ1 (i:=i.val+1) (by omega)
    have hh := (L.coreMass_le_frontier i.val).trans hm
    have hup := mul_le_mul_of_nonneg_right hu1 (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
    have hind : L.stopIndex+3-i.val=1 := by omega
    rw [hind]
    exact hh.trans (by simpa only [mul_comm] using hup)

/-- In the no-fold branch the actual retained core mass includes the exact
unused infinite tail, without an extra global overlap multiplier. -/
theorem ScaleLayers12.kept_mass_of_no_fold {G : SimpleGraph V} (L : ScaleLayers12 G)
    {A : ℝ} (hA : 0 < A) (hphase : A ≤ theta2^L.stopIndex*originalLog V)
    (hZ1 : phaseOverlap1 A < 1) (hZ2 : phaseOverlap2 A < 1)
    (u P : ℕ → ℝ) (hu1 : phaseMass1 A ≤ u 1) (hu2 : phaseMass2 A ≤ u 2)
    (hu : ∀ n, 0 ≤ u n) (hup : ∀ n, 1 ≤ n → 0 < u n) (hs : Summable u)
    (hss : ∀ t, 2 < t → (∑' j : ℕ, u (j+(t-2))) ≤ P t*u t)
    (hfold : ¬∃ i : Fin (L.stopIndex+3), 0 < L.coreMass i.val ∧ i.val+2 < L.stopIndex+3 ∧
      (∑ j : Fin (L.stopIndex+3) with j.val ≤ i.val+2, L.coreMass j.val) ≤
        P (L.stopIndex+3-i.val)*L.coreMass i.val) :
    vertexMass (pastPieces L.splitter 0 (L.stopIndex+1) [originalPiece G]) ≤
      (Fintype.card V:ℝ)*(sequenceTail u 3-sequenceTail u (L.stopIndex+4)) := by
  rw [L.kept_mass_sum]
  exact terminal_mass_with_infinite_tail (by omega) (Nat.cast_nonneg _) (fun i => L.coreMass i.val)
    (fun i => L.coreMass_nonneg i.val) u P hu hup hs
    (L.core_boundary hA hphase hZ1 hZ2 u hu1 hu2) hss hfold

end
end Cycle12.Global12
