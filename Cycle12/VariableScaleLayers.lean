import Cycle12.EntropyScaleSplit
import OAI.Combinatorics.CycleDecomposition.ScaleDecomposition

namespace Cycle12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure EntropyScaleData where
  degree : ℕ → ℝ
  cycleLength : ℕ → ℝ
  boxOrder : ℕ → ℝ
  expansion : ℕ → ℝ
  valid : ℕ → Prop
  cycle_pos : ∀ i, valid i → 1≤cycleLength i
  room : ∀ i, valid i → cycleLength i+2<boxOrder i
  expansion_pos : ∀ i, valid i → 1≤expansion i
  expansion_le : ∀ i, valid i → expansion i≤boxOrder i
  next_degree : ∀ i, valid i →
    expansion i*(1+log (boxOrder i/expansion i)/log 2) ≤ degree (i+1)

def EntropyScaleData.overlap (d : EntropyScaleData) (i : ℕ) : ℝ :=
  2*d.cycleLength i/(d.boxOrder i-d.cycleLength i-2)

theorem EntropyScaleData.overlap_nonneg (d : EntropyScaleData) {i : ℕ}
    (hi : d.valid i) : 0≤d.overlap i := by
  have h1 := d.cycle_pos i hi
  have h2 := d.room i hi
  unfold EntropyScaleData.overlap
  exact div_nonneg (by linarith) (by linarith)

theorem exists_variable_entropy_splitter (d : EntropyScaleData) :
    ∃ s : SplitSystem V, ∀ i P, d.valid i →
      2*(edgeCount P.graph:ℝ)≤d.degree i*P.vertices.card →
      EntropyStageBounds (s i P) (d.degree i) (d.cycleLength i) (d.boxOrder i) (d.expansion i) := by
  have hex (i : ℕ) (P : AssignedPiece V) : ∃ s : StageSplit P, d.valid i →
      2*(edgeCount P.graph:ℝ)≤d.degree i*P.vertices.card →
      EntropyStageBounds s (d.degree i) (d.cycleLength i) (d.boxOrder i) (d.expansion i) := by
    by_cases hh : d.valid i ∧ 2*(edgeCount P.graph:ℝ)≤d.degree i*P.vertices.card
    · obtain ⟨s,hs⟩ := exists_entropy_stage_split P (d.cycle_pos i hh.1) (d.room i hh.1)
        (d.expansion_pos i hh.1) (d.expansion_le i hh.1) hh.2
      exact ⟨s,fun _ _ => hs⟩
    · exact ⟨StageSplit.trivial P,fun h1 h2 => False.elim (hh ⟨h1,h2⟩)⟩
  choose s hs using hex
  exact ⟨s,hs⟩

theorem variable_nextLayer_mass (s : SplitSystem V) (i : ℕ)
    (L : List (AssignedPiece V)) {a : ℝ}
    (h : ∀ P∈L, vertexMass (s i P).boxes≤a*P.vertices.card) :
    vertexMass (nextLayer s i L)≤a*vertexMass L := by
  induction L with
  | nil => simp [nextLayer]
  | cons P L ih =>
    have hp := h P (by simp)
    have ht := ih (fun Q hQ => h Q (by simp [hQ]))
    simp only [nextLayer,List.flatMap_cons,vertexMass_append,StageSplit.children_mass,
      vertexMass_cons] at ht ⊢
    nlinarith only [hp,ht]

theorem variable_advance_mass (s : SplitSystem V) (j k : ℕ)
    (L : List (AssignedPiece V)) (a : ℕ → ℝ)
    (ha : ∀ i<k, 0≤a (j+i))
    (hb : ∀ i<k, ∀ P∈advance s j i L, vertexMass (s (j+i) P).boxes≤a (j+i)*P.vertices.card) :
    vertexMass (advance s j k L)≤vertexMass L*∏ i∈Finset.range k, a (j+i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hm := variable_nextLayer_mass s (j+k) (advance s j k L) (hb k (by omega))
    have hi := mul_le_mul_of_nonneg_left
      (ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))) (ha k (by omega))
    rw [advance_succ,Finset.prod_range_succ]
    nlinarith only [hm,hi]

theorem variable_advance_degree (d : EntropyScaleData) (s : SplitSystem V)
    (hs : ∀ i P, d.valid i → 2*(edgeCount P.graph:ℝ)≤d.degree i*P.vertices.card →
      EntropyStageBounds (s i P) (d.degree i) (d.cycleLength i) (d.boxOrder i) (d.expansion i))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hdeg : ∀ P∈L, 2*(edgeCount P.graph:ℝ)≤d.degree j*P.vertices.card)
    (hvalid : ∀ i<k, d.valid (j+i)) :
    ∀ P∈advance s j k L, 2*(edgeCount P.graph:ℝ)≤d.degree (j+k)*P.vertices.card := by
  induction k with
  | zero => simpa only [advance_zero,Nat.add_zero] using hdeg
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    have hpdeg := ih (fun i hi => hvalid i (by omega)) P hP
    have hb := hs (j+k) P (hvalid k (by omega)) hpdeg
    have hnext := mul_le_mul_of_nonneg_right (d.next_degree (j+k) (hvalid k (by omega)))
      (Nat.cast_nonneg (α:=ℝ) B.vertices.card)
    rw [hv,hg,show j+(k+1)=(j+k)+1 by omega]
    exact (hb.2.2.2.2 B hB).trans hnext

theorem variable_advance_entropy_bounds (d : EntropyScaleData) (s : SplitSystem V)
    (hs : ∀ i P, d.valid i → 2*(edgeCount P.graph:ℝ)≤d.degree i*P.vertices.card →
      EntropyStageBounds (s i P) (d.degree i) (d.cycleLength i) (d.boxOrder i) (d.expansion i))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hdeg : ∀ P∈L, 2*(edgeCount P.graph:ℝ)≤d.degree j*P.vertices.card)
    (hvalid : ∀ i≤k, d.valid (j+i)) :
    ∀ P∈advance s j k L, EntropyStageBounds (s (j+k) P)
      (d.degree (j+k)) (d.cycleLength (j+k)) (d.boxOrder (j+k)) (d.expansion (j+k)) := by
  intro P hP
  exact hs (j+k) P (hvalid k le_rfl)
    (variable_advance_degree d s hs j k L hdeg (fun i hi => hvalid i hi.le) P hP)

theorem variable_level_cycles (d : EntropyScaleData) (s : SplitSystem V) (i : ℕ)
    (L : List (AssignedPiece V)) (hi : d.valid i)
    (hb : ∀ P∈L, EntropyStageBounds (s i P)
      (d.degree i) (d.cycleLength i) (d.boxOrder i) (d.expansion i)) :
    ((levelCycles s i L).length:ℝ) ≤ d.degree i/(2*d.cycleLength i)*vertexMass L := by
  have hpos : 0<d.cycleLength i := by have := d.cycle_pos i hi; linarith
  induction L with
  | nil => simp [levelCycles]
  | cons P L ih =>
    have hp := (hb P (by simp)).1
    have hc : ((s i P).cycles.length:ℝ) ≤ d.degree i/(2*d.cycleLength i)*P.vertices.card := by
      rw [show d.degree i/(2*d.cycleLength i)*P.vertices.card =
        (d.degree i*P.vertices.card)/(2*d.cycleLength i) by ring]
      apply (le_div_iff₀ (by positivity : 0<2*d.cycleLength i)).mpr
      linarith only [hp]
    have ht := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [levelCycles,List.flatMap_cons,List.length_append,Nat.cast_add,vertexMass_cons] at ht ⊢
    nlinarith only [hc,ht]

end
end Cycle12
