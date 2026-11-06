import Cycle12.GlobalPotential12
import Cycle12.ContractedPackingInduction12

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- The strengthened induction hypothesis retains the actual order
potential, so contractions at scale w are paid at phi(bw). -/
def PotentialBelow (n : ℕ) : Prop := ∀ m,m<n → ∀ H : SimpleGraph (Fin m),
  ∃ P : CyclePacking H,P.weight ≤ C*orderPotential m*m

theorem PotentialBelow.unweighted {n : ℕ} (ih : PotentialBelow n) :
    ∀ m,m<n → ∀ H : SimpleGraph (Fin m),∃ P : CyclePacking H,P.weight ≤ C*m := by
  intro m hm H
  obtain ⟨P,hP⟩ := ih m hm H
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderPotential_bounds m).2 (show 0 ≤ C by norm_num [C]))
    (Nat.cast_nonneg m)
  exact ⟨P,hP.trans (by simpa only [mul_one] using hp)⟩

/-- Relabel an actual smaller graph without losing its potential. -/
theorem PotentialBelow.actual_graph {n : ℕ} (ih : PotentialBelow n)
    (H : SimpleGraph V) (hn : Fintype.card V<n) :
    ∃ P : CyclePacking H,P.weight ≤ C*orderPotential (Fintype.card V)*Fintype.card V :=
  packing_weight_of_fin_bound H (ih _ hn)

/-- A smaller graph whose order is bounded by the current contracted
scale can use the scale's single common potential coefficient. -/
theorem PotentialBelow.at_scale {n : ℕ} (ih : PotentialBelow n)
    (H : SimpleGraph V) (hn : Fintype.card V<n) {x : ℝ}
    (hx : (Fintype.card V:ℝ) ≤ (2:ℝ)^x) :
    ∃ P : CyclePacking H,P.weight ≤ C*globalPhi x*Fintype.card V := by
  obtain ⟨P,hP⟩ := ih.actual_graph H hn
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderPotential_upper_at_scale hx) (show 0 ≤ C by norm_num [C]))
    (Nat.cast_nonneg (Fintype.card V))
  exact ⟨P,hP.trans hh⟩

/-- Full contraction is performed on an actual batch of strictly smaller
order. Every recursive call is bounded by the batch order, even though
the strengthened global induction is available for more graphs. -/
theorem PotentialBelow.contracted_at_scale {n : ℕ} (ih : PotentialBelow n)
    (H : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hn : Fintype.card V<n) {x L : ℝ} (hx : (Fintype.card V:ℝ) ≤ (2:ℝ)^x)
    (hL : 1 ≤ L) (hsize : ∀ i,L ≤ ((A i).card:ℝ)) :
    ∃ P : CyclePacking (H.map (contractVertex A)),
      P.weight ≤ C*globalPhi x*((Fintype.card V:ℝ)-(1-1/L)*(∑ i,((A i).card:ℝ))) := by
  apply contracted_packing_induction H A hd (n:=Fintype.card V+1) (by omega) hL
    (mul_nonneg (by norm_num [C]) (globalPhi_bounds x).1.le) hsize
  intro m hm J
  have hm' : m ≤ Fintype.card V := by omega
  obtain ⟨P,hP⟩ := ih m (hm'.trans_lt hn) J
  have hmx : (m:ℝ) ≤ (2:ℝ)^x := (Nat.cast_le.mpr hm').trans hx
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (orderPotential_upper_at_scale hmx) (show 0 ≤ C by norm_num [C]))
    (Nat.cast_nonneg m)
  exact ⟨P,hP.trans hp⟩

end
end Cycle12.Global12
