import Cycle12.RectangularDegreeAlgebra

namespace Cycle12
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

def incidenceColumnCount (A : I → Finset V) (v : V) : ℕ :=
  (univ.filter (fun i => v∈A i)).card

theorem incidence_column_square_identity (A : I → Finset V) :
    (∑ v, (incidenceColumnCount A v:ℝ)^2)=∑ i, ∑ j, ((A i∩A j).card:ℝ) := by
  have hi (v : V) : (incidenceColumnCount A v:ℝ)=∑ i, if v∈A i then (1:ℝ) else 0 := by
    simp only [incidenceColumnCount,sum_boole]
  have hp (v : V) : (incidenceColumnCount A v:ℝ)^2=
      ∑ i, ∑ j, if v∈A i∩A j then (1:ℝ) else 0 := by
    rw [hi,pow_two,sum_mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    simp only [mem_inter]
    split_ifs <;> simp_all
  simp_rw [hp]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  have he : univ.filter (fun v => v∈A i∩A j)=A i∩A j := by
    ext v
    simp
  simp only [sum_boole,he]

theorem incidence_column_square_bound (A : I → Finset V) :
    (∑ v, (incidenceColumnCount A v:ℝ)^2) ≤
      ∑ i, ∑ j, min ((A i).card:ℝ) ((A j).card:ℝ) := by
  rw [incidence_column_square_identity]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  have hh : (A i∩A j).card ≤ min (A i).card (A j).card :=
    le_min (card_le_card inter_subset_left) (card_le_card inter_subset_right)
  exact_mod_cast hh

/-- Degree-square bound for an arbitrary incidence relation with at most C
rows and row size at most C. No bound on the number of columns is required. -/
theorem rectangular_incidence_square_bound (A : I → Finset V) (C : ℝ)
    (hC : 0<C) (hu : (Fintype.card I:ℝ)≤C) (hrow : ∀ i, ((A i).card:ℝ)≤C) :
    (∑ i, ((A i).card:ℝ)^2)+(∑ v, (incidenceColumnCount A v:ℝ)^2) ≤
      C*(∑ i, ((A i).card:ℝ))+(∑ i, ((A i).card:ℝ))^2/C := by
  have ha := rectangular_degree_square_algebra (fun i => ((A i).card:ℝ)) C hC hu
    (fun _ => Nat.cast_nonneg _) hrow
  have hb := incidence_column_square_bound A
  exact (add_le_add (le_refl _) hb).trans ha

end
end Cycle12
