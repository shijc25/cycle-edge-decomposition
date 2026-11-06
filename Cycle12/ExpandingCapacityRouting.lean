import Cycle12.IndexedCapacityRouting
import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle12.IndexedCapacity
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem source_mass_le (a : I → V) {h : ℝ}
    (hload : ∀ v, ((univ.filter (fun i => a i = v)).card:ℝ) ≤ h)
    (S : Finset V) : ((univ.filter (fun i => a i ∈ S)).card:ℝ) ≤ h*S.card := by
  rw [← sum_card_fiberwise_eq_card_filter univ S a, Nat.cast_sum]
  calc
    _ ≤ ∑ _v ∈ S, h := sum_le_sum (fun v _ => hload v)
    _ = _ := by simp [mul_comm]

/-- Expansion and total branch capacity imply every integral source-capacity
cut, with arbitrary multiplicity at each source vertex. -/
theorem expansion_capacity_cuts (G : SimpleGraph V) (a : I → V) (B : Finset V)
    (c : ℕ) {h : ℝ} (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hload : ∀ v, ((univ.filter (fun i => a i = v)).card:ℝ) ≤ h)
    (hc : (c:ℝ) ≤ h) (htotal : Fintype.card I ≤ c*B.card)
    (X : Finset V) : Fintype.card I ≤ cutSize G X +
      (univ.filter (fun i => a i ∉ X)).card + c*(B ∩ X).card := by
  have he := hexp X
  rw [← cutSize_eq_interedges] at he
  by_cases hsmall : X.card ≤ Xᶜ.card
  · have hsR : (X.card:ℝ) ≤ Xᶜ.card := by exact_mod_cast hsmall
    rw [min_eq_left hsR] at he
    have hm := (source_mass_le a hload X).trans he
    have hmN : (univ.filter (fun i => a i ∈ X)).card ≤ cutSize G X := by exact_mod_cast hm
    have ht := card_filter_add_card_filter_not (s := (univ : Finset I)) (p := fun i => a i ∈ X)
    rw [card_univ] at ht
    omega
  · have hsR : (Xᶜ.card:ℝ) ≤ X.card := by exact_mod_cast (show Xᶜ.card ≤ X.card by omega)
    rw [min_eq_right hsR] at he
    have hbranch : (B ∩ X).card + (B ∩ Xᶜ).card = B.card := by
      simpa only [← mem_compl, filter_mem_eq_inter]
        using card_filter_add_card_filter_not (s := B) (p := fun v => v ∈ X)
    have hb : ((B ∩ Xᶜ).card:ℝ) ≤ Xᶜ.card := by
      exact_mod_cast card_le_card (inter_subset_right (s₁ := B) (s₂ := Xᶜ))
    have hcR : (c:ℝ)*((B ∩ Xᶜ).card:ℝ) ≤ (cutSize G X:ℝ) :=
      ((mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg c)).trans
        (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))).trans he
    have hcN : c*(B ∩ Xᶜ).card ≤ cutSize G X := by exact_mod_cast hcR
    calc
      _ ≤ c*B.card := htotal
      _ = c*(B ∩ X).card+c*(B ∩ Xᶜ).card := by rw [← hbranch, Nat.mul_add]
      _ ≤ _ := by omega

theorem exists_routing_of_expansion (G : SimpleGraph V) (a : I → V) (B : Finset V)
    (c : ℕ) {h : ℝ} (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hload : ∀ v, ((univ.filter (fun i => a i = v)).card:ℝ) ≤ h)
    (hc : (c:ℝ) ≤ h) (htotal : Fintype.card I ≤ c*B.card) :
    Nonempty (Routing G a B c) :=
  exists_routing G a B c (expansion_capacity_cuts G a B c hexp hload hc htotal)

end
end Cycle12.IndexedCapacity
