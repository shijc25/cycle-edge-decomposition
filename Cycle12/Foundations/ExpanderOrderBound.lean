import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A balanced cut in a simple graph bounds its expansion by (n+1)/2.
This is sharper than the singleton-cut bound and pays the routing ratio. -/
theorem cutExpansion_twice_le_order_add_one (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hexp : OAI.ErdosGallai.CutExpansion G h) :
    2*h ≤ (Fintype.card V:ℝ)+1 := by
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq
    (s := (univ:Finset V)) (n := Fintype.card V/2)
    (by simpa only [Finset.card_univ] using Nat.div_le_self (Fintype.card V) 2)
  have hpos : 0 < S.card := by omega
  have hsmall : 2*S.card ≤ Fintype.card V := by omega
  have hx := cutExpansion_small G hexp hsmall
  rw [cutSize_eq_interedges] at hx
  have hb : ((G.interedges S Sᶜ).card:ℝ) ≤ (S.card:ℝ)*Sᶜ.card := by
    exact_mod_cast G.card_interedges_le_mul S Sᶜ
  have hsR : (0:ℝ) < S.card := by exact_mod_cast hpos
  have hh : h ≤ (Sᶜ.card:ℝ) := by nlinarith only [hx,hb,hsR]
  have hc : 2*Sᶜ.card ≤ Fintype.card V+1 := by rw [Finset.card_compl]; omega
  have hcR : 2*(Sᶜ.card:ℝ) ≤ (Fintype.card V:ℝ)+1 := by exact_mod_cast hc
  linarith

theorem routing_bank_order_ratio (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hh : 4096 < h)
    (hexp : OAI.ErdosGallai.CutExpansion G h) :
    4 ≤ (Fintype.card V:ℝ)/((511/1024)*(1023/1024)*h) := by
  have hb := cutExpansion_twice_le_order_add_one G hn hexp
  have hpos : 0 < (511/1024)*(1023/1024)*h := by positivity
  apply (le_div_iff₀ hpos).mpr
  linarith

end
end Cycle13
