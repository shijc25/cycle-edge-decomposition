import Cycle12.Foundations.Definitions

/-! Degree deficiency in nonempty finite simple graphs (DY Lemma 15). -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def degreeDeficiency {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ) : ℕ :=
  ∑ v : V, (d - G.degree v)

theorem exists_degree_ge_of_deficiency {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {d : ℕ} (hd : degreeDeficiency G d < d) :
    ∃ v, d ≤ G.degree v := by
  classical
  by_contra! hnone
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hsum : Fintype.card V ≤ degreeDeficiency G d := by
    calc
      _ = ∑ _v : V, 1 := by simp
      _ ≤ _ := sum_le_sum (fun v _ => by have hv := hnone v; omega)
  have hnlt : Fintype.card V < d := lt_of_le_of_lt hsum hd
  have hsum' : Fintype.card V * (d+1-Fintype.card V) ≤ degreeDeficiency G d := by
    calc
      _ = ∑ _v : V, (d+1-Fintype.card V) := by simp
      _ ≤ _ := sum_le_sum (fun v _ => by have hv := G.degree_lt_card_verts v; omega)
  have hnsub : Fintype.card V-1+1=Fintype.card V := by omega
  have hdsub : d-Fintype.card V+Fintype.card V=d := by omega
  have heq : d+1-Fintype.card V=(d-Fintype.card V)+1 := by omega
  rw [heq] at hsum'
  have hprod : 0 ≤ (Fintype.card V-1)*(d-Fintype.card V) := Nat.zero_le _
  nlinarith

theorem order_gt_of_deficiency {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {d : ℕ} (hd : degreeDeficiency G d < d) :
    d < Fintype.card V := by
  obtain ⟨v,hv⟩ := exists_degree_ge_of_deficiency G hd
  exact hv.trans_lt (G.degree_lt_card_verts v)

end
end Cycle13
