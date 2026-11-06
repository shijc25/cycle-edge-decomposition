import Cycle12.Foundations.GreedyCyclePacking

namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem greedyRatio_pow_le_exp {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    (greedyRatio n)^k ≤ exp (-2*(k:ℝ)/((n-1:ℕ):ℝ)) := by
  have hbase : greedyRatio n ≤ exp (-2/((n-1:ℕ):ℝ)) := by
    have hh := add_one_le_exp (-2/((n-1:ℕ):ℝ))
    unfold greedyRatio
    convert hh using 1 <;> ring
  have hh := pow_le_pow_left₀ (greedyRatio_nonneg hn) hbase k
  rw [← exp_nat_mul] at hh
  convert hh using 1 <;> congr 1 <;> ring

theorem exists_greedy_exp_packing (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V) (k : ℕ) :
    ∃ P : CyclePacking G, P.count ≤ k ∧
      (P.singles:ℝ) ≤ max ((G.edgeSet.ncard:ℝ)*exp (-2*(k:ℝ)/((Fintype.card V-1:ℕ):ℝ)))
        ((Fintype.card V-1:ℕ):ℝ) := by
  obtain ⟨P,hc,he⟩ := exists_greedy_packing G hn k
  exact ⟨P,hc,he.trans (max_le_max
    (mul_le_mul_of_nonneg_left (greedyRatio_pow_le_exp hn k) (Nat.cast_nonneg _)) le_rfl)⟩

/-- Arbitrary real cycle budgets can be rounded down. Deleting at most one
selected cycle costs at most n more singletons, giving the explicit +2n. -/
theorem exists_greedy_real_budget (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ P : CyclePacking G, (P.count:ℝ) ≤ B ∧
      (P.singles:ℝ) ≤ (G.edgeSet.ncard:ℝ)*exp (-2*B/Fintype.card V)+2*Fintype.card V := by
  obtain ⟨P,hPc,hPe⟩ := exists_greedy_exp_packing G hn ⌈B⌉₊
  have hN : (0:ℝ) < ((Fintype.card V-1:ℕ):ℝ) := by exact_mod_cast (show 0 < Fintype.card V-1 by omega)
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hNn : ((Fintype.card V-1:ℕ):ℝ) ≤ Fintype.card V := by exact_mod_cast Nat.sub_le (Fintype.card V) 1
  have hk : B ≤ (⌈B⌉₊:ℝ) := Nat.le_ceil B
  have hratio : B/Fintype.card V ≤ (⌈B⌉₊:ℝ)/((Fintype.card V-1:ℕ):ℝ) := by
    exact (div_le_div_of_nonneg_left hB hN hNn).trans
      (div_le_div_of_nonneg_right hk hN.le)
  have hexp : exp (-2*(⌈B⌉₊:ℝ)/((Fintype.card V-1:ℕ):ℝ)) ≤ exp (-2*B/Fintype.card V) :=
    exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonpos_left hratio (by norm_num : (-2:ℝ) ≤ 0)
      convert hh using 1 <;> ring)
  have hcost : (P.singles:ℝ) ≤ (G.edgeSet.ncard:ℝ)*exp (-2*B/Fintype.card V)+Fintype.card V := by
    apply hPe.trans
    apply max_le
    · have hh := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (α:=ℝ) G.edgeSet.ncard)
      linarith only [hh,hnR]
    · have hh : (0:ℝ) ≤ (G.edgeSet.ncard:ℝ)*exp (-2*B/Fintype.card V) := by positivity
      linarith only [hh,hNn]
  by_cases hcount : (P.count:ℝ) ≤ B
  · exact ⟨P,hcount,by linarith only [hcost,hnR]⟩
  have hpositive : 0 < P.count := by
    have hh : (0:ℝ) < P.count := lt_of_le_of_lt hB (lt_of_not_ge hcount)
    exact_mod_cast hh
  let i : Fin P.count := ⟨0,hpositive⟩
  refine ⟨P.eraseCycle i,?_,?_⟩
  · have hc : ((P.eraseCycle i).count:ℝ)+1=P.count := by exact_mod_cast P.count_eraseCycle i
    have hceil := Nat.ceil_lt_add_one hB
    have hPcR : (P.count:ℝ) ≤ (⌈B⌉₊:ℝ) := by exact_mod_cast hPc
    linarith only [hc,hceil,hPcR]
  · have he : ((P.eraseCycle i).singles:ℝ) ≤ P.singles+Fintype.card V := by
      exact_mod_cast P.singles_eraseCycle_le i
    linarith only [he,hcost]

/-- The half-order budget has no extra rounding loss: n-1 in Erdős--Gallai
ensures that floor(n/2) steps already reach the exp(-1) residual bound. -/
theorem exists_greedy_half_budget (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V) :
    ∃ P : CyclePacking G, (P.count:ℝ) ≤ (Fintype.card V:ℝ)/2 ∧
      (P.singles:ℝ) ≤ (G.edgeSet.ncard:ℝ)*exp (-1)+Fintype.card V := by
  obtain ⟨P,hPc,hPe⟩ := exists_greedy_exp_packing G hn (Fintype.card V/2)
  have hN : (0:ℝ) < ((Fintype.card V-1:ℕ):ℝ) := by exact_mod_cast (show 0 < Fintype.card V-1 by omega)
  have hk : ((Fintype.card V-1:ℕ):ℝ) ≤ 2*((Fintype.card V/2:ℕ):ℝ) := by
    exact_mod_cast (show Fintype.card V-1 ≤ 2*(Fintype.card V/2) by omega)
  have hratio : (1:ℝ) ≤ 2*((Fintype.card V/2:ℕ):ℝ)/((Fintype.card V-1:ℕ):ℝ) :=
    (one_le_div hN).mpr hk
  have hexp : exp (-2*((Fintype.card V/2:ℕ):ℝ)/((Fintype.card V-1:ℕ):ℝ)) ≤ exp (-1) :=
    exp_le_exp.mpr (by convert neg_le_neg hratio using 1 <;> ring)
  refine ⟨P,?_,?_⟩
  · have hh : 2*P.count ≤ Fintype.card V := by omega
    have hhR : 2*(P.count:ℝ) ≤ Fintype.card V := by exact_mod_cast hh
    linarith
  · apply hPe.trans
    apply max_le
    · have hh := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (α:=ℝ) G.edgeSet.ncard)
      linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
    · have hh : (0:ℝ) ≤ (G.edgeSet.ncard:ℝ)*exp (-1) := by positivity
      have hNn : ((Fintype.card V-1:ℕ):ℝ) ≤ Fintype.card V := by exact_mod_cast Nat.sub_le (Fintype.card V) 1
      linarith only [hh,hNn]

end
end Cycle13
