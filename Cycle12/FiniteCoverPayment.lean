import Cycle12.Foundations.FiniteAffineStep
import Cycle12.CoverCutAssembly

namespace Cycle12
open Cycle13 SimpleGraph Finset Real MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable

theorem coverGraphBudget_mono_order {n N m : ℝ} (hn : 0 ≤ n) (hnN : n ≤ N) (hm : 0 ≤ m) :
    coverGraphBudget n m  ≤  coverGraphBudget N m := by
  have h₁ := mul_le_mul_of_nonneg_right hnN (rpow_nonneg hm (1/3:ℝ))
  have h₂ := mul_le_mul hnN (sqrt_le_sqrt hnN) (sqrt_nonneg n) (hn.trans hnN)
  unfold coverGraphBudget cubeScale
  nlinarith

theorem fineMixedCover_padded {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : FineCover G 2) {N : ℝ} (hn : (0:ℝ)<Fintype.card V)
    (hN : (Fintype.card V:ℝ) ≤ N) :
    ∃ P : CyclePacking G, (P.count:ℝ) ≤ coverCycleBudget N G.edgeSet.ncard ∧
      (P.singles:ℝ) ≤ coverGraphBudget N G.edgeSet.ncard+2*N := by
  obtain ⟨P,hPc,hPe⟩ := hG
  refine ⟨P,hPc.trans (cover_cycle_budget_mono_order hn hN),?_⟩
  have hf := coverGraphBudget_mono_order hn.le hN (Nat.cast_nonneg (α:=ℝ) G.edgeSet.ncard)
  linarith

/-- A low-density block may be left entirely as single edges; otherwise
use the fine mixed cover with its order padded by isolated vertices. -/
theorem exists_mixed_local_payment {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : FineCover G 2) {N t T : ℝ} (hn : (0:ℝ)<Fintype.card V)
    (hN : (Fintype.card V:ℝ) ≤ N) (ht : 0<t) :
    ∃ P : CyclePacking G, (P.count:ℝ)+(P.singles:ℝ)/t-(G.edgeSet.ncard:ℝ)/T  ≤ 
      min ((G.edgeSet.ncard:ℝ)/t-(G.edgeSet.ncard:ℝ)/T)
        (coverCycleBudget N G.edgeSet.ncard+(coverGraphBudget N G.edgeSet.ncard+2*N)/t-
          (G.edgeSet.ncard:ℝ)/T) := by
  by_cases hmin : (G.edgeSet.ncard:ℝ)/t  ≤ 
      coverCycleBudget N G.edgeSet.ncard+(coverGraphBudget N G.edgeSet.ncard+2*N)/t
  · refine ⟨CyclePacking.empty G,?_⟩
    have hs : (CyclePacking.empty G).singles=G.edgeSet.ncard := by simp [CyclePacking.singles,
      CyclePacking.residue,CyclePacking.used,CyclePacking.empty]
    rw [hs,min_eq_left (sub_le_sub_right hmin _)]
    simp only [CyclePacking.empty,Nat.cast_zero,zero_add,le_refl]
  · obtain ⟨P,hPc,hPe⟩ := fineMixedCover_padded G hG hn hN
    refine ⟨P,?_⟩
    rw [min_eq_right (sub_le_sub_right (le_of_lt (lt_of_not_ge hmin)) _)]
    have hh := div_le_div_of_nonneg_right hPe ht.le
    linarith

def regularBlockFee (s T t m : ℝ) : ℝ :=
  min (m/t-m/T)
    (coverCycleBudget (s+T) m+(coverGraphBudget (s+T) m+2*(s+T))/t-m/T)

def terminalBlockFee (s T t m : ℝ) : ℝ :=
  s/2+(coverGraphBudget s m+s)/t-m/T

/-- All graph hypotheses in the block-payment interface are discharged
here. Its remaining inputs are the universal mixed cover and two scalar
inequalities, one for regular cores and one for boundary-free cores. -/
theorem finiteBlockPayment_of_mixed_cover {k T : ℕ} {t K : ℝ} (ht : 0<t)
    (hcover : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      FineCover H 2 ∧ CoarseCover H 1)
    (hregular : ∀ s : ℕ, k ≤ s → s<2*k → ∀ m : ℝ, 0 ≤ m →
      regularBlockFee s T t m  ≤  K*s)
    (hterminal : ∀ s : ℕ, 0<s → s ≤ k → ∀ m : ℝ, 0 ≤ m →
      terminalBlockFee s T t m  ≤  K*s) : FiniteBlockPayment k T t K := by
  intro V _ _ G B
  have hsize : Fintype.card B.vertices=B.vertices.card := Fintype.card_coe _
  have hnonempty : B.vertices.Nonempty := by
    obtain ⟨v,hv⟩ := B.core_nonempty
    exact ⟨v,Finset.mem_union_left _ hv⟩
  have hn : (0:ℝ)<Fintype.card B.vertices := by
    rw [hsize]
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hm : (0:ℝ) ≤ B.localGraph.edgeSet.ncard := Nat.cast_nonneg _
  obtain ⟨hFine,hCoarse⟩ := hcover B.vertices B.localGraph
  rcases B.size with hsmall | hregularB
  · have hs : Fintype.card B.vertices=B.core.card := by
      rw [hsize,B.vertices_card,hsmall.2,Finset.card_empty,Nat.add_zero]
    obtain ⟨P,hPc,hPe⟩ := hCoarse
    rw [hs] at hPc hPe
    have hh := div_le_div_of_nonneg_right hPe ht.le
    have hb := hterminal B.core.card (Finset.card_pos.mpr B.core_nonempty) hsmall.1 _ hm
    refine ⟨P,?_⟩
    unfold terminalBlockFee at hb
    simp only [one_mul] at hh
    linarith
  · have hN : (Fintype.card B.vertices:ℝ) ≤ (B.core.card:ℝ)+T := by
      have hh := B.order_le
      rw [← hsize] at hh
      exact_mod_cast hh
    obtain ⟨P,hP⟩ := exists_mixed_local_payment B.localGraph hFine hn hN ht (T:=(T:ℝ))
    exact ⟨P,hP.trans (hregular B.core.card hregularB.1 hregularB.2.1 _ hm)⟩

end
end Cycle12
