import Cycle12.Foundations.ProperCutContraction
import Cycle12.Foundations.SimpleCutCount

namespace Cycle13
open Finset ARA ARA.MultiGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [DecidableEq V]

theorem properSmallCuts_fractional_potential (g : MultiGraph V) (hwf : g.WF)
    {k K l : ℕ} {θ : ℝ} (hk : 2 ≤ k) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hl : 0 < l) (hK : 2*(K:ℝ) ≤ ((k:ℝ)+θ)*l) (hmin : l ≤ g.minCutValue)
    (hn : k+1 ≤ g.verts.card) :
    ((properSmallCuts g K).card:ℝ) ≤ fractionalCutPotential g.verts.card k θ := by
  have main : ∀ n, ∀ g : MultiGraph V, g.verts.card=n → g.WF →
      l ≤ g.minCutValue → k+1 ≤ n →
      ((properSmallCuts g K).card:ℝ) ≤ fractionalCutPotential n k θ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hcard hwf hmin hn
      by_cases heq : n=k+1
      · rw [heq,fractionalCutPotential_base]
        have hh := (properSmallCuts_total g K).trans
          (proper_subsets_le_factorial (by omega : 2 ≤ g.verts.card))
        simpa only [hcard,heq] using (Nat.cast_le (α:=ℝ)).mpr hh
      have hlt : k+1 < n := by omega
      have hstep : ((n:ℝ)-((k:ℝ)+θ))*(properSmallCuts g K).card ≤
          (n:ℝ)*fractionalCutPotential (n-1) k θ := by
        rw [← hcard]
        apply properSmallCuts_contraction_step g hwf (by positivity) hl hK hmin (by omega)
        intro e he
        have hfresh : e.out.1∉g.verts.filter (·∉e) := by simp [Sym2.out_fst_mem]
        have hcontract := card_verts_contractEdgeTo hfresh (hwf.incidence e he) (hwf.loopless e he)
        have hc : (g.contractEdgeTo e e.out.1).verts.card=n-1 := by omega
        rw [hcard]
        apply ih (n-1) (by omega) _ hc hwf.contractEdgeTo
        · exact hmin.trans (minCutValue_le_contractEdgeTo hwf hfresh
            (hwf.incidence e he) (hwf.loopless e he) (by omega))
        · omega
      have hpot := fractionalCutPotential_step hlt hθ₀ hθ₁
      have hpos : 0 < (n:ℝ)-((k:ℝ)+θ) := by
        have hh : (k:ℝ)+1 < n := by exact_mod_cast hlt
        linarith
      exact (mul_le_mul_iff_right₀ hpos).mp (hstep.trans hpot)
  exact main _ g rfl hwf hmin hn

/-- Oriented proper cuts are counted separately, including complementary
pairs. The exponent is real; no ceiling or extra factor of n is present. -/
theorem properSmallCuts_real_bound (g : MultiGraph V) (hwf : g.WF)
    {K l : ℕ} {a : ℝ} (ha : 2 ≤ a) (hl : 0 < l)
    (hK : 2*(K:ℝ) ≤ a*l) (hmin : l ≤ g.minCutValue) (hn : 2 ≤ g.verts.card) :
    ((properSmallCuts g K).card:ℝ) ≤ (g.verts.card:ℝ)^a := by
  let k := ⌊a⌋₊
  let θ := a-k
  have hk : 2 ≤ k := Nat.le_floor ha
  have hθ₀ : 0 ≤ θ := sub_nonneg.mpr (Nat.floor_le (by linarith : 0 ≤ a))
  have hθ₁ : θ ≤ 1 := by have hh := Nat.lt_floor_add_one a; dsimp [θ,k]; linarith
  have he : (k:ℝ)+θ=a := by dsimp [θ]; ring
  by_cases hkn : k+1 ≤ g.verts.card
  · have hh := properSmallCuts_fractional_potential g hwf hk hθ₀ hθ₁ hl (by rwa [he]) hmin hkn
    have hp := fractionalCutPotential_le_rpow (by omega : k ≤ g.verts.card) hθ₀ (by omega)
    rw [he] at hp
    exact hh.trans hp
  · have hh := (properSmallCuts_total g K).trans
        ((proper_subsets_le_factorial hn).trans (Nat.factorial_le_pow _))
    have hna : (g.verts.card:ℝ) ≤ a := by
      have hh : (g.verts.card:ℝ) ≤ k := by exact_mod_cast (show g.verts.card ≤ k by omega)
      linarith [Nat.floor_le (by linarith : 0 ≤ a)]
    calc
      _ ≤ (g.verts.card:ℝ)^g.verts.card := by exact_mod_cast hh
      _ = (g.verts.card:ℝ)^(g.verts.card:ℝ) := (rpow_natCast _ _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ g.verts.card by omega)) hna

theorem simple_proper_cut_count_real [Fintype V] (G : SimpleGraph V)
    {K : ℕ} {a lam : ℝ} (ha : 2 ≤ a) (hlam : 0 < lam)
    (hK : 2*(K:ℝ) ≤ a*lam) (hn : 2 ≤ Fintype.card V)
    (hmin : ∀ S : Finset V, S.Nonempty → S≠univ → lam ≤ (cutSize G S:ℝ)) :
    ((univ.filter (fun S : Finset V => S.Nonempty ∧ S≠univ ∧ cutSize G S ≤ K)).card:ℝ) ≤
      (Fintype.card V:ℝ)^a := by
  let l := ⌈lam⌉₊
  have hlR : lam ≤ (l:ℝ) := Nat.le_ceil lam
  have hl : 0 < l := by exact_mod_cast hlam.trans_le hlR
  have hminN : ∀ S : Finset V, S.Nonempty → S≠univ → l ≤ cutSize G S := by
    intro S hS hSu
    exact Nat.ceil_le.mpr (hmin S hS hSu)
  have hk : 2*(K:ℝ) ≤ a*l := hK.trans (mul_le_mul_of_nonneg_left hlR (by linarith))
  have hh := properSmallCuts_real_bound (simpleAsMulti G) (simpleAsMulti_wf G) ha hl hk
    (simpleAsMulti_minCut_lower G hn hminN) (by simpa [simpleAsMulti] using hn)
  have he : properSmallCuts (simpleAsMulti G) K=
      univ.filter (fun S : Finset V => S.Nonempty ∧ S≠univ ∧ cutSize G S ≤ K) := by
    ext S
    rw [mem_properSmallCuts,simpleAsMulti_cutValue]
    change (S⊆univ ∧ cutSize G S ≤ K ∧ S.Nonempty ∧ S≠univ) ↔ _
    simp only [subset_univ,mem_filter,mem_univ,true_and]
    tauto
  rw [he] at hh
  simpa only [simpleAsMulti,card_univ] using hh

end
end Cycle13
