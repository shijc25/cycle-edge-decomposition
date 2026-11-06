import Cycle12.DirectEdgeSplit
import Cycle12.Foundations.ExpanderParityForest

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A coarse explicit sufficient scale for the sharp all-cut bound.
It applies to either side of an arbitrarily biased Bernoulli split. -/
theorem sharp_cut_failure_quarter {n : ℕ} {ε h : ℝ} (hn : 1 ≤ n)
    (hscale : 4*log (n:ℝ)+8 ≤ 2*ε^2*h) :
    0 < 2*ε^2*h-2*log (n:ℝ) ∧ sharpCutFailure n ε h ≤ 1/4 := by
  let A := 2*ε^2*h
  let D := A-2*log (n:ℝ)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ log (n:ℝ) := log_nonneg hnR
  have hD : 8 ≤ D := by dsimp [D,A]; linarith only [hscale,hl]
  have hD0 : 0 < D := by linarith only [hD]
  have hratio : A/D ≤ 2 := (div_le_iff₀ hD0).mpr (by dsimp [D,A]; linarith only [hscale])
  have hexp : exp (-D) ≤ 1/9 := by
    rw [exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (exp_pos D)).mpr
    have hh := add_one_le_exp D
    linarith only [hh,hD]
  refine ⟨hD0,?_⟩
  change A/D*exp (-D) ≤ 1/4
  calc
    _ ≤ 2*(1/9:ℝ) := mul_le_mul hratio hexp (exp_pos _).le (by norm_num)
    _ ≤ _ := by norm_num

theorem cutExpansion_proper_cut {G : SimpleGraph V} {h : ℝ} (hh : 0 ≤ h)
    (hexp : OAI.ErdosGallai.CutExpansion G h) (S : Finset V)
    (hS : S.Nonempty) (hne : S ≠ univ) : h ≤ (cutSize G S:ℝ) := by
  have hc : Sᶜ.Nonempty := by
    by_contra hempty
    have he : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hne
    simpa using congrArg Compl.compl he
  have hmin : (1:ℝ) ≤ min (S.card:ℝ) Sᶜ.card := by
    exact le_min (by exact_mod_cast hS.card_pos) (by exact_mod_cast hc.card_pos)
  have he := hexp S
  rw [←cutSize_eq_interedges] at he
  have hfirst : h ≤ h*min (S.card:ℝ) Sᶜ.card := by
    simpa using mul_le_mul_of_nonneg_left hmin hh
  exact hfirst.trans he

theorem cutExpansion_of_cut_retention {G H : SimpleGraph V} {h f : ℝ}
    (hf : 0 ≤ f) (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hret : ∀ S : Finset V, f*cutSize G S ≤ (cutSize H S:ℝ)) :
    OAI.ErdosGallai.CutExpansion H (f*h) := by
  intro S
  rw [←cutSize_eq_interedges]
  have he := hexp S
  rw [←cutSize_eq_interedges] at he
  have hh := (mul_le_mul_of_nonneg_left he hf).trans (hret S)
  simpa only [mul_assoc] using hh

/-- Actual biased edge partition, simultaneously retaining both cut expansions. -/
theorem biased_bank_split (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hh : 0 < h)
    (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hscale : 4*log (Fintype.card V:ℝ)+8 ≤ h/524288) :
    ∃ ω : Sym2 V → Bool,
      OAI.ErdosGallai.CutExpansion (splitBank G ω true) ((1021/1024)*h) ∧
      OAI.ErdosGallai.CutExpansion (splitBank G ω false) ((1/1024)*h) ∧
      Disjoint (splitBank G ω true) (splitBank G ω false) ∧
      splitBank G ω true ⊔ splitBank G ω false=G := by
  let q : unitInterval := ⟨511/512,by norm_num⟩
  obtain ⟨hgap,hfail⟩ := sharp_cut_failure_quarter (ε:=1/1024) (h:=h) (by omega : 1 ≤ Fintype.card V)
    (by convert hscale using 1 <;> ring)
  obtain ⟨ω,htrue,hfalse⟩ := exists_direct_edge_split G q (ε:=1/1024)
    (f:=1021/1024) (g:=1/1024) (budget:=1/4)
    (by norm_num) hh hn (cutExpansion_proper_cut hh.le hexp)
    (by norm_num [q]) (by norm_num [q]) hgap hfail (by norm_num)
  exact ⟨ω,cutExpansion_of_cut_retention (by norm_num) hexp htrue,
    cutExpansion_of_cut_retention (by norm_num) hexp hfalse,splitBank_partition G ω⟩

/-- Parity correction and the two unequal banks, with all edges accounted for. -/
theorem prepare_biased_expander_banks [Nonempty V] (G : SimpleGraph V) {h : ℝ}
    (hn : 2 ≤ Fintype.card V) (hh : 4096 < h)
    (hsquare : 2048*(Fintype.card V:ℝ) < h^2)
    (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hscale : 4*log (Fintype.card V:ℝ)+8 ≤ ((1023/1024)*h)/524288) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V-componentCount G ∧
      (∀ v, (F.degree v:ℝ) < h/1024) ∧
      (∀ v, Even ((G\F).degree v)) ∧
      ∃ ω : Sym2 V → Bool,
        OAI.ErdosGallai.CutExpansion (splitBank (G\F) ω true) ((1044483/1048576)*h) ∧
        OAI.ErdosGallai.CutExpansion (splitBank (G\F) ω false) ((1023/1048576)*h) ∧
        Disjoint (splitBank (G\F) ω true) (splitBank (G\F) ω false) ∧
        splitBank (G\F) ω true ⊔ splitBank (G\F) ω false=G\F := by
  obtain ⟨F,hFG,hforest,hsize,hdeg,heven,hexpF⟩ := expander_parity_forest_1023 G hh hsquare hexp
  obtain ⟨ω,ht,hf,hd,hu⟩ := biased_bank_split (G\F) hn (by linarith) (by convert hexpF using 1) hscale
  refine ⟨F,hFG,hforest,hsize,hdeg,heven,ω,?_,?_,hd,hu⟩
  · convert ht using 1 <;> ring
  · convert hf using 1 <;> ring

end
end Cycle12
