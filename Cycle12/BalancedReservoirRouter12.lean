import Cycle12.IndexedImmersionRouting
import Cycle12.BalancedRouterRounding12
import Cycle12.BiasedBankSplit
import Cycle12.Foundations.SampleGraphBounds
import Cycle12.Foundations.EulerianPreprocessing

namespace Cycle12
open SimpleGraph Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- The balanced reservoir router is an actual graph theorem. All endpoint
occurrences are retained, including repetitions. It promises edge
disjointness, not disjoint interiors. The logarithmic gate here is weaker
than the original `13500 * log₂ n` gate. -/
theorem balanced_reservoir_router [Nonempty V] (G : SimpleGraph V)
    (source : I × Bool → V) {z : ℝ} (hz : 8192 ≤ z)
    (hlog : 8192*log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card I:ℝ) ≤ z^2)
    (hdeg : ∀ v, (15/16:ℝ)*z ≤ (G.degree v:ℝ))
    (hexp : OAI.ErdosGallai.CutExpansion G (z/30))
    (hload : ∀ v, ((univ.filter (fun k => source k = v)).card:ℝ) ≤ z/64) :
    ∃ p : ∀ i, G.Walk (source (i,false)) (source (i,true)),
      (∀ i, (p i).IsPath) ∧ Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet) := by
  have hz0 : 0 < z := by linarith only [hz]
  have hn : 2 ≤ Fintype.card V := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hd := hdeg v
    have hn := G.degree_lt_card_verts v
    have hnR : (G.degree v:ℝ) < Fintype.card V := by exact_mod_cast hn
    have hh : (2:ℝ) ≤ Fintype.card V := by linarith only [hd,hnR,hz]
    exact_mod_cast hh
  have hcut := mincut_of_degree_and_expansion G (by linarith only [hz] : 1 ≤ z/30) hdeg
    (by
      intro S hS
      have he := hexp S
      rw [← cutSize_eq_interedges] at he
      have hc : (S.card:ℝ) ≤ Sᶜ.card := by
        exact_mod_cast (show S.card ≤ Sᶜ.card by have := card_add_card_compl S; omega)
      simpa only [min_eq_left hc] using he)
  obtain ⟨hgap,hfail⟩ := sharp_cut_failure_quarter (ε := 1/32) (h := (15/16)*z)
    (by omega : 1 ≤ Fintype.card V) (by nlinarith only [hz,hlog])
  let q : unitInterval := ⟨1/2,by norm_num⟩
  obtain ⟨ω,hF,hK⟩ := exists_direct_edge_split G q (ε := 1/32)
    (f := 15/32) (g := 15/32) (budget := 1/4)
    (by norm_num) (by positivity) hn hcut
    (by norm_num [q]) (by norm_num [q]) hgap hfail (by norm_num)
  let F := splitBank G ω true
  let K := splitBank G ω false
  have hpart := splitBank_partition G ω
  have hFG : F ≤ G := by intro x y hxy; exact hxy.1
  have hKG : K ≤ G := by intro x y hxy; exact hxy.1
  have hFexp : OAI.ErdosGallai.CutExpansion F (z/64) := by
    convert cutExpansion_of_cut_retention (by norm_num : (0:ℝ) ≤ 15/32) hexp hF using 1 <;> ring
  have hKdeg : ∀ v, (225/512:ℝ)*z ≤ (K.degree v:ℝ) := by
    intro v
    have hh := (mul_le_mul_of_nonneg_left (hdeg v) (by norm_num : (0:ℝ) ≤ 15/32)).trans
      (cut_retention_implies_degree_retention G K hK v)
    convert hh using 1 <;> ring
  obtain ⟨ht,hteven,hd,hc,hcap,hterminal⟩ := balanced_router_rounding hz hsquare
  obtain ⟨M,_⟩ := budgeted_clique_of_min_degree K ht hteven (by
    intro v
    exact_mod_cast hd.trans (hKdeg v))
  have hFM : Disjoint F.edgeSet (M.mapLe hKG).used := by
    rw [WeakCliqueImmersion.used_mapLe]
    apply Disjoint.mono_right M.used_subset
    apply Set.disjoint_left.mpr
    intro e heF heK
    induction e using Sym2.inductionOn with
    | _ x y => exact SimpleGraph.disjoint_left.mp hpart.1 x y heF heK
  exact route_via_expansion_and_immersion G F hFG (M.mapLe hKG) hFM source
    hFexp hload hc hcap hterminal

end
end Cycle12
