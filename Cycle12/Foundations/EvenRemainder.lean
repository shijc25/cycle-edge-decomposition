import Cycle12.Foundations.ParityForest
import Cycle12.Foundations.EulerianBudgeted

/-! Parity correction inside a prescribed connected subgraph. Every degree
loss is bounded by that subgraph's degree, including the root vertex. -/
namespace Cycle13
open SimpleGraph Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem degree_sdiff_add (G F : SimpleGraph V) (hFG : F≤G) (v : V) :
    (G \ F).degree v+F.degree v=G.degree v := by
  have h := graph_symmDiff_degree_balance G F v
  have hx : G ∆ F=G \ F := symmDiff_of_ge hFG
  have hi : G⊓F=F := inf_eq_right.mpr hFG
  simp only [← ncard_neighborSet] at h ⊢
  rw [hx,hi] at h
  omega

theorem exists_even_remainder_in_connected (G T : SimpleGraph V)
    (hTG : T≤G) (hT : T.Connected) :
    ∃ F : SimpleGraph V, F≤T ∧ ∀ v, Even ((G \ F).degree v) := by
  classical
  obtain ⟨root⟩ := hT.nonempty
  let S : Finset V := univ.filter (fun v => v≠root ∧ Odd (G.degree v))
  have hr : root∉S := by simp [S]
  obtain ⟨F,hFT,hpar⟩ := exists_rooted_parity_subgraph T hT root S hr
  have hFG : F≤G := hFT.trans hTG
  have hx : G ∆ F=G \ F := symmDiff_of_ge hFG
  have he : ∀ v, v≠root → Even ((G \ F).degree v) := by
    intro v hv
    have hFp := hpar v hv
    have hS : v∉S ↔ Even (G.degree v) := by simp [S,hv,← Nat.not_even_iff_odd]
    rw [hS] at hFp
    have hE : Even ((G ∆ F).degree v) := (graph_symmDiff_degree_even G F v).mpr hFp.symm
    simpa only [← ncard_neighborSet,hx] using hE
  refine ⟨F,hFT,?_⟩
  intro v
  by_cases hv : v=root
  · subst v
    by_contra hn
    have ho := Nat.not_even_iff_odd.mp hn
    obtain ⟨w,hw,hwo⟩ := (G \ F).exists_ne_odd_degree_of_exists_odd_degree root ho
    exact (Nat.not_even_iff_odd.mpr hwo) (he w hw)
  · exact he v hv

theorem exists_even_remainder_degree_bound (G T : SimpleGraph V) {k : ℕ}
    (hTG : T≤G) (hT : T.Connected) (hdeg : ∀ v, T.degree v≤k) :
    ∃ H : SimpleGraph V, H≤G ∧ (∀ v, Even (H.degree v)) ∧
      ∀ v, G.degree v≤H.degree v+k := by
  obtain ⟨F,hFT,hEven⟩ := exists_even_remainder_in_connected G T hTG hT
  refine ⟨G \ F,sdiff_le,?_,?_⟩
  · simpa only [← ncard_neighborSet] using hEven
  intro v
  have hf := (SimpleGraph.degree_le_of_le hFT (v:=v)).trans (hdeg v)
  have hb := degree_sdiff_add G F (hFT.trans hTG) v
  simp only [← ncard_neighborSet] at hf hb ⊢
  omega

end
end Cycle13
