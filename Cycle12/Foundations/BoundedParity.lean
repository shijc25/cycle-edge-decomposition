import Cycle12.Foundations.ParityBlowup
import Cycle12.Foundations.MatchingParityProjection

/-! Bounded parity correction directly from Tutte's theorem. No bounded-degree
spanning-tree theorem is assumed. Three or four copies per vertex suffice. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def parityCopies (G : SimpleGraph V) (v : V) : ℕ := if Even (G.degree v) then 4 else 3

theorem parityCopies_bounds (G : SimpleGraph V) (v : V) :
    3 ≤ parityCopies G v ∧ parityCopies G v ≤ 4 := by unfold parityCopies; split_ifs <;> omega

theorem parityCopies_even (G : SimpleGraph V) (v : V) :
    Even (parityCopies G v) ↔ Even (G.degree v) := by
  by_cases h : Even (G.degree v)
  · simp only [parityCopies,if_pos h]
    exact iff_of_true (by decide) h
  · simp only [parityCopies,if_neg h]
    exact iff_of_false (by decide) h

theorem parityCopies_total_even (G : SimpleGraph V) :
    Even (Nat.card (Σ v, Fin (parityCopies G v))) := by
  have hp : ∀ v, Even (parityCopies G v+G.degree v) := by
    intro v
    exact Nat.even_add.mpr (parityCopies_even G v)
  have hs : Even (∑ v : V, (parityCopies G v+G.degree v)) := Finset.even_sum _ (fun v _ => hp v)
  rw [sum_add_distrib,G.sum_degrees_eq_twice_card_edges] at hs
  have he : Even (∑ v : V, parityCopies G v) :=
    (Nat.even_add.mp hs).mpr (even_two_mul _)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_fin] using he

theorem sigma_first_fiber_card (k : V → ℕ) (v : V) :
    (univ.filter (fun x : Σ v, Fin (k v) => x.1=v)).card=k v := by
  rw [← Fintype.card_subtype]
  let e : {x : Σ v, Fin (k v) // x.1=v} ≃ Fin (k v) := {
    toFun x := x.property ▸ x.val.2
    invFun i := ⟨⟨v,i⟩,rfl⟩
    left_inv := by rintro ⟨⟨w,i⟩,h⟩; cases h; rfl
    right_inv _ := rfl }
  simpa using Fintype.card_congr e

theorem exists_bounded_parity_subgraph (G : SimpleGraph V) (hG : G.Preconnected)
    (hcomp : ∀ U : Set V, U.Nonempty →
      Nat.card (G.induce Uᶜ).ConnectedComponent ≤ 3*U.ncard) :
    ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v,
      F.degree v ≤ 4 ∧ (Even (F.degree v) ↔ Even (G.degree v)) := by
  obtain ⟨M,hM,hcover⟩ := parity_blowup_perfect_matching G (parityCopies G) hG
    (fun v => (parityCopies_bounds G v).1) (parityCopies_total_even G) hcomp
  obtain ⟨F,hFG,hF⟩ := matching_parity_projection G M hM hcover Sigma.fst
    (fun x y hxy => (M.adj_sub hxy).2)
  refine ⟨F,hFG,fun v => ?_⟩
  have hv := hF v
  rw [sigma_first_fiber_card] at hv
  exact ⟨hv.1.trans (parityCopies_bounds G v).2,hv.2.trans (parityCopies_even G v)⟩

theorem exists_even_remainder_loss_four (G : SimpleGraph V) (hG : G.Preconnected)
    (hcomp : ∀ U : Set V, U.Nonempty →
      Nat.card (G.induce Uᶜ).ConnectedComponent ≤ 3*U.ncard) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, Even (H.degree v)) ∧
      ∀ v, G.degree v ≤ H.degree v+4 := by
  obtain ⟨F,hFG,hF⟩ := exists_bounded_parity_subgraph G hG hcomp
  refine ⟨G\F,sdiff_le,?_,?_⟩
  · intro v
    have he := (graph_symmDiff_degree_even G F v).mpr (hF v).2.symm
    have hx : G ∆ F=G\F := symmDiff_of_ge hFG
    simpa only [← ncard_neighborSet,hx] using he
  · intro v
    have hb := degree_sdiff_add G F hFG v
    have hf := (hF v).1
    simp only [← ncard_neighborSet] at hb hf ⊢
    omega

end
end Cycle13
