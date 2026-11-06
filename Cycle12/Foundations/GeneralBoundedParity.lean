import Cycle12.Foundations.BoundedParity

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def boundedParityCopies (G : SimpleGraph V) (q : ℕ) (v : V) : ℕ :=
  if Even q ↔ Even (G.degree v) then q else q+1

theorem boundedParityCopies_bounds (G : SimpleGraph V) (q : ℕ) (v : V) :
    q ≤ boundedParityCopies G q v ∧ boundedParityCopies G q v ≤ q+1 := by
  unfold boundedParityCopies
  split_ifs <;> omega

theorem boundedParityCopies_even (G : SimpleGraph V) (q : ℕ) (v : V) :
    Even (boundedParityCopies G q v) ↔ Even (G.degree v) := by
  unfold boundedParityCopies
  split_ifs with h
  · exact h
  · simp only [Nat.even_add_one]
    tauto

theorem boundedParityCopies_total_even (G : SimpleGraph V) (q : ℕ) :
    Even (Nat.card (Σ v, Fin (boundedParityCopies G q v))) := by
  have hp : ∀ v, Even (boundedParityCopies G q v+G.degree v) :=
    fun v => Nat.even_add.mpr (boundedParityCopies_even G q v)
  have hs : Even (∑ v : V, (boundedParityCopies G q v+G.degree v)) :=
    Finset.even_sum _ (fun v _ => hp v)
  rw [sum_add_distrib,G.sum_degrees_eq_twice_card_edges] at hs
  have he : Even (∑ v : V, boundedParityCopies G q v) :=
    (Nat.even_add.mp hs).mpr (even_two_mul _)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_fin] using he

/-- The Tutte blowup argument works for every component-count parameter.
It constructs the parity correction directly, without a spanning tree. -/
theorem exists_bounded_parity_subgraph_general (G : SimpleGraph V) {q : ℕ}
    (hG : G.Preconnected)
    (hcomp : ∀ U : Set V, U.Nonempty →
      Nat.card (G.induce Uᶜ).ConnectedComponent ≤ q*U.ncard) :
    ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v,
      F.degree v ≤ q+1 ∧ (Even (F.degree v) ↔ Even (G.degree v)) := by
  obtain ⟨M,hM,hcover⟩ := parity_blowup_perfect_matching G (boundedParityCopies G q) hG
    (fun v => (boundedParityCopies_bounds G q v).1) (boundedParityCopies_total_even G q) hcomp
  obtain ⟨F,hFG,hF⟩ := matching_parity_projection G M hM hcover Sigma.fst
    (fun x y hxy => (M.adj_sub hxy).2)
  refine ⟨F,hFG,fun v => ?_⟩
  have hv := hF v
  rw [sigma_first_fiber_card] at hv
  exact ⟨hv.1.trans (boundedParityCopies_bounds G q v).2,
    hv.2.trans (boundedParityCopies_even G q v)⟩

end
end Cycle13
