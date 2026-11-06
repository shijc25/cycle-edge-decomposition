import Cycle12.VertexSeparator
import Cycle12.TerminalSmallBase
import Cycle12.Foundations.FiniteAffineStep

/-! Reduce the terminal affine theorem to vertex-biconnected graphs. The
remaining classification theorem is an explicit input, never an axiom. -/
namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

theorem noLongCycle_induce {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {T : ℕ} (hG : Cycle13.NoCycleAtLeast G T) (S : Set V) :
    Cycle13.NoCycleAtLeast (G.induce S) T := by
  intro v p hp
  have hh := hG v.val (p.map (SimpleGraph.Embedding.induce (G:=G) S).toHom)
    (hp.map Subtype.val_injective)
  erw [Walk.length_map] at hh
  exact hh

/-- Every possible vertex separator is handled by a strict order induction.
Only the actual two-connected terminal theorem remains as an input. -/
theorem terminal_affine_from_blocks {threshold : ℕ}
    (hblock : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      4 ≤ Fintype.card W → H.Connected →
      (∀ a, (H.induce ({a}ᶜ : Set W)).Preconnected) →
      Cycle13.NoCycleAtLeast H threshold → ∃ P : Cycle13.CyclePacking H,
        P.cost ≤ 19*(Fintype.card W-1)+6*H.edgeSet.ncard)
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G threshold) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have main : ∀ n : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
      (H : SimpleGraph W), Fintype.card W=n → Cycle13.NoCycleAtLeast H threshold →
      ∃ P : Cycle13.CyclePacking H,
        P.cost ≤ 19*(Fintype.card W-1)+6*H.edgeSet.ncard := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ H hcard hshort
      by_cases hsmall : Fintype.card W ≤ 3
      · exact terminal_affine_card_le_three H hsmall
      by_cases hrobust : ∀ a, (H.induce ({a}ᶜ : Set W)).Preconnected
      · exact hblock W H (by omega)
          (connected_of_all_vertex_deletions H (by omega) hrobust) hrobust hshort
      obtain ⟨a,ha⟩ : ∃ a, ¬(H.induce ({a}ᶜ : Set W)).Preconnected :=
        not_forall.mp hrobust
      obtain ⟨S,T,hcover,hinter,hSsmall,hTsmall,hcross⟩ := vertex_separator_sets H a ha
      have haST : a∈S∩T := by rw [hinter]; exact Finset.mem_singleton_self _
      have haS := (Finset.mem_inter.mp haST).1
      have haT := (Finset.mem_inter.mp haST).2
      have : Nonempty (S:Set W) := ⟨⟨a,haS⟩⟩
      have : Nonempty (T:Set W) := ⟨⟨a,haT⟩⟩
      have hScard : Fintype.card (S:Set W)=S.card := Fintype.card_of_finset' _ (by simp)
      have hTcard : Fintype.card (T:Set W)=T.card := Fintype.card_of_finset' _ (by simp)
      obtain ⟨P,hP⟩ := ih S.card (by omega) (S:Set W) (H.induce (S:Set W)) hScard
        (noLongCycle_induce H hshort _)
      obtain ⟨Q,hQ⟩ := ih T.card (by omega) (T:Set W) (H.induce (T:Set W)) hTcard
        (noLongCycle_induce H hshort _)
      rw [hScard] at hP
      rw [hTcard] at hQ
      exact terminal_affine_one_vertex_gluing H S T a hcover hinter hcross P hP Q hQ
  exact main _ V G rfl hshort

end
end Cycle12
