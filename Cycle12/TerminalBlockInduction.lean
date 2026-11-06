import Cycle12.TerminalBlockReduction
import Cycle12.SixCycleTwinFree

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exactly the smaller induced graphs available in a strong order induction. -/
def TerminalProperInduction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → S.card<Fintype.card V →
    ∃ P : Cycle13.CyclePacking (G.induce (S:Set V)),
      P.cost ≤ 19*(S.card-1)+6*(G.induce (S:Set V)).edgeSet.ncard

/-- A block step may use every proper induced subgraph. Consequently a
local deletion need not preserve vertex robustness or a chosen graph family. -/
theorem terminal_affine_block_induction {threshold : ℕ}
    (hblock : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      4≤Fintype.card W → H.Connected →
      (∀ a, (H.induce ({a}ᶜ : Set W)).Preconnected) →
      Cycle13.NoCycleAtLeast H threshold → TerminalProperInduction H →
      ∃ P : Cycle13.CyclePacking H,
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
      by_cases hsmall : Fintype.card W≤3
      · exact terminal_affine_card_le_three H hsmall
      have hproper : TerminalProperInduction H := by
        intro S hS hSsmall
        obtain ⟨a,ha⟩ := hS
        have : Nonempty (S:Set W) := ⟨⟨a,ha⟩⟩
        have hScard : Fintype.card (S:Set W)=S.card := Fintype.card_of_finset' _ (by simp)
        obtain ⟨P,hP⟩ := ih S.card (by omega) (S:Set W) (H.induce (S:Set W)) hScard
          (noLongCycle_induce H hshort _)
        exact ⟨P,by simpa only [hScard] using hP⟩
      by_cases hrobust : ∀ a, (H.induce ({a}ᶜ : Set W)).Preconnected
      · exact hblock W H (by omega)
          (connected_of_all_vertex_deletions H (by omega) hrobust) hrobust hshort hproper
      obtain ⟨a,ha⟩ : ∃ a, ¬(H.induce ({a}ᶜ : Set W)).Preconnected := not_forall.mp hrobust
      obtain ⟨S,T,hcover,hinter,hSsmall,hTsmall,hcross⟩ := vertex_separator_sets H a ha
      have haST : a∈S∩T := by rw [hinter]; exact Finset.mem_singleton_self _
      have haS := (Finset.mem_inter.mp haST).1
      have haT := (Finset.mem_inter.mp haST).2
      obtain ⟨P,hP⟩ := hproper S ⟨a,haS⟩ hSsmall
      obtain ⟨Q,hQ⟩ := hproper T ⟨a,haT⟩ hTsmall
      exact terminal_affine_one_vertex_gluing H S T a hcover hinter hcross P hP Q hQ
  exact main _ V G rfl hshort

/-- The actual twin-removal step using the strict induction hypothesis. -/
theorem terminal_induction_degree_two_twins {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ih : TerminalProperInduction G) (a b x y : V)
    (hab : a≠b) (hxy : x≠y)
    (hx : ∀ v, G.Adj x v ↔ v=a ∨ v=b)
    (hy : ∀ v, G.Adj y v ↔ v=a ∨ v=b) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hxa := (hx a).mpr (Or.inl rfl)
  have hxb := (hx b).mpr (Or.inr rfl)
  have hya := (hy a).mpr (Or.inl rfl)
  have hyb := (hy b).mpr (Or.inr rfl)
  let S : Finset V := ({x,y}:Finset V)ᶜ
  have hS : S.Nonempty := by
    refine ⟨a,?_⟩
    simp only [S,mem_compl,mem_insert,mem_singleton,not_or]
    exact ⟨hxa.ne.symm,hya.ne.symm⟩
  have hSsmall : S.card<Fintype.card V := by
    have hh := Finset.card_add_card_compl ({x,y}:Finset V)
    rw [Finset.card_pair hxy] at hh
    dsimp only [S]
    omega
  obtain ⟨P,hP⟩ := ih S hS hSsmall
  exact terminal_delete_degree_two_twins G a b x y hab hxy
    hxa.ne.symm hya.ne.symm hxb.ne.symm hyb.ne.symm hx hy P hP

/-- A minimal counterexample must be twin-free; no family-preservation
assumption is introduced when reducing the original graph. -/
theorem terminal_induction_twins_or_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ih : TerminalProperInduction G) :
    NoDegreeTwoTwins G ∨ ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  by_cases htwin : NoDegreeTwoTwins G
  · exact Or.inl htwin
  · unfold NoDegreeTwoTwins at htwin
    push_neg at htwin
    obtain ⟨a,b,x,y,hab,hx,hy,hxy⟩ := htwin
    exact Or.inr (terminal_induction_degree_two_twins G ih a b x y hab hxy hx hy)

end
end Cycle12
