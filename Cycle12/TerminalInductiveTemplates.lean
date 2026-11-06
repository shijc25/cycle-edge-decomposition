import Cycle12.TerminalBlockInduction
import Cycle12.TerminalNeighborhoodReduction

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Apply any checked deletion template directly inside the strong order
induction. The retained induced graph may have new cut vertices or components. -/
theorem terminal_neighborhood_induction {d : ℕ} (G : SimpleGraph V)
    (ih : TerminalProperInduction G)
    (E : Finset (Sym2 W)) (words : Fin d → CycleWord W) (D : Finset W)
    (hD : D.Nonempty) (a : W) (ha : a∉D) (f : W ↪ V)
    (hc : TerminalCert.Valid E words)
    (hb : 42*d+23*(E\TerminalCert.covered words).card ≤ 19*D.card+6*E.card)
    (hincident : ∀ i j, (TerminalCert.graph E).Adj i j → i∈D ∨ j∈D)
    (hneighbors : ∀ i∈D, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph E).Adj i j ∧ f j=v) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let S : Finset V := (D.map f)ᶜ
  have hS : S.Nonempty := by
    refine ⟨f a,?_⟩
    simpa only [S,Finset.mem_compl,Finset.mem_map,f.injective.eq_iff,exists_eq_right] using ha
  have hSsmall : S.card<Fintype.card V := by
    have hh := Finset.card_add_card_compl (D.map f)
    rw [Finset.card_map] at hh
    have hp := Finset.card_pos.mpr hD
    dsimp only [S]
    omega
  obtain ⟨P,hP⟩ := ih S hS hSsmall
  exact terminal_neighborhood_reduction G E words D a ha f hc hb hincident hneighbors P hP

end
end Cycle12
