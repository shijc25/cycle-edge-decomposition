import Cycle12.Foundations.ExpanderDiameter
import Cycle12.Foundations.ExpansionWithinTools

namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- A short path in the original graph, with every vertex in the
prescribed expanding induced subgraph. -/
theorem ExpansionWithin.short_path {G : SimpleGraph V} {S : Finset V} {h : ℝ}
    (hexp : ExpansionWithin G S h) (hh : 0 < h) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    ∃ p : G.Walk a b, p.IsPath ∧ (∀ v ∈ p.support, v ∈ S) ∧
      (p.length:ℝ) ≤ 2*sqrt (2*S.card/h)+2 := by
  let H := G.induce (S:Set V)
  obtain ⟨q,hq,hlen⟩ := expander_short_path H hh hexp.induce ⟨a,ha⟩ ⟨b,hb⟩
  let f : H ↪g G := SimpleGraph.Embedding.induce (S:Set V)
  refine ⟨q.map f.toHom,hq.map f.injective,?_,?_⟩
  · intro v hv
    erw [SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨x,hx,rfl⟩ := hv
    exact x.property
  · erw [SimpleGraph.Walk.length_map]
    have hc : Fintype.card (S:Set V)=S.card := Fintype.card_of_finset' S (fun _ => Iff.rfl)
    simpa only [hc] using hlen

end
end Cycle13
