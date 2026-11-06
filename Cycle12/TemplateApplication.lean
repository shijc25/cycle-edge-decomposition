import Cycle12.TerminalCertificate
import Cycle12.TerminalReduction

/-! Verified finite templates can be used inside arbitrary finite graphs.
The exact-image hypothesis states explicitly which incident edges are removed. -/
namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem terminal_certificate_transport {d b : ℕ}
    (E : Finset (Sym2 W)) (words : Fin d → CycleWord W)
    (hc : TerminalCert.Valid E words) (hb : 42*d+23*(E\TerminalCert.covered words).card ≤ b)
    (f : W ↪ V) (H : SimpleGraph V) (hmodel : (TerminalCert.graph E).map f=H) :
    ∃ P : Cycle13.CyclePacking H, P.cost ≤ b := by
  subst H
  obtain ⟨P,hP⟩ := TerminalCert.sound E words hc hb
  exact ⟨P.mapEmbedding f,by rw [indexed_packing_cost_mapEmbedding]; exact hP⟩

theorem terminal_template_image_edge_count (E : Finset (Sym2 W))
    (hc : ∀ e ∈ E, ¬e.IsDiag) (f : W ↪ V) (H : SimpleGraph V)
    (hmodel : (TerminalCert.graph E).map f=H) : H.edgeSet.ncard=E.card := by
  rw [← hmodel,SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _ f.sym2Map.injective,
    TerminalCert.edgeSet_graph E hc,Set.ncard_coe_finset]

/-- Apply any verified local removal template to a real graph. Every
incident edge is covered once, including its boundary-to-retained edges. -/
theorem terminal_template_vertex_reduction {d : ℕ} (G : SimpleGraph V) (S : Finset V)
    (hS : S.Nonempty) (E : Finset (Sym2 W)) (words : Fin d → CycleWord W)
    (hc : TerminalCert.Valid E words)
    (hb : 42*d+23*(E\TerminalCert.covered words).card ≤
      19*(Fintype.card V-S.card)+6*E.card)
    (f : W ↪ V) (hmodel : (TerminalCert.graph E).map f=incidentRemainder G S)
    (P : Cycle13.CyclePacking (G.induce (S:Set V)))
    (hP : P.cost ≤ 19*(S.card-1)+6*(G.induce (S:Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  obtain ⟨Q,hQ⟩ := terminal_certificate_transport E words hc hb f _ hmodel
  have he := terminal_template_image_edge_count E hc.1 f _ hmodel
  apply terminal_affine_vertex_reduction G S hS P hP Q
  simpa only [he] using hQ

end
end Cycle12
