import Cycle12.SixEarModels

namespace Cycle12
open SimpleGraph Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def sixEarAllowed : Finset (Fin 11) := {0,1,3,4,6}

def sixEarWitness : Fin 11 → CycleWord (Fin 9) :=
  ![⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,8,4,3,7,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,8,5,4,3,7,6]⟩,⟨0,[1,2]⟩,⟨0,[1,8,4,3,7,6]⟩,⟨0,[1,2,8,5,4,3,7,6]⟩,⟨0,[1,2,8,4,3,7,6]⟩,⟨0,[1,8,5,4,3,7,6]⟩]

theorem six_ear_witnesses_checked : ∀ i : Fin 11, i∈sixEarAllowed ∨
    ((sixEarWitness i).Valid (TerminalCert.graph (sixEarEdges (sixAttachment i))) ∧
      7≤(sixEarWitness i).tail.length+1) := by decide +kernel

/-- The pair constraints and one fixed three-edge ear leave only four families. -/
theorem six_ear_family_cover : ∀ S : Finset (Fin 11), S⊆sixEarAllowed →
    (∀ i∈S, ∀ j∈S, SixPairCompatible i j) →
    ∃ k : Fin 4, S⊆sixAttachmentFamily (Fin.castLE (by decide) k) := by decide +kernel

theorem six_actual_ear_attachment_allowed {V : Type} {G : SimpleGraph V}
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hshort : Cycle13.NoCycleAtLeast G 7)
    {x y z : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i)
    (hxa : G.Adj x (f 0)) (hxy : G.Adj x y) (hyb : G.Adj y (f 3))
    {i : Fin 11} (hz : SixAttachmentVertex G f i z) : i∈sixEarAllowed := by
  rcases six_ear_witnesses_checked i with h | ⟨hw,hlen⟩
  · exact h
  · have hxz : x≠z := by
      intro he; subst z
      exact six_attachment_vertex_no_external_neighbors hz hy hxy
    have hyz : y≠z := by
      intro he; subst z
      exact six_attachment_vertex_no_external_neighbors hz hx hxy.symm
    obtain ⟨e,he⟩ := six_ear_model_embedding f hcycle hx hy hz.1 hxy.ne hxz hyz
      hxa hxy hyb (sixAttachment i)
      (fun k hk => (six_attachment_vertex_adj_frame hz k).mpr hk)
    exact False.elim (noLongCycle_excludes_word_embedding hshort e he _ hw hlen)

end Cycle12
