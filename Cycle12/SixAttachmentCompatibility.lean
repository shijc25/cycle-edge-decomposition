import Cycle12.SixAttachmentModels

namespace Cycle12
open SimpleGraph Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def sixCompatibleTypes : Fin 11 → Finset (Fin 11) :=
  ![{0,2,3,4,6,8,9},{1,3,4,5,6,7,10},{0,2,4,5,7,8,9},{0,1,3,5,6,8,10},{0,1,2,4,6,7,9},{1,2,3,5,7,8,10},{0,1,3,4,6},{1,2,4,5,7},{0,2,3,5,8},{0,2,4,9},{1,3,5,10}]

def SixPairCompatible (i j : Fin 11) : Prop := j∈sixCompatibleTypes i

instance : DecidableRel SixPairCompatible := fun _ _ => inferInstanceAs (Decidable (_∈_))

def sixPairWitness : Fin 11 → Fin 11 → CycleWord (Fin 8) :=
  ![![⟨0,[1,2]⟩,⟨0,[5,4,3,7,1,2,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,7,5,4,3,2,6]⟩,⟨0,[1,2]⟩,⟨0,[1,7,4,3,2,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,7,5,4,3,2,6]⟩],
    ![⟨0,[5,4,3,6,1,2,7]⟩,⟨0,[1,2]⟩,⟨0,[1,6,3,2,7,4,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,6,3,2,7,5]⟩,⟨0,[1,6,3,2,7,4,5]⟩,⟨0,[1,2]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,7,3,2,6,4,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,6,4,3,7,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,6,4,3,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,6,4,3,7,5]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,7,4,3,6,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,6,5,4,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,7,4,3,6,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,6,5,4,7]⟩,⟨0,[1,2]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,7,5,4,6]⟩,⟨0,[1,2]⟩,⟨0,[5,7,1,2,3,4,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,7,5,4,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,7,5,4,6]⟩],
    ![⟨0,[1,6,5,4,3,2,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[5,6,1,2,3,4,7]⟩,⟨0,[1,2]⟩,⟨0,[1,6,5,4,3,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,6,5,4,3,2,7]⟩,⟨0,[1,2]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,7,4,3,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,7,5,4,3,6]⟩,⟨0,[1,2]⟩,⟨0,[5,4,7,1,2,3,6]⟩,⟨0,[1,2,7,5,4,3,6]⟩,⟨0,[1,2,7,4,3,6]⟩,⟨0,[1,7,5,4,3,6]⟩],
    ![⟨0,[1,6,4,3,2,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,6,4,3,7,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[5,4,6,1,2,3,7]⟩,⟨0,[1,2]⟩,⟨0,[1,6,4,3,2,7,5]⟩,⟨0,[1,6,4,3,2,7]⟩,⟨0,[1,6,4,3,7,5]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,7,3,2,6,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2]⟩,⟨0,[1,2,6,5,4,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2,6,5,4,3,7]⟩,⟨0,[1,7,4,3,2,6,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,6,5,4,7]⟩,⟨0,[1,7,3,2,6,5]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,7,3,2,6,4,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,7,5,4,6]⟩,⟨0,[1,2]⟩,⟨0,[1,7,5,4,3,2,6]⟩,⟨0,[1,2,6,4,3,7]⟩,⟨0,[1,7,4,3,2,6]⟩,⟨0,[1,2,7,5,4,6]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,7,5,4,6]⟩],
    ![⟨0,[1,6,5,4,3,2,7]⟩,⟨0,[1,2]⟩,⟨0,[1,2,7,4,3,6,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,6,5,4,7]⟩,⟨0,[1,2]⟩,⟨0,[1,6,5,4,3,7]⟩,⟨0,[1,7,4,3,6,5]⟩,⟨0,[1,6,3,2,7,5]⟩,⟨0,[1,2,3,6,5,4,7]⟩,⟨0,[1,2]⟩]]

/-- All 56 incompatible pairs carry an explicit simple long cycle. -/
theorem six_pair_witnesses_checked : ∀ i j : Fin 11, SixPairCompatible i j ∨
    ((sixPairWitness i j).Valid (TerminalCert.graph
      (sixPairEdges (sixAttachment i) (sixAttachment j))) ∧
      7≤(sixPairWitness i j).tail.length+1) := by decide +kernel

theorem six_pair_compatible_refl : ∀ i, SixPairCompatible i i := by decide +kernel

def sixAttachmentFamily : Fin 14 → Finset (Fin 11) :=
  ![{0,3,6},{1,3,6},{0,4,6},{1,4,6},{1,4,7},{2,4,7},{1,5,7},{2,5,7},{0,2,8},{0,3,8},{2,5,8},{3,5,8},{0,2,4,9},{1,3,5,10}]

/-- Exhaustive coverage of compatible families, with no graph-classification assumption. -/
theorem six_compatible_family_cover : ∀ S : Finset (Fin 11),
    (∀ i∈S, ∀ j∈S, SixPairCompatible i j) →
    ∃ k, S⊆sixAttachmentFamily k := by decide +kernel

/-- The finite witnesses apply to actual vertices of any ambient order. -/
theorem six_actual_attachments_compatible {V : Type} {G : SimpleGraph V}
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hshort : Cycle13.NoCycleAtLeast G 7)
    {x y : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i) (hxy : x≠y)
    (i j : Fin 11) (hi : ∀ k∈sixAttachment i, G.Adj x (f k))
    (hj : ∀ k∈sixAttachment j, G.Adj y (f k)) : SixPairCompatible i j := by
  rcases six_pair_witnesses_checked i j with h | ⟨hw,hlen⟩
  · exact h
  · obtain ⟨e,he⟩ := six_pair_model_embedding f hcycle hx hy hxy
      (sixAttachment i) (sixAttachment j) hi hj
    exact False.elim (noLongCycle_excludes_word_embedding hshort e he _ hw hlen)

end Cycle12
