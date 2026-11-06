import Cycle12.Foundations.ReservoirRouting

/-! Small-side anchoring and branch cuts pay every directed-source cut. -/
namespace Cycle13.ReservoirPorts
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma internal_cut_relative_compl (G : SimpleGraph V) (U S : Finset V) (hS : S ⊆ U) :
    cutSize (internalGraph G U) (U \ S) = cutSize (internalGraph G U) S := by
  have he : cutGraph (internalGraph G U) (U \ S) = cutGraph (internalGraph G U) S := by
    ext x y
    change ((G.Adj x y ∧ x ∈ U ∧ y ∈ U) ∧ _) ↔
      ((G.Adj x y ∧ x ∈ U ∧ y ∈ U) ∧ _)
    simp only [mem_coe, Set.mem_compl_iff, mem_sdiff]
    tauto
  exact congrArg (fun H : SimpleGraph V => H.edgeSet.ncard) he

lemma branch_partition (B U S : Finset V) (hBU : B ⊆ U) :
    (B ∩ (U \ S)).card + (B ∩ S).card = B.card := by
  have he : B ∩ (U \ S) = B \ (B ∩ S) := by
    ext v
    simp only [mem_inter, mem_sdiff]
    constructor
    · rintro ⟨hB, hU, hnS⟩
      exact ⟨hB, fun h => hnS h.2⟩
    · rintro ⟨hB, h⟩
      exact ⟨hB, hBU hB, fun hS => h ⟨hB,hS⟩⟩
  rw [he]
  exact card_sdiff_add_card_eq_card inter_subset_left

/-- Large reservoir sides are paid for by the complementary branch cut
and the total capacity; small sides are paid for by external anchoring. -/
theorem cutCondition_of_small_sides (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (hBU : B ⊆ U) (hcap : A.card ≤ c * B.card)
    (hanchor : ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U →
      2 * S.card ≤ U.card →
      Y.card ≤ cutSize (internalGraph G U) S + (G.interedges Y (U \ S)).card)
    (hbranch : ∀ S : Finset V, S ⊆ U → 2 * S.card ≤ U.card →
      c * (B ∩ S).card ≤ cutSize (internalGraph G U) S) :
    CutCondition G A U B c := by
  intro Y hYA S hSU
  by_cases hS : 2 * S.card ≤ U.card
  · exact (hanchor Y hYA S hSU hS).trans (Nat.le_add_right _ _)
  · have hSc : 2 * (U \ S).card ≤ U.card := by
      have h := card_sdiff_add_card_eq_card hSU
      omega
    have hb := hbranch (U \ S) sdiff_subset hSc
    rw [internal_cut_relative_compl G U S hSU] at hb
    have hp := branch_partition B U S hBU
    have hm : c * (B ∩ (U \ S)).card + c * (B ∩ S).card = c * B.card := by
      rw [← Nat.mul_add, hp]
    have hY := card_le_card hYA
    omega

/-- Full routing from the two small-side certificates used in the paper. -/
theorem exists_routing_of_small_sides (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (hAU : Disjoint A U) (hBU : B ⊆ U) (hcap : A.card ≤ c * B.card)
    (hanchor : ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U →
      2 * S.card ≤ U.card →
      Y.card ≤ cutSize (internalGraph G U) S + (G.interedges Y (U \ S)).card)
    (hbranch : ∀ S : Finset V, S ⊆ U → 2 * S.card ≤ U.card →
      c * (B ∩ S).card ≤ cutSize (internalGraph G U) S) :
    Nonempty (Routing G A U B c) :=
  exists_routing G A U B c hAU hBU
    (cutCondition_of_small_sides G A U B c hBU hcap hanchor hbranch)

/-- If reservoir cuts retain a fraction `f`, then external anchoring of
strength `L` survives whenever `f*L ≥ 1`. Attachment edges are unchanged. -/
theorem retained_anchor (G F : SimpleGraph V) (A U : Finset V)
    {f L : ℝ} (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f * L)
    (hattach : ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U →
      (G.interedges Y (U \ S)).card = (F.interedges Y (U \ S)).card)
    (hretain : ∀ S : Finset V, S ⊆ U →
      f * cutSize (internalGraph G U) S ≤ (cutSize (internalGraph F U) S : ℝ))
    (hanchor : ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U →
      2 * S.card ≤ U.card →
      L * Y.card ≤ (cutSize (internalGraph G U) S : ℝ) + (G.interedges Y (U \ S)).card) :
    ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U → 2 * S.card ≤ U.card →
      Y.card ≤ cutSize (internalGraph F U) S + (F.interedges Y (U \ S)).card := by
  intro Y hYA S hSU hsmall
  have h₀ := hanchor Y hYA S hSU hsmall
  have h₁ := mul_le_mul_of_nonneg_left h₀ hf₀
  have h₂ := hretain S hSU
  have h₃ := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg Y.card : (0:ℝ) ≤ Y.card)
  have h₄ := mul_le_mul_of_nonneg_right hf₁
    (Nat.cast_nonneg (G.interedges Y (U \ S)).card : (0:ℝ) ≤ _)
  rw [hattach Y hYA S hSU] at h₁ h₄
  have h : (Y.card : ℝ) ≤ cutSize (internalGraph F U) S + (F.interedges Y (U \ S)).card := by
    nlinarith
  exact_mod_cast h

end
end Cycle13.ReservoirPorts
