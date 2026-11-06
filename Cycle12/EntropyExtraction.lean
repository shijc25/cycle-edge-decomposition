import Cycle12.EntropyPotential
import Cycle12.SupportedEdges

namespace Cycle12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem entropy_cut_extraction (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) (σ : ℝ) (hσ : 1 ≤ σ) :
    ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V),
      (∀ P ∈ R, P.vertices ⊆ A ∧ σ < (P.vertices.card:ℝ) ∧ 2 ≤ P.vertices.card ∧
        CutExpansionOn P.graph P.vertices σ) ∧
      R.Pairwise (fun P Q => Disjoint P.vertices Q.vertices) ∧
      GraphPartition G (H :: R.map AssignedPiece.graph) ∧
      SupportedOn H A ∧
      (edgeCount H : ℝ) ≤ entropyPotential σ A.card := by
  classical
  induction hcard : A.card using Nat.strong_induction_on generalizing A G with
  | h n ih =>
    have hσpos : 0 < σ := by linarith only [hσ]
    by_cases hsmall : (A.card:ℝ) ≤ σ
    · refine ⟨[],G,by simp,by simp,?_,hG,?_⟩
      · intro x y; simp
      · rw [← hcard,entropy_potential_small hσpos hsmall]
        exact supported_edge_count_le_square G A hG
    by_cases hexp : CutExpansionOn G A σ
    · refine ⟨[⟨A,G,hG⟩],⊥,?_,by simp,?_,?_,?_⟩
      · intro P hP
        have he := List.mem_singleton.mp hP
        subst P
        exact ⟨fun _ h => h,lt_of_not_ge hsmall,by
          change 2 ≤ A.card
          have hh : (1:ℝ) < A.card := hσ.trans_lt (lt_of_not_ge hsmall)
          exact_mod_cast hh,hexp⟩
      · intro x y; simp
      · intro x y h; exact False.elim h
      · simp only [edgeCount_bot,Nat.cast_zero]
        exact entropy_potential_nonneg hσpos (Nat.cast_nonneg _)
    unfold CutExpansionOn at hexp
    push Not at hexp
    obtain ⟨U,hU,hcut⟩ := hexp
    have hdisUB : Disjoint U (A\U) := Finset.disjoint_left.mpr
      (fun _ hu hb => (Finset.mem_sdiff.mp hb).2 hu)
    have hcnt : (0 : ℝ) ≤ cutCount G U (A\U) := Nat.cast_nonneg _
    have hUpos : 0 < U.card := by
      by_contra h
      have hz : U.card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_left (0:ℝ) ((A\U).card:ℝ)]
    have hBpos : 0 < (A\U).card := by
      by_contra h
      have hz : (A\U).card = 0 := by omega
      simp [hz] at hcut
      linarith [min_le_right (U.card:ℝ) (0:ℝ)]
    have hcardSum := Finset.card_sdiff_add_card_eq_card hU
    have hUlt : U.card < n := by omega
    have hBlt : (A\U).card < n := by omega
    obtain ⟨R₁,H₁,hR₁,hd₁,hp₁,hs₁,hc₁⟩ := ih U.card hUlt (restrictGraph G U) U
      (restrictGraph_supported G U) rfl
    obtain ⟨R₂,H₂,hR₂,hd₂,hp₂,hs₂,hc₂⟩ := ih (A\U).card hBlt (restrictGraph G (A\U)) (A\U)
      (restrictGraph_supported G (A\U)) rfl
    let K := crossingGraph G U (A\U)
    obtain ⟨hcover,hdis₁,hdis₂,hdis₃⟩ := cut_split_properties G A U hG hU
    refine ⟨R₁++R₂,K ⊔ H₁ ⊔ H₂,?_,?_,?_,?_,?_⟩
    · intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · obtain ⟨hPA,hPσ,hPc,hPe⟩ := hR₁ P hP
        exact ⟨hPA.trans hU,hPσ,hPc,hPe⟩
      · obtain ⟨hPA,hPσ,hPc,hPe⟩ := hR₂ P hP
        exact ⟨hPA.trans Finset.sdiff_subset,hPσ,hPc,hPe⟩
    · apply List.pairwise_append.mpr
      refine ⟨hd₁,hd₂,?_⟩
      intro P hP Q hQ
      exact hdisUB.mono
        (hR₁ P hP).1 (hR₂ Q hQ).1
    · simpa only [List.map_append] using partition_combine hp₁ hp₂ hcover hdis₁ hdis₂ hdis₃
    · intro x y h
      rcases h with (h|h)|h
      · exact hG h.1
      · exact ⟨hU (hs₁ h).1,hU (hs₁ h).2⟩
      · exact ⟨(Finset.mem_sdiff.mp (hs₂ h).1).1,(Finset.mem_sdiff.mp (hs₂ h).2).1⟩
    · have hcardK : edgeCount K = cutCount G U (A\U) :=
        crossing_count G U (A\U) hdisUB
      have hcost : (edgeCount (K⊔H₁⊔H₂) : ℝ) ≤
          edgeCount K + edgeCount H₁ + edgeCount H₂ := by
        exact_mod_cast (edgeCount_sup_le (K⊔H₁) H₂).trans
          (Nat.add_le_add_right (edgeCount_sup_le K H₁) _)
      have hsimple : (cutCount G U (A\U):ℝ) ≤ (U.card:ℝ)*(A\U).card := by
        exact_mod_cast G.card_interedges_le_mul U (A\U)
      have hcutbound := le_min hsimple hcut.le
      have hpot := entropy_potential_split hσpos (Nat.cast_nonneg (α:=ℝ) U.card)
        (Nat.cast_nonneg (α:=ℝ) (A\U).card)
      have he : (U.card:ℝ)+(A\U).card=(A.card:ℝ) := by
        exact_mod_cast (by omega : U.card+(A\U).card=A.card)
      rw [he] at hpot
      rw [hcardK] at hcost
      rw [← hcard]
      linarith only [hcost,hcutbound,hpot,hc₁,hc₂]

end
end Cycle12
