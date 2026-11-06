import Cycle12.RationalCutProfile
import Cycle12.Foundations.MixedCoverCut

namespace Cycle12
open SimpleGraph Finset Real Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def CoverSparseCutIrreducible (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → 2*(S.card:ℝ) ≤ Fintype.card V →
    coverCutThreshold (Fintype.card V) (Fintype.card G.edgeSet) ((S.card:ℝ)/Fintype.card V) ≤ cutSize G S

theorem cover_irreducible_cut_profile (G : SimpleGraph V) (C : CoverCutProfileCertificate)
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxl : C.xl ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ C.xh)
    (hI : CoverSparseCutIrreducible G) (S : Finset V)
    (hS : (S.card:ℝ) ≤ C.side*(Fintype.card V:ℝ)) :
    C.alpha*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤ cutSize G S := by
  by_cases hz : S.card=0
  · rw [hz,Nat.cast_zero,mul_zero]
    positivity
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hy : (0:ℝ) < (S.card:ℝ)/Fintype.card V := div_pos hcard hn
  have hside := (div_le_iff₀ hn).mpr hS
  have hb := cover_profile_cut_threshold_lower C hn hm hxl hxh hy hside
  rw [div_mul_cancel₀ _ hn.ne'] at hb
  apply hb.trans
  apply hI S (card_pos.mp (Nat.pos_of_ne_zero hz))
  have hh := mul_le_mul_of_nonneg_right C.side_half hn.le
  linarith only [hS,hh]

theorem cover_irreducible_expansion (G : SimpleGraph V)
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxmax : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ 17/250)
    (hI : CoverSparseCutIrreducible G) (S : Finset V)
    (hS : 2*(S.card:ℝ) ≤ Fintype.card V) :
    coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤ cutSize G S := by
  have hh := cover_irreducible_cut_profile G coverBasicCutProfile hn hm
    (cover_graph_x_pos hn hm).le hxmax hI S
    (show (S.card:ℝ) ≤ (1/2:ℝ)*Fintype.card V by linarith only [hS])
  simpa only [coverBasicCutProfile,one_mul] using hh

theorem cover_rational_irreducible_cut_profile (G : SimpleGraph V) (c : RatCutProfile) (hc : c.Valid)
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxl : (c.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.xh:ℝ))
    (hI : CoverSparseCutIrreducible G) (S : Finset V)
    (hS : (S.card:ℝ) ≤ (c.side:ℝ)*(Fintype.card V:ℝ)) :
    max 1 (c.alpha:ℝ)*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*S.card ≤ cutSize G S := by
  let C := c.realCertificate hc
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24⟩
  have hraw := cover_irreducible_cut_profile G C hn hm hxl hxh hI S hS
  by_cases ha : 1 ≤ (c.alpha:ℝ)
  · rw [max_eq_right ha]
    exact hraw
  · rw [max_eq_left (le_of_not_ge ha),one_mul]
    apply cover_irreducible_expansion G hn hm (hxh.trans C.xmax) hI S
    have hh := mul_le_mul_of_nonneg_right C.side_half hn.le
    change (c.side:ℝ)*(Fintype.card V:ℝ) ≤ (1/2:ℝ)*Fintype.card V at hh
    linarith only [hS,hh]

theorem cover_graph_sparse_cut_payment (G : SimpleGraph V) (S : Finset V)
    (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hB : (43/10)*(Fintype.card V:ℝ)*cubeScale (Fintype.card G.edgeSet) ≤ (Fintype.card G.edgeSet:ℝ))
    (hcut : (cutSize G S:ℝ) ≤ coverCutThreshold (Fintype.card V) (Fintype.card G.edgeSet)
      ((S.card:ℝ)/Fintype.card V)) :
    coverGraphBudget S.card (Fintype.card (G.induce (S:Set V)).edgeSet)+
      coverGraphBudget (Sᶜ : Finset V).card (Fintype.card (G.induce ((Sᶜ : Finset V):Set V)).edgeSet)+
      cutSize G S ≤ coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet) := by
  have hsize := twice_graph_edges_le_order_sq G
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  have hs : (S.card:ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ S
  have hy : (0:ℝ) ≤ (S.card:ℝ)/Fintype.card V := by positivity
  have hy1 : (S.card:ℝ)/Fintype.card V ≤ 1 := (div_le_one hn).mpr hs
  have he : (Fintype.card (G.induce (S:Set V)).edgeSet:ℝ)+
      (Fintype.card (G.induce ((Sᶜ : Finset V):Set V)).edgeSet:ℝ)+(cutSize G S:ℝ)=
      (Fintype.card G.edgeSet:ℝ) := by
    simp only [Set.fintypeCard_eq_ncard]
    exact_mod_cast induced_cut_edge_partition G S
  have he1 := Nat.cast_nonneg (α:=ℝ) (Fintype.card (G.induce (S:Set V)).edgeSet)
  have he2 := Nat.cast_nonneg (α:=ℝ) (Fintype.card (G.induce ((Sᶜ : Finset V):Set V)).edgeSet)
  have hp := cover_cut_pays_children hn.le hm hy hy1 he1 he2
    (Nat.cast_nonneg (α:=ℝ) (cutSize G S)) (by linarith only [he,he1,he2])
    (by linarith only [he]) hB hcut
  have hn1 : (S.card:ℝ)/Fintype.card V*Fintype.card V=S.card := div_mul_cancel₀ _ hn.ne'
  have hn2 : (1-(S.card:ℝ)/Fintype.card V)*Fintype.card V=(Sᶜ : Finset V).card := by
    have hh : (S.card:ℝ)+(Sᶜ : Finset V).card=Fintype.card V := by exact_mod_cast card_add_card_compl S
    rw [sub_mul,one_mul,hn1]
    linarith only [hh]
  rw [hn1,hn2] at hp
  exact hp

end
end Cycle12
