import Cycle12.SupportedParityForest12
import Cycle12.Foundations.CutPartition

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem core_external_cut_ledger (G : SimpleGraph V) (U T : Finset V) :
    ((G.interedges (T∩U) (U\T)).card:ℝ)+((G.interedges (T\U) (U\T)).card:ℝ)≤
      (cutSize G T:ℝ) := by
  have he : (T∩U)∪(T\U)=T := by
    ext v
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto
  have hd : Disjoint (T∩U) (T\U) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
  have hh := interedges_card_union_left G (T∩U) (T\U) (U\T) hd
  rw [he] at hh
  have hsub : G.interedges T (U\T)⊆G.interedges T Tᶜ := by
    intro e he
    obtain ⟨he₁,he₂,ha⟩ := G.mem_interedges_iff.mp he
    exact G.mem_interedges_iff.mpr ⟨he₁,mem_compl.mpr (mem_sdiff.mp he₂).2,ha⟩
  have hc := Finset.card_le_card hsub
  rw [hh,←cutSize_eq_interedges] at hc
  exact_mod_cast hc

theorem high_centers_cross_cut (G : SimpleGraph V) (U T : Finset V) {d : ℝ}
    (hdeg : ∀ v,v∉U → d≤((neighborsIn G v U).card:ℝ)) :
    (d-(T∩U).card)*((T\U).card:ℝ)≤((G.interedges (T\U) (U\T)).card:ℝ) := by
  have hpart : U\(T∩U)=U\T := by
    ext v
    simp only [mem_sdiff,mem_inter]
    tauto
  have hpoint (v : V) (hv : v∈T\U) :
      d-(T∩U).card≤((neighborsIn G v (U\T)).card:ℝ) := by
    have hh := neighborsIn_partition_card G v (T∩U) U inter_subset_right
    rw [hpart] at hh
    have hb : (neighborsIn G v (T∩U)).card≤(T∩U).card := card_le_card (filter_subset _ _)
    have hn := hdeg v (mem_sdiff.mp hv).2
    have hhR : ((neighborsIn G v U).card:ℝ)=
        ((neighborsIn G v (T∩U)).card:ℝ)+((neighborsIn G v (U\T)).card:ℝ) := by exact_mod_cast hh
    have hbR : ((neighborsIn G v (T∩U)).card:ℝ)≤(T∩U).card := by exact_mod_cast hb
    linarith only [hn,hhR,hbR]
  have hh := Finset.sum_le_sum (fun v hv => hpoint v hv)
  rw [card_interedges_eq_sum_neighborsIn,Nat.cast_sum]
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

theorem high_center_oriented_expansion (G : SimpleGraph V) (U T : Finset V)
    {h d : ℝ} (hh : 0≤h) (hd : 0≤d)
    (hexp : OAI.ErdosGallai.Scale.CutExpansionOn G U h)
    (hdeg : ∀ v,v∉U → d≤((neighborsIn G v U).card:ℝ))
    (hfew : (Uᶜ.card:ℝ)≤d/2) (hsmall : 2*(T∩U).card≤U.card) :
    (min h d/2)*(T.card:ℝ)≤(cutSize G T:ℝ) := by
  have he : U\(T∩U)=U\T := by
    ext v
    simp only [mem_sdiff,mem_inter]
    tauto
  have hsub : T∩U⊆U := inter_subset_right
  have hmin : ((T∩U).card:ℝ)≤(U\(T∩U)).card := by
    rw [card_sdiff_of_subset hsub]
    exact_mod_cast (show (T∩U).card≤U.card-(T∩U).card by omega)
  have hcore := hexp (T∩U) hsub
  rw [min_eq_left hmin] at hcore
  change h*((T∩U).card:ℝ)≤((G.interedges (T∩U) (U\(T∩U))).card:ℝ) at hcore
  rw [he] at hcore
  have hcross := high_centers_cross_cut G U T hdeg
  have hledger := core_external_cut_ledger G U T
  have hsize : T.card=(T∩U).card+(T\U).card := by
    have ht : (T∩U)∪(T\U)=T := by ext v; simp only [mem_union,mem_inter,mem_sdiff]; tauto
    have hdi : Disjoint (T∩U) (T\U) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
    exact (congrArg Finset.card ht).symm.trans (card_union_of_disjoint hdi)
  have hsizeR : (T.card:ℝ)=((T∩U).card:ℝ)+(T\U).card := by exact_mod_cast hsize
  have hminh := min_le_left h d
  have hmind := min_le_right h d
  have hmin0 : 0 ≤ min h d := le_min hh hd
  have hA0 : (0:ℝ)≤(T∩U).card := Nat.cast_nonneg _
  have hY0 : (0:ℝ)≤(T\U).card := Nat.cast_nonneg _
  rw [hsizeR]
  by_cases hA : ((T∩U).card:ℝ)≤d/2
  · have h1 := mul_le_mul_of_nonneg_right hminh hA0
    have h2 := mul_le_mul_of_nonneg_right hmind hY0
    have h3 := mul_nonneg (show 0≤d/2-((T∩U).card:ℝ) by linarith) hY0
    nlinarith only [hcore,hcross,hledger,hsizeR,h1,h2,h3,hmin0,hA0]
  · have hY : ((T\U).card:ℝ)≤Uᶜ.card := by
      exact_mod_cast card_le_card (show T\U⊆Uᶜ from fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2)
    have h1 := mul_le_mul_of_nonneg_right hminh hA0
    have h2 := mul_nonneg hmin0 (show 0≤((T∩U).card:ℝ)-(T\U).card by linarith)
    have hcross0 : (0:ℝ)≤(G.interedges (T\U) (U\T)).card := Nat.cast_nonneg _
    nlinarith only [hcore,hledger,hsizeR,h1,h2,hcross0]

/-- Adding few vertices, each with many neighbors in the expanding core,
preserves half the smaller expansion. Extra exterior edges can only help. -/
theorem high_center_cut_extension (G : SimpleGraph V) (U : Finset V)
    {h d : ℝ} (hh : 0≤h) (hd : 0≤d)
    (hexp : OAI.ErdosGallai.Scale.CutExpansionOn G U h)
    (hdeg : ∀ v,v∉U → d≤((neighborsIn G v U).card:ℝ))
    (hfew : (Uᶜ.card:ℝ)≤d/2) : OAI.ErdosGallai.CutExpansion G (min h d/2) := by
  intro S
  rw [←cutSize_eq_interedges]
  have hnonneg : 0 ≤ min h d/2 := div_nonneg (le_min hh hd) (by norm_num)
  by_cases hsmall : 2*(S∩U).card≤U.card
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hnonneg).trans
      (high_center_oriented_expansion G U S hh hd hexp hdeg hfew hsmall)
  · have hsplit : (S∩U).card+(Sᶜ∩U).card=U.card := by
      have he : (S∩U)∪(Sᶜ∩U)=U := by ext v; simp only [mem_union,mem_inter,mem_compl]; tauto
      have hdis : Disjoint (S∩U) (Sᶜ∩U) := by
        apply Finset.disjoint_left.mpr
        intro v hv hw
        exact (mem_compl.mp (mem_inter.mp hw).1) (mem_inter.mp hv).1
      rw [←card_union_of_disjoint hdis,he]
    have hs : 2*(Sᶜ∩U).card≤U.card := by omega
    have hb := high_center_oriented_expansion G U Sᶜ hh hd hexp hdeg hfew hs
    rw [cutSize_compl] at hb
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hnonneg).trans hb

end
end Cycle12
