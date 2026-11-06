import Cycle12.Foundations.ReservoirLift

namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem degree_le_cut_add_erase (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v∈S) :
    G.degree v ≤ (cutGraph G S).degree v+(S.card-1) := by
  have hsub : G.neighborSet v ⊆ (cutGraph G S).neighborSet v∪(S.erase v:Set V) := by
    intro w hw
    by_cases hs : w∈S
    · exact Or.inr (mem_erase.mpr ⟨hw.ne.symm,hs⟩)
    · exact Or.inl ⟨hw,Or.inl ⟨hv,hs⟩⟩
  have hh := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  simpa only [ncard_neighborSet,Set.ncard_coe_finset,card_erase_of_mem hv] using hh

theorem cut_lower_from_min_degree (G : SimpleGraph V) (S : Finset V) {δ : ℝ}
    (hdeg : ∀ v∈S, δ ≤ (G.degree v:ℝ)) :
    (S.card:ℝ)*(δ+1-S.card) ≤ (cutSize G S:ℝ) := by
  by_cases hs : S.Nonempty
  · have hcard : 1 ≤ S.card := hs.card_pos
    have hp : ∀ v∈S, δ+1-S.card ≤ ((cutGraph G S).degree v:ℝ) := by
      intro v hv
      have hh := degree_le_cut_add_erase G S hv
      have hr : (G.degree v:ℝ) ≤ (cutGraph G S).degree v+(S.card:ℝ)-1 := by
        have hz := (Nat.cast_le (α:=ℝ)).mpr hh
        simpa only [Nat.cast_add,Nat.cast_sub hcard,Nat.cast_one,add_sub_assoc] using hz
      linarith [hdeg v hv]
    calc
      _ = ∑ _v∈S, (δ+1-(S.card:ℝ)) := by simp; ring
      _ ≤ ∑ v∈S, ((cutGraph G S).degree v:ℝ) := sum_le_sum hp
      _ = _ := by rw [cutSize_eq_sum,Nat.cast_sum]
  · have hz : S=∅ := not_nonempty_iff_eq_empty.mp hs
    subst S
    simp only [card_empty,Nat.cast_zero,zero_mul]
    exact Nat.cast_nonneg _

theorem mincut_of_degree_and_expansion (G : SimpleGraph V) {δ β : ℝ}
    (hβ : 1 ≤ β) (hdeg : ∀ v, δ ≤ (G.degree v:ℝ))
    (hexp : ∀ S : Finset V, 2*S.card ≤ Fintype.card V → β*S.card ≤ (cutSize G S:ℝ)) :
    ∀ S : Finset V, S.Nonempty → S≠univ → δ ≤ (cutSize G S:ℝ) := by
  have hsmall : ∀ S : Finset V, S.Nonempty → 2*S.card ≤ Fintype.card V →
      δ ≤ (cutSize G S:ℝ) := by
    intro S hs hS
    have hc : (1:ℝ) ≤ S.card := by exact_mod_cast hs.card_pos
    by_cases hδ : (S.card:ℝ) ≤ δ
    · have hh := cut_lower_from_min_degree G S (fun v _ => hdeg v)
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hδ)]
    · have hh := hexp S hS
      have hm := mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg (α:=ℝ) S.card)
      linarith
  intro S hs hproper
  by_cases hS : 2*S.card ≤ Fintype.card V
  · exact hsmall S hs hS
  · have hcompl : Sᶜ.Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro hz
      apply hproper
      ext v
      simp only [mem_univ,iff_true]
      by_contra hv
      have hh : v∈Sᶜ := mem_compl.mpr hv
      rw [hz] at hh
      exact notMem_empty v hh
    have hside : 2*Sᶜ.card ≤ Fintype.card V := by
      have hh := card_add_card_compl S
      omega
    simpa only [cutSize_compl] using hsmall Sᶜ hcompl hside

theorem reservoirSide_image (U : Finset V) (S : Finset U) :
    reservoirSide U (S.image Subtype.val)=S := by
  ext v
  rw [mem_reservoirSide]
  constructor
  · intro hv
    obtain ⟨w,hw,he⟩ := mem_image.mp hv
    exact Subtype.val_injective he ▸ hw
  · intro hv
    exact mem_image.mpr ⟨v,hv,rfl⟩

theorem induced_cutSize_image (G : SimpleGraph V) (U : Finset V) (S : Finset U) :
    cutSize (G.induce (U:Set V)) S=
      (G.interedges (S.image Subtype.val) (U\S.image Subtype.val)).card := by
  have hSU : S.image Subtype.val⊆U := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hh := reservoirLift_cutSize U (S.image Subtype.val) (G.induce (U:Set V))
  rw [reservoirSide_image,reservoirLift_induce,internal_cutSize G U _ hSU] at hh
  exact hh.symm

theorem sample_induced_degree (G : SimpleGraph V) (U : Finset V) (v : U) :
    (G.induce (U:Set V)).degree v=(neighborsIn G v.val U).card := by
  have hh := reservoirLift_degree U (G.induce (U:Set V)) v
  rw [reservoirLift_induce,internal_degree G U v.property] at hh
  exact hh.symm

theorem sample_induced_edge_count (G : SimpleGraph V) (U : Finset V) :
    (G.induce (U:Set V)).edgeSet.ncard=sampledEdgeCount G (U:Set V) := by
  have he : Subtype.val '' {e : G.edgeSet | (edgeVertexSet G e:Set V)⊆(U:Set V)}=
      (G.edgeFinset.filter (fun e => e.toFinset⊆U):Set (Sym2 V)) := by
    ext e
    constructor
    · rintro ⟨a,ha,rfl⟩
      apply mem_filter.mpr
      exact ⟨G.mem_edgeFinset.mpr a.property,ha⟩
    · intro h
      obtain ⟨he,hU⟩ := mem_filter.mp h
      exact ⟨⟨e,G.mem_edgeFinset.mp he⟩,hU,rfl⟩
  have hh := congrArg Set.ncard he
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset,
    G.card_filter_edgeFinset_toFinset_subset] at hh
  simpa only [sampledEdgeCount,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hh.symm

theorem sample_induced_expansion (G : SimpleGraph V) (U : Finset V) {β : ℝ}
    (h : SampleCutExpansion G U β) :
    ∀ S : Finset U, 2*S.card ≤ Fintype.card U →
      β*S.card ≤ (cutSize (G.induce (U:Set V)) S:ℝ) := by
  intro S hS
  have hSU : S.image Subtype.val⊆U := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hcard : (S.image Subtype.val).card=S.card := card_image_of_injective _ Subtype.val_injective
  rw [induced_cutSize_image]
  have hh := h (S.image Subtype.val) hSU (by simpa only [hcard,Fintype.card_coe] using hS)
  simpa only [hcard] using hh

theorem GoodVertexSample.induced_mincut (G : SimpleGraph V) (U : Finset V)
    {δ β L lower upper edgeLower incidentUpper : ℝ}
    (h : GoodVertexSample G U δ β L lower upper edgeLower incidentUpper) (hβ : 1 ≤ β) :
    ∀ S : Finset U, S.Nonempty → S≠univ → δ ≤ (cutSize (G.induce (U:Set V)) S:ℝ) :=
  mincut_of_degree_and_expansion _ hβ
    (fun v => by
      have he := sample_induced_degree G U v
      have hh := h.neighbors v.val
      rw [← he] at hh
      simpa only [SimpleGraph.degree,SimpleGraph.neighborFinset,Set.toFinset_card,
        ← Nat.card_eq_fintype_card] using hh)
    (sample_induced_expansion G U h.cuts)

end
end Cycle13
