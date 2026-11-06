import Cycle12.Foundations.MatchingObstruction
import Cycle12.Foundations.MultipartiteImmersion
import Cycle12.Foundations.ImmersionMap

/-! Component counting for the DY matching obstruction, and its small
common-neighbour block. Missing-neighbour degree excludes the vertex itself,
exactly as in GLW's notation. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma components_except_count (H : SimpleGraph V) (S K : Set V) (hK : K ∈ comps H S) :
    (comps H S).ncard ≤ (S \ K).ncard+1 := by
  classical
  let T := comps H S \ {K}
  let f : T → ↥(S \ K) := fun J => ⟨(comps_nonempty J.property.1).choose,by
    have hv := (comps_nonempty J.property.1).choose_spec
    refine ⟨comps_subset J.property.1 hv,?_⟩
    intro hvK
    exact J.property.2 (comps_eq_of_mem J.property.1 hK hv hvK)⟩
  have hf : Function.Injective f := by
    intro J J' he
    apply Subtype.ext
    apply comps_eq_of_mem J.property.1 J'.property.1
      (comps_nonempty J.property.1).choose_spec
    have hv := congrArg Subtype.val he
    change (comps_nonempty J.property.1).choose=(comps_nonempty J'.property.1).choose at hv
    exact hv ▸ (comps_nonempty J'.property.1).choose_spec
  have hc : T.ncard ≤ (S \ K).ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf
  have hk := Set.ncard_sdiff_singleton_add_one hK
  change T.ncard+1=(comps H S).ncard at hk
  omega

lemma components_sdiff_component (H : SimpleGraph V) (S K : Set V)
    (hK : K ∈ comps H S) : comps H (S \ K)=comps H S \ {K} := by
  rw [comps_of_closed Set.sdiff_subset (closed_compl (comps_closed hK))]
  ext J
  constructor
  · rintro ⟨hJ,hsub⟩
    refine ⟨hJ,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := comps_nonempty hJ
    exact (hsub hv).2 (heq ▸ hv)
  · rintro ⟨hJ,hne⟩
    refine ⟨hJ,fun v hv => ⟨comps_subset hJ hv,?_⟩⟩
    intro hvK
    exact hne (comps_eq_of_mem hJ hK hv hvK)

lemma component_complement_card (H : SimpleGraph V) (S : Set V) (v : S) :
    (S \ cc H S v.val).ncard =
      (univ.filter (fun w : S => (H.induce S).connectedComponentMk w ≠
        (H.induce S).connectedComponentMk v)).card := by
  classical
  have heq : S \ cc H S v.val = Subtype.val ''
      {w : S | (H.induce S).connectedComponentMk w ≠ (H.induce S).connectedComponentMk v} := by
    ext w
    constructor
    · rintro ⟨hwS,hwK⟩
      refine ⟨⟨w,hwS⟩,?_,rfl⟩
      intro hc
      exact hwK ⟨v.property,hwS,(ConnectedComponent.eq.mp hc).symm⟩
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      rintro ⟨hv,hw',hreach⟩
      exact hw (ConnectedComponent.eq.mpr hreach.symm)
  rw [heq,Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simp

lemma component_block_degree (H : SimpleGraph V) (U K : Set V)
    (hK : K ∈ comps H Uᶜ) (hcount : U.ncard < (comps H Uᶜ).ncard)
    {v : V} (hv : v ∈ Uᶜ \ K) : H.degree v ≤ (Uᶜ \ K).ncard := by
  classical
  let W := Uᶜ \ K
  let J := cc H W v
  have hJ : J ∈ comps H W := cc_mem_comps hv
  have hvJ : v ∈ J := mem_cc_self hv
  have hc := components_except_count H W J hJ
  have hcomps : (comps H W).ncard+1=(comps H Uᶜ).ncard := by
    dsimp [W]
    rw [components_sdiff_component H Uᶜ K hK]
    exact Set.ncard_sdiff_singleton_add_one hK
  have hneighbors : H.neighborSet v ⊆ U ∪ (J \ {v}) := by
    intro w hw
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · apply Or.inr
      have hwW : w ∈ W := closed_compl (comps_closed hK) v hv w hwU hw
      exact ⟨mem_cc_of_adj hvJ hwW hw,hw.ne.symm⟩
  have hd := Set.ncard_le_ncard hneighbors
  rw [H.ncard_neighborSet] at hd
  have hu := Set.ncard_union_le U (J \ {v})
  have hj := Set.ncard_sdiff_singleton_add_one hvJ
  have hw := Set.ncard_sdiff_add_ncard_of_subset (comps_subset hJ)
  change H.degree v ≤ W.ncard
  omega

theorem small_component_complement_of_no_strong_model (G : SimpleGraph V) (t : ℕ)
    (hno : ¬ Nonempty (StrongCliqueImmersion t G)) (S : Set V) (hS : S.Nonempty) :
    ∃ v : S, (S \ cc Gᶜ S v.val).ncard < t := by
  classical
  letI : Nonempty S := ⟨⟨hS.choose,hS.choose_spec⟩⟩
  by_contra! hnone
  let H := Gᶜ.induce S
  obtain ⟨M⟩ := strong_model_of_complete_multipartite (G.induce S)
    H.connectedComponentMk t (by
      intro x y hxy
      have hne : x.val ≠ y.val := fun he => hxy (congrArg H.connectedComponentMk (Subtype.ext he))
      by_contra hG
      apply hxy
      apply ConnectedComponent.eq.mpr
      apply Adj.reachable
      exact (compl_adj G x.val y.val).mpr ⟨hne,hG⟩) (by
      intro v
      rw [← component_complement_card]
      exact hnone v)
  exact hno ⟨M.mapCopy (SimpleGraph.Copy.induce G S)⟩

theorem exists_DY_small_block_of_partition_bound (G : SimpleGraph V) (t : ℕ)
    (hblocks : ∀ S : Set V, S.Nonempty → ∃ v : S, (S \ cc Gᶜ S v.val).ncard < t)
    (hperfect : ¬ HasPerfectMatchingOn Gᶜ Set.univ) (hhypo : ¬ Hypomatchable Gᶜ) :
    ∃ W L : Set V, W.Nonempty ∧ W.ncard < t ∧ Disjoint W L ∧
      Nat.card V ≤ L.ncard+2*W.ncard ∧
      (∀ v ∈ W, Gᶜ.degree v ≤ W.ncard) ∧
      ∀ v ∈ W, ∀ w ∈ L, G.Adj v w := by
  classical
  obtain ⟨U,_,hcount,htwo⟩ := exists_matching_obstruction Gᶜ hperfect hhypo
  have hS : Uᶜ.Nonempty := by
    have hc : (comps Gᶜ Uᶜ).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
    obtain ⟨K,hK⟩ := hc
    obtain ⟨v,hv⟩ := comps_nonempty hK
    exact ⟨v,comps_subset hK hv⟩
  obtain ⟨v,hvsmall⟩ := hblocks Uᶜ hS
  let K := cc Gᶜ Uᶜ v.val
  let W := Uᶜ \ K
  have hK : K ∈ comps Gᶜ Uᶜ := cc_mem_comps v.property
  have hc := components_except_count Gᶜ Uᶜ K hK
  change (comps Gᶜ Uᶜ).ncard ≤ W.ncard+1 at hc
  have hWU : U.ncard ≤ W.ncard := by omega
  have hWnon : W.Nonempty := (Set.ncard_pos (Set.toFinite W)).mp (by omega)
  have hsplit := Set.ncard_sdiff_add_ncard_of_subset (comps_subset hK)
  change W.ncard+K.ncard=Uᶜ.ncard at hsplit
  have htotal := Set.ncard_add_ncard_compl U
  refine ⟨W,K,hWnon,hvsmall,Set.disjoint_sdiff_left,by omega,?_,?_⟩
  · intro w hw
    have hd := component_block_degree Gᶜ U K hK hcount hw
    simp only [← ncard_neighborSet] at hd ⊢
    exact hd
  · intro x hx y hy
    have hne : x ≠ y := fun h => hx.2 (h ▸ hy)
    by_contra hG
    have hH : Gᶜ.Adj y x := (compl_adj G y x).mpr ⟨hne.symm,fun h => hG h.symm⟩
    exact hx.2 (comps_closed hK y hy x hx.1 hH)

theorem exists_DY_small_block (G : SimpleGraph V) (t : ℕ)
    (hno : ¬ Nonempty (StrongCliqueImmersion t G))
    (hperfect : ¬ HasPerfectMatchingOn Gᶜ Set.univ) (hhypo : ¬ Hypomatchable Gᶜ) :
    ∃ W L : Set V, W.Nonempty ∧ W.ncard < t ∧ Disjoint W L ∧
      Nat.card V ≤ L.ncard+2*W.ncard ∧
      (∀ v ∈ W, Gᶜ.degree v ≤ W.ncard) ∧
      ∀ v ∈ W, ∀ w ∈ L, G.Adj v w :=
  exists_DY_small_block_of_partition_bound G t
    (small_component_complement_of_no_strong_model G t hno) hperfect hhypo

end
end Cycle13
