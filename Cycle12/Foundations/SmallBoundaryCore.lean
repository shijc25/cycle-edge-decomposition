import Cycle12.Foundations.CutPartition

/-! A smallest nonempty set with boundary less than d has internal
edge connectivity at least d/2 (DY Lemma 11). -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem connected_of_positive_cuts [Nonempty V] (G : SimpleGraph V)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠univ → 0 < cutSize G S) :
    G.Connected := by
  refine ⟨?_⟩
  intro u v
  by_contra hn
  let S : Finset V := univ.filter (G.Reachable u)
  have hu : u∈S := by simp [S]
  have hv : v∉S := by simpa [S] using hn
  have hp := hcut S ⟨u,hu⟩ (fun he => hv (he ▸ mem_univ v))
  have hb : cutGraph G S=⊥ := by
    ext x y
    change (G.Adj x y ∧ (x∈(S : Set V) ∧ y∉(S : Set V) ∨
      x∉(S : Set V) ∧ y∈(S : Set V))) ↔ False
    constructor
    · rintro ⟨hxy,hS⟩
      rcases hS with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · apply hy
        exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hx).2).trans hxy.reachable⟩
      · apply hx
        exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp hy).2).trans hxy.symm.reachable⟩
    · exact False.elim
  simpa [cutSize,hb] using hp

theorem exists_minimum_small_boundary [Nonempty V] (G : SimpleGraph V) {d : ℕ}
    (hd : 0<d) :
    ∃ S : Finset V, S.Nonempty ∧ cutSize G S<d ∧
      ∀ T : Finset V, T.Nonempty → T.card<S.card → d ≤ cutSize G T := by
  have hz : cutSize G univ=0 := by
    rw [cutSize_eq_interedges]
    simp [interedges_def]
  have hex : ∃ n : ℕ, ∃ S : Finset V, S.card=n ∧ S.Nonempty ∧ cutSize G S<d :=
    ⟨Fintype.card V,univ,card_univ,univ_nonempty,by omega⟩
  obtain ⟨S,hcard,hS,hcut⟩ := Nat.find_spec hex
  refine ⟨S,hS,hcut,?_⟩
  intro T hT hsmall
  by_contra! hn
  have hle := Nat.find_min' hex (show ∃ R : Finset V,
    R.card=T.card ∧ R.Nonempty ∧ cutSize G R<d from ⟨T,rfl,hT,hn⟩)
  omega

theorem exists_small_boundary_connected_core [Nonempty V] (G : SimpleGraph V) {d : ℕ}
    (hd : 0<d) :
    ∃ S : Finset V, S.Nonempty ∧ cutSize G S<d ∧
      (G.induce (S : Set V)).Connected ∧
      ∀ T : Finset S, T.Nonempty → T≠univ →
        d ≤ 2*cutSize (G.induce (S : Set V)) T := by
  obtain ⟨S,hS,hboundary,hmin⟩ := exists_minimum_small_boundary G hd
  letI : Nonempty S := ⟨⟨hS.choose,hS.choose_spec⟩⟩
  have hc : ∀ T : Finset S, T.Nonempty → T≠univ →
      d ≤ 2*cutSize (G.induce (S : Set V)) T := by
    intro T hT hproper
    let A : Finset V := T.image Subtype.val
    have hAS : A ⊆ S := by
      intro v hv
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
      exact x.property
    have hA : A.Nonempty := hT.image _
    have hcard : A.card=T.card := card_image_of_injective _ Subtype.val_injective
    have hAsmall : A.card<S.card := by
      have hh := card_lt_card (ssubset_univ_iff.mpr hproper)
      simpa only [card_univ,Fintype.card_coe,← hcard] using hh
    have hrest : (S\A).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro hz
      have hSA : S ⊆ A := sdiff_eq_empty_iff_subset.mp hz
      have hh := card_le_card hSA
      omega
    have hrsmall : (S\A).card<S.card := by
      have hbal := card_sdiff_add_card_eq_card hAS
      have hpos := card_pos.mpr hA
      omega
    have hleft := hmin A hA hAsmall
    have hright := hmin (S\A) hrest hrsmall
    have hid := cut_partition_identity G S A hAS
    rw [cutSize_induce]
    change d ≤ 2*(G.interedges A (S\A)).card
    omega
  refine ⟨S,hS,hboundary,?_,hc⟩
  apply connected_of_positive_cuts
  intro T hT hproper
  have hh := hc T hT hproper
  omega

end
end Cycle13
