import Cycle12.FirstPassLedger12
import Cycle12.SecondPassReservoirPacking12
import Cycle12.PackingCompletionLedger12
import Cycle12.ParityReserveSlots12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

set_option maxHeartbeats 8000000

/-- Actual two-pass completion for an arbitrary graph. A parity-dependent
reserve leaves one singleton incident edge precisely at each odd outside
vertex, with no extra cycle charge and the same reservoir capacity. -/
theorem parity_three_reservoir_completion [Nonempty V]
    (G H₁ H₂ : SimpleGraph V) (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G)
    (hdis : Disjoint H₁.edgeSet H₂.edgeSet)
    (A B C : Finset V) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {z a b c : ℝ} (hA : ReservoirSample H₁ A z a) (hB : ReservoirSample H₁ B z b)
    (hC : ReservoirSample H₂ C z c)
    (hz : 8192 ≤ z) (hzr : z ≤ (Fintype.card V:ℝ))
    (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) :
    ∃ T : CyclePacking G, T.count ≤ Fintype.card V ∧
      ∀ v, v∉A∪B∪C → T.residue.degree v=if Even (G.degree v) then 0 else 1 := by
  let D := A ∪ B
  let U := D ∪ C
  let O := Uᶜ
  have hDC : Disjoint D C := Finset.disjoint_union_left.mpr ⟨hAC,hBC⟩
  have hDO : Disjoint D O := by
    apply Finset.disjoint_left.mpr
    intro v hv ho
    exact (mem_compl.mp ho) (mem_union_left _ hv)
  have hOC : Disjoint O C := by
    apply Finset.disjoint_left.mpr
    intro v ho hc
    exact (mem_compl.mp ho) (mem_union_right _ hc)
  let DD := parityDoubleRoots G D O
  let OO := paritySingleRoots G O
  let root := reserveRoot DD OO
  obtain ⟨hDDC,hOOC⟩ := parity_reserve_roots_outside G D O C hDC hOC
  have hrootout : ∀ j, root j ∉ C := reserveRoot_outside DD OO C hDDC hOOC
  obtain ⟨hslotcard,hslotload⟩ := reserveSlots_bounds DD OO (parity_reserve_roots_disjoint G D O hDO)
  obtain ⟨tip,htip,htipinj,htipload⟩ := choose_reserved_spokes H₂ C root hC hrootout hslotload
    hslotcard hz hzr hsquare
  let R := bankReserve H₂ C root tip
  have hRH₂ : R ≤ H₂ := bankReserve_le H₂ C root tip (fun j => (htip j).2)
  have hRG : R ≤ G := hRH₂.trans h₂
  have hspoke : ∀ j, R.Adj (root j) (tip j) := by
    intro j
    exact Or.inl (spokeGraph_root_adj root tip j (h₂ (htip j).2).ne)
  have hinside : ∀ x ∈ C, ∀ y ∈ C, H₂.Adj x y → R.Adj x y :=
    fun x hx y hy h => Or.inr ⟨h,hx,hy⟩
  have hRdegree : ∀ v, v ∉ U → R.degree v = if Even (G.degree v) then 1 else 2 := by
    intro v hv
    have hvC : v ∉ C := fun hc => hv (mem_union_right _ hc)
    have hvD : v ∉ D := fun hd => hv (mem_union_left _ hd)
    have hvO : v ∈ O := mem_compl.mpr hv
    have hh := bankReserve_degree_outside H₂ C root tip hrootout (fun j => (htip j).1) htipinj v hvC
    rw [show Fintype.card {j // root j=v}=if Even (G.degree v) then 1 else 2 from
      parity_reserve_fiber G D O v hvD hvO] at hh
    exact hh
  let J := firstExterior G R D U
  let f := firstExteriorHom G R D U
  have hfinj : Function.Injective f := Subtype.val_injective
  have hfar : ∀ w : (Dᶜ : Set V), f w ∉ A ∧ f w ∉ B := by
    intro w
    have hw : w.val ∉ D := w.property
    exact ⟨fun ha => hw (mem_union_left _ ha),fun hb => hw (mem_union_right _ hb)⟩
  obtain ⟨P,hPcount,hPcover,hPused⟩ := first_pass_reservoir_packing J G H₁ h₁ f hfinj
    A B hAB hfar hA hB hz hzr hlog hsquare
  have hRJ : Disjoint R.edgeSet (Sym2.map f '' J.edgeSet) := by
    apply Set.disjoint_left.mpr
    rintro e he ⟨d,hd,hde⟩
    induction d using Sym2.inductionOn with
    | _ x y =>
      change s(x.val,y.val) = e at hde
      have hh := (deleteEdges_adj.mp hd).2
      have heR : s(x.val,y.val) ∈ R.edgeSet := hde.symm ▸ he
      exact hh (Or.inl heR)
  have hRH₁ : Disjoint R.edgeSet H₁.edgeSet := hdis.symm.mono_left (edgeSet_mono hRH₂)
  have hRP : R ≤ P.residue := packing_preserves_reserve P _ hRG hPused hRJ hRH₁
  let K := P.residue.deleteEdges (R.edgeSet ∪ (insideGraph G U).edgeSet)
  have hKP : K ≤ P.residue := P.residue.deleteEdges_le _
  have hKG : K ≤ G := hKP.trans P.residue_le
  have hbip : ∀ x y, K.Adj x y → (x ∈ D ∧ y ∉ U) ∨ (y ∈ D ∧ x ∉ U) := by
    intro x y hxy
    exact first_pass_bipartite D U (fun v hv => mem_union_left _ hv) P hPcover hxy
  have hKC : ∀ x y, K.Adj x y → x ∉ C ∧ y ∉ C := by
    intro x y hxy
    rcases hbip x y hxy with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact ⟨fun hc => Finset.disjoint_left.mp hDC hx hc,fun hc => hy (mem_union_right _ hc)⟩
    · exact ⟨fun hc => hx (mem_union_right _ hc),fun hc => Finset.disjoint_left.mp hDC hy hc⟩
  let W := (Cᶜ : Set V)
  let J₂ := K.induce W
  let f₂ : J₂ →g G := {toFun := Subtype.val,map_rel' := fun h => hKG h}
  let A₂ : Finset W := univ.filter (fun w => w.val ∈ D)
  have hA₂ : A₂.card = D.card := by
    have hi : A₂.image Subtype.val = D := by
      ext v
      simp only [mem_image,A₂,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨w,hw,rfl⟩; exact hw
      · intro hv
        have hvC : v ∉ C := fun hc => Finset.disjoint_left.mp hDC hv hc
        exact ⟨⟨v,hvC⟩,hv,rfl⟩
    rw [←hi,card_image_of_injective _ Subtype.val_injective]
  have hdeg : ∀ w : W, J₂.degree w = K.degree w.val := by
    intro w
    exact degree_induce_of_neighborSet_subset (fun y hy => (hKC w y hy).2)
  have hodd : ∀ w : W, w ∉ A₂ → 0 < J₂.degree w → Odd (J₂.degree w) := by
    intro w hw _
    have hwD : w.val ∉ D := by simpa only [A₂,mem_filter,mem_univ,true_and] using hw
    have hwC : w.val ∉ C := w.property
    have hwU : w.val ∉ U := fun h => (mem_union.mp h).elim hwD hwC
    have hh := parity_first_pass_outside_odd U P hRP w.val hwU (hRdegree w.val hwU)
    simpa only [hdeg] using hh
  have hslots : ∀ w : W, (if w ∈ A₂ then 2 else 1) ≤ Fintype.card {t // root t = f₂ w} := by
    intro w
    change (if w∈A₂ then 2 else 1)≤Fintype.card {t // reserveRoot DD OO t=w.val}
    have hv : w.val∈D ∨ w.val∈O := by
      by_cases hvD : w.val∈D
      · exact Or.inl hvD
      · exact Or.inr (mem_compl.mpr (fun h => (mem_union.mp h).elim hvD w.property))
    simpa only [A₂,mem_filter,mem_univ,true_and] using parity_reserve_slots_at_least G D O w.val hv
  obtain ⟨Q,hQcount,hQcover,hQused⟩ := second_pass_reservoir_packing J₂ G H₂ R h₂ f₂
    Subtype.val_injective A₂ (by
      intro w hw hpos
      have hh := hodd w hw
      simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hh hpos ⊢
      exact hh hpos) C (fun w => w.property) hC root tip htip hspoke
    htipinj hinside htipload (by
      intro w
      by_cases hw : w ∈ A₂
      · simpa only [if_pos hw] using hslots w
      · simpa only [if_neg hw] using hslots w) hz hlog hsquare
  have hKimage : Sym2.map f₂ '' J₂.edgeSet = K.edgeSet := by
    ext e
    constructor
    · rintro ⟨d,hd,hde⟩
      induction d using Sym2.inductionOn with
      | _ x y =>
        change s(x.val,y.val) = e at hde
        exact hde ▸ (show s(x.val,y.val) ∈ K.edgeSet from hd)
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hh := hKC x y he
        exact ⟨s((⟨x,hh.1⟩ : W),(⟨y,hh.2⟩ : W)),he,rfl⟩
  rw [hKimage] at hQcover hQused
  have hQP : Q.used ⊆ P.residue.edgeSet := hQused.trans (Set.union_subset (edgeSet_mono hKP) (edgeSet_mono hRP))
  obtain ⟨T,hTcount,hTused⟩ := combine_residual_packings P Q hQP
  have hTsmall : T.count ≤ Fintype.card V := by
    have hDcard : D.card + Dᶜ.card = Fintype.card V := by rw [card_add_card_compl]
    have hCcard : C.card + Cᶜ.card = Fintype.card V := by rw [card_add_card_compl]
    have hCpos : 0 < C.card := card_pos.mpr (hC.nonempty (by linarith only [hz]))
    have hcompl : ∀ E : Finset V, Fintype.card (Eᶜ : Set V) = Eᶜ.card := by
      intro E
      rw [Fintype.card_subtype]
      congr 1
      ext v
      simp
    have hp : 2*P.count ≤ Dᶜ.card+1 := by rw [hcompl] at hPcount; exact hPcount
    have hq : 2*Q.count ≤ Cᶜ.card+D.card := by simpa only [W,hcompl,hA₂] using hQcount
    omega
  refine ⟨T,hTsmall,?_⟩
  have hs := two_pass_residue_edges U P Q T hTused hQcover
  exact parity_graph_outside_degree G T.residue R U hs hRdegree (packing_residue_parity T)


end
end Cycle12
