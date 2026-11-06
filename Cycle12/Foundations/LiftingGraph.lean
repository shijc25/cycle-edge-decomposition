import Cycle12.Foundations.EquitableColoring
import Cycle12.Foundations.IndexedFactorization

/-! The auxiliary simple graph for a lifting coloring: original vertices
and indexed edges, with every incidence star a clique. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def liftingStar (a b : I → V) (v : V) : Set (V⊕I)
  | .inl w => w=v
  | .inr i => a i=v ∨ b i=v

def liftingGraph (a b : I → V) : SimpleGraph (V⊕I) where
  Adj x y := x≠y ∧ ∃ v, x∈liftingStar a b v ∧ y∈liftingStar a b v
  symm := ⟨by rintro x y ⟨hne,v,hx,hy⟩; exact ⟨hne.symm,v,hy,hx⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

theorem liftingStar_isClique (a b : I → V) (v : V) :
    (liftingGraph a b).IsClique (liftingStar a b v) := by
  intro x hx y hy hne
  exact ⟨hne,v,hx,hy⟩

lemma twoColor_neighbors_same_color {W C : Type} [Fintype W] [DecidableEq W]
    [DecidableEq C] (H : SimpleGraph W) (f : W → C) (a b : C) (hab : a≠b)
    {x y z : W} (hy : (twoColorGraph H f a b).Adj x y)
    (hz : (twoColorGraph H f a b).Adj x z) : f y=f z := by
  rcases hy.2 with hy | hy <;> rcases hz.2 with hz | hz
  · exact hy.2.trans hz.2.symm
  · exact (hab (hy.1.symm.trans hz.1)).elim
  · exact (hab (hz.1.symm.trans hy.1)).elim
  · exact hy.2.trans hz.2.symm

theorem clique_twoColor_neighbors_le_one {W C : Type} [Fintype W] [DecidableEq W]
    [DecidableEq C] (H : SimpleGraph W) (f : H.Coloring C) (a b : C) (hab : a≠b)
    (S : Set W) (hS : H.IsClique S) (x : W) :
    (((twoColorGraph H f a b).neighborFinset x).filter (fun y => y∈S)).card ≤ 1 := by
  apply card_le_one.mpr
  intro y hy z hz
  by_contra hne
  have hya := (mem_filter.mp hy)
  have hza := (mem_filter.mp hz)
  exact f.valid (hS hya.2 hza.2 hne) (twoColor_neighbors_same_color H f a b hab
    ((twoColorGraph H f a b).mem_neighborFinset x y |>.mp hya.1)
    ((twoColorGraph H f a b).mem_neighborFinset x z |>.mp hza.1))

theorem lifting_twoColor_original_degree {C : Type} [DecidableEq C]
    (a b : I → V) (f : (liftingGraph a b).Coloring C) (r s : C) (hrs : r≠s) (v : V) :
    (twoColorGraph (liftingGraph a b) f r s).degree (.inl v) ≤ 1 := by
  let H := twoColorGraph (liftingGraph a b) f r s
  have he : (H.neighborFinset (.inl v)).filter (fun y => y∈liftingStar a b v)=
      H.neighborFinset (.inl v) := by
    apply filter_eq_self.mpr
    intro y hy
    have hh := (H.mem_neighborFinset (.inl v) y).mp hy
    obtain ⟨hne,w,hv,hw⟩ := hh.1
    change v=w at hv
    subst w
    exact hw
  have h := clique_twoColor_neighbors_le_one (liftingGraph a b) f r s hrs
    (liftingStar a b v) (liftingStar_isClique a b v) (.inl v)
  change ((H.neighborFinset (.inl v)).filter (fun y => y∈liftingStar a b v)).card ≤ 1 at h
  rw [he,card_neighborFinset_eq_degree] at h
  exact h

theorem lifting_twoColor_degree {C : Type} [DecidableEq C]
    (a b : I → V) (f : (liftingGraph a b).Coloring C) (r s : C) (hrs : r≠s)
    (x : V⊕I) : (twoColorGraph (liftingGraph a b) f r s).degree x ≤ 2 := by
  cases x with
  | inl v => exact (lifting_twoColor_original_degree a b f r s hrs v).trans (by decide)
  | inr i =>
    let H := twoColorGraph (liftingGraph a b) f r s
    let A := (H.neighborFinset (.inr i)).filter (fun y => y∈liftingStar a b (a i))
    let B := (H.neighborFinset (.inr i)).filter (fun y => y∈liftingStar a b (b i))
    have hsub : H.neighborFinset (.inr i) ⊆ A∪B := by
      intro y hy
      have hh := (H.mem_neighborFinset (.inr i) y).mp hy
      obtain ⟨hne,v,hi,hv⟩ := hh.1
      rcases hi with ha | hb
      · exact mem_union_left B (mem_filter.mpr ⟨hy,ha ▸ hv⟩)
      · exact mem_union_right A (mem_filter.mpr ⟨hy,hb ▸ hv⟩)
    have hA := clique_twoColor_neighbors_le_one (liftingGraph a b) f r s hrs
      (liftingStar a b (a i)) (liftingStar_isClique a b (a i)) (.inr i)
    have hB := clique_twoColor_neighbors_le_one (liftingGraph a b) f r s hrs
      (liftingStar a b (b i)) (liftingStar_isClique a b (b i)) (.inr i)
    have hc := (card_le_card hsub).trans (card_union_le A B)
    change A.card ≤ 1 at hA
    change B.card ≤ 1 at hB
    rw [card_neighborFinset_eq_degree] at hc
    simp only [← ncard_neighborSet,H] at hc ⊢
    omega

theorem connected_marked_le_two {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hc : H.Connected) (M : Finset W)
    (hd : ∀ v, H.degree v ≤ 2) (hm : ∀ v∈M, H.degree v ≤ 1) : M.card ≤ 2 := by
  have hsum : (∑ v, H.degree v)+M.card ≤ 2*Fintype.card W := by
    have hp : ∀ v : W, H.degree v+(if v∈M then 1 else 0) ≤ 2 := by
      intro v
      by_cases hv : v∈M
      · have hh := hm v hv; simp only [if_pos hv]; omega
      · simpa only [if_neg hv,add_zero] using hd v
    have hh := sum_le_sum (fun v (_ : v∈(univ : Finset W)) => hp v)
    simpa only [sum_add_distrib,sum_boole,filter_mem_eq_inter,univ_inter,Nat.cast_id,
      sum_const,card_univ,nsmul_eq_mul,Nat.mul_comm] using hh
  have hv := hc.card_vert_le_card_edgeSet_add_one
  rw [H.sum_degrees_eq_twice_card_edges] at hsum
  simp only [Nat.card_eq_fintype_card,← edgeFinset_card] at hv
  omega

end
end Cycle13
