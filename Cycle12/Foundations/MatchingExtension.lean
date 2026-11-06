import Cycle12.Foundations.SuppressionRoutes

/-! Complete an already prescribed port matching. New pairs use only
uncovered ports, so previously selected external pairs remain untouched. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [DecidableEq I]

theorem matching_extends_to_perfect (M : (⊤ : SimpleGraph I).Subgraph)
    (hM : M.IsMatching) (heven : Even (Fintype.card I)) :
    ∃ N : (⊤ : SimpleGraph I).Subgraph,
      N.IsMatching ∧ N.verts=Set.univ ∧ M≤N ∧
      (∀ x y, N.Adj x y → ¬M.Adj x y → x∉M.verts ∧ y∉M.verts) := by
  have hcard : Even M.verts.ncard := by
    simpa only [Set.ncard_eq_toFinset_card'] using hM.even_card
  have hcompl : Even M.vertsᶜ.ncard :=
    (Set.even_ncard_compl_iff (by simpa only [Nat.card_eq_fintype_card] using heven) _).mpr hcard
  have hc : (⊤ : SimpleGraph I).IsClique M.vertsᶜ := by intro x _ y _ hxy; exact hxy
  obtain ⟨P,hPverts,hP⟩ := (hc.even_iff_exists_isMatching (Set.toFinite _)).mp hcompl
  have hd : Disjoint M.support P.support := by
    rw [hM.support_eq_verts,hP.support_eq_verts,hPverts]
    exact disjoint_compl_right
  refine ⟨M⊔P,hM.sup hP hd,?_,le_sup_left,?_⟩
  · change M.verts ∪ P.verts=Set.univ
    rw [hPverts,Set.union_compl_self]
  · intro x y hN hnot
    have hp : P.Adj x y := hN.resolve_left hnot
    exact ⟨by simpa only [hPverts,Set.mem_compl_iff] using hp.fst_mem,
      by simpa only [hPverts,Set.mem_compl_iff] using hp.snd_mem⟩

theorem matching_add_pair (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    {x y : I} (hxy : x≠y) (hx : x∉M.verts) (hy : y∉M.verts) :
    ∃ N : (⊤ : SimpleGraph I).Subgraph, N.IsMatching ∧
      N.verts=M.verts ∪ {x,y} ∧ M≤N ∧ N.Adj x y ∧
      (∀ a b, N.Adj a b → M.Adj a b ∨ s(a,b)=s(x,y)) := by
  let P := (⊤ : SimpleGraph I).subgraphOfAdj (show (⊤ : SimpleGraph I).Adj x y from hxy)
  have hP : P.IsMatching := Subgraph.IsMatching.subgraphOfAdj _
  have hd : Disjoint M.support P.support := by
    rw [hM.support_eq_verts,hP.support_eq_verts]
    change Disjoint M.verts {x,y}
    apply Set.disjoint_left.mpr
    intro a ha hp
    rcases hp with rfl | rfl
    · exact hx ha
    · exact hy ha
  refine ⟨M⊔P,hM.sup hP hd,rfl,le_sup_left,Or.inr (by rfl),?_⟩
  intro a b hab
  rcases hab with h | h
  · exact Or.inl h
  · change s(x,y)=s(a,b) at h
    exact Or.inr h.symm

theorem matching_extends_with_pair (M : (⊤ : SimpleGraph I).Subgraph)
    (hM : M.IsMatching) (heven : Even (Fintype.card I))
    {x y : I} (hxy : x≠y) (hx : x∉M.verts) (hy : y∉M.verts) :
    ∃ N : (⊤ : SimpleGraph I).Subgraph,
      N.IsMatching ∧ N.verts=Set.univ ∧ M≤N ∧ N.Adj x y ∧
      (∀ a b, N.Adj a b → ¬M.Adj a b → s(a,b)≠s(x,y) →
        a∉M.verts ∪ {x,y} ∧ b∉M.verts ∪ {x,y}) := by
  obtain ⟨P,hP,hPv,hMP,hPxy,hPnew⟩ := matching_add_pair M hM hxy hx hy
  obtain ⟨N,hN,hNv,hPN,hNnew⟩ := matching_extends_to_perfect P hP heven
  refine ⟨N,hN,hNv,hMP.trans hPN,hPN.2 hPxy,?_⟩
  intro a b hab hMab hpair
  have hPab : ¬P.Adj a b := fun h => (hPnew a b h).elim hMab hpair
  simpa only [hPv] using hNnew a b hab hPab

end
end Cycle13
