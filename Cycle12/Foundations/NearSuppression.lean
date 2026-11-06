import Cycle12.Foundations.ForcedPairCounts
import Cycle12.Foundations.WellSuppression

/-! A near-perfect external matching plus one forced external/internal pair
gives a full suppression. The unique possible new crossing edge is counted
exactly, while the external induced multigraph remains simple. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)

theorem exists_near_controlled_suppression (S : Set {v : V // v≠z})
    (M : (⊤ : SimpleGraph (R.Ports z)).Subgraph) (hM : M.IsMatching)
    (a b : R.Ports z) (ha : R.portTip z a∈S) (hb : R.portTip z b∉S)
    (haun : a∉M.verts)
    (hcover : ∀ i, R.portTip z i∈S → i≠a → i∈M.verts)
    (hends : ∀ i j, M.Adj i j → R.portTip z i∈S ∧ R.portTip z j∈S)
    (hnoloop : ∀ i j, M.Adj i j → R.portTip z i≠R.portTip z j)
    (hi : Set.InjOn (Sym2.map (R.portTip z)) M.edgeSet)
    (habsent : ∀ i j, M.Adj i j →
      R.multiplicity (R.portTip z i).val (R.portTip z j).val=0)
    (heven : Even (R.degree z)) (hold : R.SimpleOn (Subtype.val '' S)) :
    ∃ N : (⊤ : SimpleGraph (R.Ports z)).Subgraph, ∃ hN : N.IsMatching,
      N.verts=Set.univ ∧ N.Adj a b ∧ (R.suppress z N hN).SimpleOn S ∧
      (∀ x y, x∈S → y∉S → (R.suppress z N hN).multiplicity x y=
        R.multiplicity x.val y.val+
          (if s(R.portTip z a,R.portTip z b)=s(x,y) then 1 else 0)) ∧
      (∀ v, (R.suppress z N hN).degree v=R.degree v.val) := by
  have hab : a≠b := fun h => hb (h ▸ ha)
  have hbun : b∉M.verts := by
    intro h
    obtain ⟨c,hbc,_⟩ := hM h
    exact hb (hends b c hbc).1
  obtain ⟨P,hP,hPv,hMP,hPab,hPnew⟩ := matching_add_pair M hM hab haun hbun
  have hc : ∀ i, R.portTip z i∈S → i∈P.verts := by
    intro i hiS
    rw [hPv]
    by_cases he : i=a
    · exact Or.inr (Or.inl he)
    · exact Or.inl (hcover i hiS he)
  obtain ⟨N,hN,hNv,hPN,_,hdeg⟩ := R.exists_suppressed_prescribed z P hP heven
  have hcount : ∀ x∈S, ∀ y, (R.suppress z N hN).multiplicity x y=
      R.multiplicity x.val y.val+MatchingCounts.outputCount P (R.portTip z) x y := by
    intro x hx y
    exact R.suppress_extension_multiplicity z hP hN hPN x y (fun i he => hc i (he ▸ hx))
  have hs : (R.suppress z N hN).SimpleOn S := by
    constructor
    · intro x hx
      rw [hcount x hx x,
        MatchingCounts.added_pair_internal (R.portTip z) S hb hMP hPnew hx hx,
        R.external_output_loop_zero z M hnoloop x,Nat.add_zero]
      exact hold.1 x.val ⟨x,hx,rfl⟩
    · intro x hx y hy
      rw [hcount x hx y,
        MatchingCounts.added_pair_internal (R.portTip z) S hb hMP hPnew hx hy]
      exact R.prescribed_output_simple z M hi habsent x y (hold.2 _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩)
  refine ⟨N,hN,hNv,hPN.2 hPab,hs,?_,hdeg⟩
  intro x y hx hy
  rw [hcount x hx y,MatchingCounts.added_pair_cross (R.portTip z) S hPab hends hPnew x y hy]

theorem near_cross_multiplicity_le_two
    (S : Set {v : V // v≠z}) (a b x y : {v : V // v≠z})
    (ha : a∈S) (hb : b∉S) (hx : x∈S) (hy : y∉S)
    (hold : R.multiplicity x.val y.val≤2)
    (hfresh : ∀ w, w∉S → R.multiplicity a.val w.val≤1) :
    R.multiplicity x.val y.val+(if s(a,b)=s(x,y) then 1 else 0)≤2 := by
  split_ifs with he
  · rcases Sym2.eq_iff.mp he with h | h
    · have hh := hfresh y hy
      rw [h.1] at hh
      omega
    · exact False.elim (hb (h.2 ▸ hx))
  · omega

end RoutedEdges
end
end Cycle13
