import Cycle12.Foundations.MatchingControl

/-! Complete a prescribed external matching and suppress a vertex. The
external induced multigraph stays simple and all external/internal edge
multiplicities stay unchanged. The edge routes and exact degrees are retained. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I)

def SimpleOn (X : Set V) : Prop :=
  (∀ x∈X, R.multiplicity x x=0) ∧ ∀ x∈X, ∀ y∈X, R.multiplicity x y≤1

theorem simpleOn_univ_iff : R.SimpleOn Set.univ ↔ R.IsSimple := by
  simp only [SimpleOn,Set.mem_univ,forall_const]
  exact R.isSimple_iff_multiplicity.symm

variable (z : V) (X : Set {v : V // v≠z})
    {H : SimpleGraph (R.Ports z)} (M : H.Subgraph)

theorem external_output_cross_zero
    (hends : ∀ a b, M.Adj a b → R.portTip z a∈X ∧ R.portTip z b∈X)
    {x y : {v : V // v≠z}} (hy : y∉X) :
    MatchingCounts.outputCount M (R.portTip z) x y=0 := by
  apply MatchingCounts.outputCount_eq_zero
  intro a b hab he
  rcases Sym2.eq_iff.mp he with h | h
  · exact hy (h.2 ▸ (hends a b hab).2)
  · exact hy (h.1 ▸ (hends a b hab).1)

theorem external_output_loop_zero
    (hnoloop : ∀ a b, M.Adj a b → R.portTip z a≠R.portTip z b)
    (x : {v : V // v≠z}) : MatchingCounts.outputCount M (R.portTip z) x x=0 := by
  apply MatchingCounts.outputCount_eq_zero
  intro a b hab he
  rcases Sym2.eq_iff.mp he with h | h <;>
    exact hnoloop a b hab (h.1.trans h.2.symm)

theorem old_multiplicity_zero_of_output
    (habsent : ∀ a b, M.Adj a b →
      R.multiplicity (R.portTip z a).val (R.portTip z b).val=0)
    {x y : {v : V // v≠z}}
    (hpos : 0<MatchingCounts.outputCount M (R.portTip z) x y) :
    R.multiplicity x.val y.val=0 := by
  obtain ⟨e,he⟩ := card_pos.mp hpos
  have hp := (mem_filter.mp he).2
  have ha : M.Adj e.val.out.1 e.val.out.2 := edge_out_adj M.spanningCoe e
  have ho : s(R.portTip z e.val.out.1,R.portTip z e.val.out.2)=s(x,y) :=
    (congrArg (Sym2.map (R.portTip z)) (out_pair_eq e.val)).trans hp
  have hv : s((R.portTip z e.val.out.1).val,(R.portTip z e.val.out.2).val)=s(x.val,y.val) :=
    congrArg (Sym2.map Subtype.val) ho
  have hh := habsent _ _ ha
  unfold multiplicity at hh ⊢
  rwa [hv] at hh

theorem prescribed_output_simple
    (hi : Set.InjOn (Sym2.map (R.portTip z)) M.edgeSet)
    (habsent : ∀ a b, M.Adj a b →
      R.multiplicity (R.portTip z a).val (R.portTip z b).val=0)
    (x y : {v : V // v≠z}) (hold : R.multiplicity x.val y.val≤1) :
    R.multiplicity x.val y.val+MatchingCounts.outputCount M (R.portTip z) x y≤1 := by
  by_cases hz : MatchingCounts.outputCount M (R.portTip z) x y=0
  · simpa only [hz,Nat.add_zero] using hold
  · have hzero := R.old_multiplicity_zero_of_output z M habsent (Nat.pos_of_ne_zero hz)
    rw [hzero,Nat.zero_add]
    exact MatchingCounts.outputCount_le_one M (R.portTip z) hi x y

theorem suppress_simpleOn_of_prescribed {N : H.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (hle : M≤N)
    (hcover : ∀ a, R.portTip z a∈X → a∈M.verts)
    (hold : R.SimpleOn (Subtype.val '' X))
    (hnoloop : ∀ a b, M.Adj a b → R.portTip z a≠R.portTip z b)
    (hi : Set.InjOn (Sym2.map (R.portTip z)) M.edgeSet)
    (habsent : ∀ a b, M.Adj a b →
      R.multiplicity (R.portTip z a).val (R.portTip z b).val=0) :
    (R.suppress z N hN).SimpleOn X := by
  have hc : ∀ x∈X, ∀ a, R.portTip z a=x → a∈M.verts := by
    intro x hx a ha
    exact hcover a (ha ▸ hx)
  constructor
  · intro x hx
    rw [R.suppress_extension_multiplicity z hM hN hle x x (hc x hx),
      R.external_output_loop_zero z M hnoloop x, Nat.add_zero]
    exact hold.1 x.val ⟨x,hx,rfl⟩
  · intro x hx y hy
    rw [R.suppress_extension_multiplicity z hM hN hle x y (hc x hx)]
    exact R.prescribed_output_simple z M hi habsent x y (hold.2 _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩)

theorem suppress_cross_unchanged {N : H.Subgraph}
    (hM : M.IsMatching) (hN : N.IsMatching) (hle : M≤N)
    (hcover : ∀ a, R.portTip z a∈X → a∈M.verts)
    (hends : ∀ a b, M.Adj a b → R.portTip z a∈X ∧ R.portTip z b∈X)
    (x y : {v : V // v≠z}) (hx : x∈X) (hy : y∉X) :
    (R.suppress z N hN).multiplicity x y=R.multiplicity x.val y.val := by
  rw [R.suppress_extension_multiplicity z hM hN hle x y
    (fun a ha => hcover a (ha ▸ hx)),R.external_output_cross_zero z X M hends hy,Nat.add_zero]

theorem exists_controlled_suppression
    (M : (⊤ : SimpleGraph (R.Ports z)).Subgraph) (hM : M.IsMatching)
    (heven : Even (R.degree z))
    (hcover : ∀ a, R.portTip z a∈X → a∈M.verts)
    (hends : ∀ a b, M.Adj a b → R.portTip z a∈X ∧ R.portTip z b∈X)
    (hold : R.SimpleOn (Subtype.val '' X))
    (hnoloop : ∀ a b, M.Adj a b → R.portTip z a≠R.portTip z b)
    (hi : Set.InjOn (Sym2.map (R.portTip z)) M.edgeSet)
    (habsent : ∀ a b, M.Adj a b →
      R.multiplicity (R.portTip z a).val (R.portTip z b).val=0) :
    ∃ N : (⊤ : SimpleGraph (R.Ports z)).Subgraph, ∃ hN : N.IsMatching,
      N.verts=Set.univ ∧ M≤N ∧
      (R.suppress z N hN).SimpleOn X ∧
      (∀ x y, x∈X → y∉X → (R.suppress z N hN).multiplicity x y=R.multiplicity x.val y.val) ∧
      (∀ v, (R.suppress z N hN).degree v=R.degree v.val) := by
  obtain ⟨N,hN,hNv,hMN,_,hdeg⟩ := R.exists_suppressed_prescribed z M hM heven
  exact ⟨N,hN,hNv,hMN,R.suppress_simpleOn_of_prescribed z X M hM hN hMN
    hcover hold hnoloop hi habsent,
    R.suppress_cross_unchanged z X M hM hN hMN hcover hends,hdeg⟩

end RoutedEdges
end
end Cycle13
