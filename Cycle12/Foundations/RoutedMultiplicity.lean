import Cycle12.Foundations.SuppressionGraph

/-! Exact multiplicities for actual routed multigraphs and vertex suppression. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I J V W : Type} [Fintype I] [Fintype J] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W}

def multiplicity (R : RoutedEdges G φ I) (x y : V) : ℕ :=
  (univ.filter (fun i => R.edge i=s(x,y))).card

theorem multiplicity_eq_sum (R : RoutedEdges G φ I) (x y : V) :
    R.multiplicity x y=∑ i, if R.edge i=s(x,y) then (1:ℕ) else 0 := by
  simp [multiplicity]

theorem multiplicity_symm (R : RoutedEdges G φ I) (x y : V) :
    R.multiplicity x y=R.multiplicity y x := by
  unfold multiplicity
  rw [Sym2.eq_swap]

theorem multiplicity_pos_iff (R : RoutedEdges G φ I) (x y : V) :
    0<R.multiplicity x y ↔ ∃ i, R.edge i=s(x,y) := by
  simp [multiplicity,Finset.card_pos,Finset.nonempty_def]

theorem multiplicity_eq_zero_iff (R : RoutedEdges G φ I) (x y : V) :
    R.multiplicity x y=0 ↔ ∀ i, R.edge i≠s(x,y) := by
  constructor
  · intro hz i hi
    have hp := (R.multiplicity_pos_iff x y).mpr ⟨i,hi⟩
    omega
  · intro h
    by_contra hn
    obtain ⟨i,hi⟩ := (R.multiplicity_pos_iff x y).mp (Nat.pos_of_ne_zero hn)
    exact h i hi

theorem graph_adj_iff_multiplicity (R : RoutedEdges G φ I) (x y : V) :
    R.graph.Adj x y ↔ x≠y ∧ 0<R.multiplicity x y := by
  rw [multiplicity_pos_iff]
  rfl

theorem multiplicity_le_one_iff (R : RoutedEdges G φ I) (x y : V) :
    R.multiplicity x y≤1 ↔ ∀ i j, R.edge i=s(x,y) → R.edge j=s(x,y) → i=j := by
  simp only [multiplicity,card_le_one,mem_filter,mem_univ,true_and]
  constructor
  · intro h i j hi hj; exact h i hi j hj
  · intro h i hi j hj; exact h i j hi hj

theorem isSimple_iff_multiplicity (R : RoutedEdges G φ I) :
    R.IsSimple ↔ (∀ x, R.multiplicity x x=0) ∧ ∀ x y, R.multiplicity x y≤1 := by
  constructor
  · rintro ⟨hl,hi⟩
    constructor
    · intro x
      apply (R.multiplicity_eq_zero_iff x x).mpr
      intro i he
      rcases Sym2.eq_iff.mp he with h | h <;>
        exact hl i (h.1.trans h.2.symm)
    · intro x y
      exact (R.multiplicity_le_one_iff x y).mpr (fun i j hi' hj' => hi (hi'.trans hj'.symm))
  · rintro ⟨hl,hi⟩
    constructor
    · intro i he
      exact (R.multiplicity_eq_zero_iff _ _).mp (hl (R.left i)) i
        (by change s(R.left i,R.right i)=_; rw [he])
    · intro i j he
      exact (R.multiplicity_le_one_iff _ _).mp (hi (R.left i) (R.right i)) i j rfl he.symm

theorem multiplicity_append (R : RoutedEdges G φ I) (S : RoutedEdges G φ J)
    (hd : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) (x y : V) :
    (R.append S hd).multiplicity x y=R.multiplicity x y+S.multiplicity x y := by
  simp only [multiplicity_eq_sum,Fintype.sum_sum_type,append,edge,Sum.elim_inl,Sum.elim_inr]
  rfl

variable [DecidableEq I] (R : RoutedEdges G φ I) (z : V)

theorem multiplicity_kept (x y : {v : V // v≠z}) :
    (R.keptRoutes z).multiplicity x y=R.multiplicity x.val y.val := by
  rw [multiplicity,multiplicity,← Fintype.card_subtype,← Fintype.card_subtype]
  apply Fintype.card_congr
  refine {
    toFun := fun i => ⟨i.val.val,?_⟩
    invFun := fun i => ⟨⟨i.val,?_⟩,?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  · exact congrArg (Sym2.map Subtype.val) i.property
  · change R.left i.val≠z ∧ R.right i.val≠z
    have hi : s(R.left i.val,R.right i.val)=s(x.val,y.val) := i.property
    rcases Sym2.eq_iff.mp hi with h | h
    · exact ⟨fun he => x.property (h.1.symm.trans he),fun he => y.property (h.2.symm.trans he)⟩
    · exact ⟨fun he => y.property (h.1.symm.trans he),fun he => x.property (h.2.symm.trans he)⟩
  · apply Sym2.eq_iff.mpr
    rcases Sym2.eq_iff.mp i.property with h | h
    · exact Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩
    · exact Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩

theorem multiplicity_suppress {H : SimpleGraph (R.Ports z)}
    (M : H.Subgraph) (hM : M.IsMatching) (x y : {v : V // v≠z}) :
    (R.suppress z M hM).multiplicity x y=
      R.multiplicity x.val y.val+(R.pairedRoutes z M hM).multiplicity x y := by
  rw [suppress,multiplicity_append,multiplicity_kept]

end RoutedEdges
end
end Cycle13
