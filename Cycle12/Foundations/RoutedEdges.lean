import Cycle12.Foundations.MatchingPorts

/-! Indexed edges routed in a simple host. Different indices remain different
edges even when their endpoints agree; loops count twice toward degree. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure RoutedEdges {V W : Type} (G : SimpleGraph W) (φ : V ↪ W) (I : Type) where
  left : I → V
  right : I → V
  route : ∀ i, G.Walk (φ (left i)) (φ (right i))
  disjoint : Pairwise (fun i j => Disjoint (route i).edgeSet (route j).edgeSet)
  avoids : ∀ i v, φ v ∈ (route i).support → v=left i ∨ v=right i

namespace RoutedEdges
variable {I J V W : Type} {G : SimpleGraph W} {φ : V ↪ W}

def degree [Fintype I] [DecidableEq V] (R : RoutedEdges G φ I) (v : V) : ℕ :=
  ∑ i, ((if R.left i=v then 1 else 0) + (if R.right i=v then 1 else 0))

def restrict (R : RoutedEdges G φ I) (f : J ↪ I) : RoutedEdges G φ J where
  left := R.left ∘ f
  right := R.right ∘ f
  route i := R.route (f i)
  disjoint := by
    intro i j h
    exact R.disjoint (f.injective.ne h)
  avoids i v := R.avoids (f i) v

def append (R : RoutedEdges G φ I) (S : RoutedEdges G φ J)
    (hcross : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) :
    RoutedEdges G φ (I ⊕ J) where
  left := Sum.elim R.left S.left
  right := Sum.elim R.right S.right
  route := fun i => match i with
    | .inl i => R.route i
    | .inr j => S.route j
  disjoint := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · exact R.disjoint (fun he => h (he ▸ rfl))
    · exact hcross a b
    · exact (hcross b a).symm
    · exact S.disjoint (fun he => h (he ▸ rfl))
  avoids := by
    rintro (i | j) v h
    · exact R.avoids i v h
    · exact S.avoids j v h

theorem degree_append [Fintype I] [Fintype J] [DecidableEq V]
    (R : RoutedEdges G φ I) (S : RoutedEdges G φ J)
    (hcross : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) (v : V) :
    (R.append S hcross).degree v=R.degree v+S.degree v := by
  unfold degree
  rw [Fintype.sum_sum_type]
  congr 1

end RoutedEdges

namespace MatchingPortFamily
variable {I V W : Type} {H : SimpleGraph I} (M : H.Subgraph) (o : I → V)
    {G : SimpleGraph W} (φ : V ↪ W) (z : W) (P : ∀ i, G.Walk z (φ (o i)))

def walk (e : M.edgeSet) : G.Walk (φ (o e.val.out.1)) (φ (o e.val.out.2)) :=
  (P e.val.out.1).reverse.append (P e.val.out.2)

theorem walk_disjoint (hM : M.IsMatching)
    (hP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet)) :
    Pairwise (fun e f : M.edgeSet => Disjoint (walk M o φ z P e).edgeSet
      (walk M o φ z P f).edgeSet) := by
  intro e f hne
  have he : M.Adj e.val.out.1 e.val.out.2 := edge_out_adj M.spanningCoe e
  have hf : M.Adj f.val.out.1 f.val.out.2 := edge_out_adj M.spanningCoe f
  have hsep := matching_pair_separation M hM he hf (by
    intro h
    exact hne (Subtype.ext (e.val.out_eq.symm.trans (h.trans f.val.out_eq))))
  simp only [walk,Walk.edgeSet_append,Walk.edgeSet_reverse]
  exact (hP hsep.1).union_right (hP hsep.2.1) |>.union_left
    ((hP hsep.2.2.1).union_right (hP hsep.2.2.2))

theorem walk_avoids (havoid : ∀ i v, φ v ∈ (P i).support → v=o i)
    (e : M.edgeSet) (v : V) (h : φ v ∈ (walk M o φ z P e).support) :
    v=o e.val.out.1 ∨ v=o e.val.out.2 := by
  simp only [walk,Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at h
  exact h.imp (havoid _ v) (havoid _ v)

def routed (hM : M.IsMatching)
    (hP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet))
    (havoid : ∀ i v, φ v ∈ (P i).support → v=o i) : RoutedEdges G φ M.edgeSet where
  left e := o e.val.out.1
  right e := o e.val.out.2
  route := walk M o φ z P
  disjoint := walk_disjoint M o φ z P hM hP
  avoids := walk_avoids M o φ z P havoid

theorem degree_routed [Fintype I] [DecidableEq I] [DecidableEq V]
    (hM : M.IsMatching)
    (hP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet))
    (havoid : ∀ i v, φ v ∈ (P i).support → v=o i) (v : V) :
    (routed M o φ z P hM hP havoid).degree v=
      (univ.filter (fun i : M.verts => o i.val=v)).card :=
  matching_output_incidence M hM o v

end MatchingPortFamily
end
end Cycle13
