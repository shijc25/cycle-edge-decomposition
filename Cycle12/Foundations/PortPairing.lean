import Cycle12.Foundations.CloneMatching

/-! Lifting a port matching to actual paths in the host graph. Ports may
share their retained endpoint, but their host edges are pairwise disjoint. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

lemma matching_pair_separation {I : Type} {H : SimpleGraph I} (M : H.Subgraph)
    (hM : M.IsMatching) {x y a b : I} (hxy : M.Adj x y) (hab : M.Adj a b)
    (hne : s(x,y) ≠ s(a,b)) : x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    subst a
    have hyb := hM.eq_of_adj_left hxy hab
    exact hne (by rw [hyb])
  · intro h
    subst b
    have hya := hM.eq_of_adj_left hxy hab.symm
    exact hne (by rw [hya,Sym2.eq_swap])
  · intro h
    subst a
    have hxb := hM.eq_of_adj_left hxy.symm hab
    exact hne (by rw [hxb,Sym2.eq_swap])
  · intro h
    subst b
    have hxa := hM.eq_of_adj_right hxy hab
    exact hne (by rw [hxa])

namespace PortPairing
variable {I V W : Type} {H : SimpleGraph I} (M : H.Subgraph) (o : I → V)
    {G : SimpleGraph W} (φ : V ↪ W) (z : W) (P : ∀ i : I, G.Walk z (φ (o i)))

def output : SimpleGraph V := M.spanningCoe.map o

def first {v w : V} (h : (output M o).Adj v w) : I := h.2.choose
def second {v w : V} (h : (output M o).Adj v w) : I := h.2.choose_spec.choose
lemma pair_spec {v w : V} (h : (output M o).Adj v w) :
    M.Adj (first M o h) (second M o h) ∧ o (first M o h)=v ∧ o (second M o h)=w :=
  h.2.choose_spec.choose_spec

def pairedWalk {v w : V} (h : (output M o).Adj v w) : G.Walk (φ v) (φ w) :=
  ((P (first M o h)).reverse.append (P (second M o h))).copy
    (congrArg φ (pair_spec M o h).2.1) (congrArg φ (pair_spec M o h).2.2)

lemma pairedWalk_edgeSet {v w : V} (h : (output M o).Adj v w) :
    (pairedWalk M o φ z P h).edgeSet=
      (P (first M o h)).edgeSet ∪ (P (second M o h)).edgeSet := by
  simp only [pairedWalk,Walk.edgeSet_copy,Walk.edgeSet_append,Walk.edgeSet_reverse]

theorem pairedWalk_disjoint (hM : M.IsMatching)
    (hP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet))
    {v w a b : V} (h : (output M o).Adj v w) (k : (output M o).Adj a b)
    (hne : s(v,w) ≠ s(a,b)) :
    Disjoint (pairedWalk M o φ z P h).edgeSet (pairedWalk M o φ z P k).edgeSet := by
  have h₁ := pair_spec M o h
  have h₂ := pair_spec M o k
  have hedge : s(first M o h,second M o h) ≠ s(first M o k,second M o k) := by
    intro he
    apply hne
    have hm := congrArg (Sym2.map o) he
    simpa only [Sym2.map_mk,h₁.2.1,h₁.2.2,h₂.2.1,h₂.2.2] using hm
  have hsep := matching_pair_separation M hM h₁.1 h₂.1 hedge
  rw [pairedWalk_edgeSet,pairedWalk_edgeSet]
  exact (hP hsep.1).union_right (hP hsep.2.1) |>.union_left
    ((hP hsep.2.2.1).union_right (hP hsep.2.2.2))

theorem pairedWalk_avoids
    (havoid : ∀ i v, φ v ∈ (P i).support → v=o i)
    {v w : V} (h : (output M o).Adj v w) (a : V)
    (ha : φ a ∈ (pairedWalk M o φ z P h).support) : a=v ∨ a=w := by
  simp only [pairedWalk,Walk.support_copy,Walk.mem_support_append_iff,
    Walk.support_reverse,List.mem_reverse] at ha
  have h₁ := pair_spec M o h
  rcases ha with ha | ha
  · exact Or.inl ((havoid _ a ha).trans h₁.2.1)
  · exact Or.inr ((havoid _ a ha).trans h₁.2.2)

def routing (hM : M.IsMatching)
    (hP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet))
    (havoid : ∀ i v, φ v ∈ (P i).support → v=o i) : EdgeRouting (output M o) G where
  vertex := φ
  route := pairedWalk M o φ z P
  disjoint := pairedWalk_disjoint M o φ z P hM hP
  avoids := pairedWalk_avoids M o φ z P havoid

end PortPairing
end
end Cycle13
