import Cycle12.Foundations.GLWStopping

/-! The ordered missing-neighbor hypotheses imply the quantitative clone
obstruction size bound at every nonzero state, with actual graph counts. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

def baseNeighbors {X : Type} [Fintype X] {p : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) : Finset X :=
  univ.filter (fun x => G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inl x))

def baseMissing {X : Type} [Fintype X] {p : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) (i : Fin p) : ℕ :=
  ((baseNeighbors G hp).filter (fun x => ¬G.Adj (Sum.inr i) (Sum.inl x))).card

theorem baseMissing_root {X : Type} [Fintype X] {p : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) : baseMissing G hp ⟨0,hp⟩=0 := by
  simp [baseMissing,baseNeighbors,filter_filter]

theorem root_degree_balance {X : Type} [Fintype X] {p : ℕ}
    (G : SimpleGraph (X ⊕ Fin p)) (hp : 0<p) :
    G.degree (Sum.inr ⟨0,hp⟩)+prefixRho G hp p=(baseNeighbors G hp).card+p := by
  let f := fun v : X ⊕ Fin p => if G.Adj (Sum.inr ⟨0,hp⟩) v then (1:ℕ) else 0
  have hdeg : G.degree (Sum.inr ⟨0,hp⟩)=∑ v, f v := by
    rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
    simp only [f,sum_boole,Nat.cast_id]
  rw [hdeg,Fintype.sum_sum_type]
  have hb : (∑ x : X, f (Sum.inl x))=(baseNeighbors G hp).card := by
    simp [f,baseNeighbors]
  rw [hb]
  have hpos : (∑ i : Fin p, f (Sum.inr i))=
      (univ.filter (fun i : Fin p => G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))).card := by simp [f]
  rw [hpos]
  have hr : prefixRho G hp p=
      (univ.filter (fun i : Fin p => ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr i))).card := by
    simp [prefixRho]
  rw [hr,add_assoc,card_filter_add_card_filter_not,card_univ,Fintype.card_fin]

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {hj : j+1≤p} (hp : 0<p)
    (A : GLWState G (prefixRho G hp) (j+1) hj)

theorem base_card_le_neighbors_add_missing :
    (baseNeighbors G hp).card≤A.neighborFinset.card+baseMissing G hp ⟨j,hj⟩ := by
  let B := baseNeighbors G hp
  let M := B.filter (fun x => ¬G.Adj (Sum.inr (⟨j,hj⟩ : Fin p)) (Sum.inl x))
  have hsub : B⊆A.neighborFinset∪M := by
    intro x hx
    by_cases hg : G.Adj (Sum.inr (⟨j,hj⟩ : Fin p)) (Sum.inl x)
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      have hR : A.routes.graph.Adj (Sum.inl x) (lastVertex j) := A.originals hg.symm
      exact (A.routes.graph_adj_iff_multiplicity _ _).mp hR |>.2
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,hg⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

theorem clone_size_bound {d t : ℕ} (hpt : p<t) (hd : 7*t≤d)
    (hdegree : d≤G.degree (Sum.inr ⟨0,hp⟩))
    (hordered : ∀ i : Fin p, i.val≠0 →
      baseMissing G hp i≤p+(i.val+1)+prefixRho G hp (i.val+1)) :
    3*t+2*(A.routes.doubleExternal (lastVertex j) A.neighbors).card≤Fintype.card A.neighbors := by
  have hb := root_degree_balance G hp
  have hn := A.base_card_le_neighbors_add_missing hp
  have hD := A.doubleExternal_card_le
  have hrp := prefixRho_le G hp p
  have hrj := prefixRho_monotone G hp hj
  rw [A.neighbors_card]
  by_cases hj0 : j=0
  · have hm : baseMissing G hp ⟨j,hj⟩=0 := by subst j; exact baseMissing_root G hp
    rw [hm,Nat.add_zero] at hn
    simp only [hj0,if_true] at hD
    omega
  · have hm := hordered ⟨j,hj⟩ hj0
    change baseMissing G hp ⟨j,hj⟩≤p+(j+1)+prefixRho G hp (j+1) at hm
    simp only [hj0,if_false] at hD
    omega

end GLWState
end
end Cycle13
