import Cycle12.Foundations.DemandRoutingOperations

/-! Replacing all old star edges simultaneously by distinct targets in
the retained vertex set. A resolution of the residual demand pulls back
to a resolution of every old edge and avoids a prescribed protection graph. -/
namespace Cycle13
open SimpleGraph
noncomputable section
variable {U V K I : Type}

def starPrefix (e : U ↪ V) (x : I → V) (hx : ∀ i u, x i≠e u)
    (a : K → U) (target : I ↪ U) :
    DemandRouting (completeGraph V) (Sum.elim (e ∘ a) x) (e ∘ Sum.elim a target) where
  route j := match j with
    | .inl k => .nil
    | .inr i => cliqueHop (x i) (e (target i))
  disjoint := by
    intro i j hij
    cases i with
    | inl k => cases j <;> simp
    | inr i =>
      cases j with
      | inl k => simp
      | inr j => exact indexed_star_hops_disjoint e x hx target (fun h => hij (congrArg Sum.inr h))

def starDemandPullback (e : U ↪ V) (x : I → V) (hx : ∀ i u, x i≠e u)
    (a b : K → U) (other : I → U) (target : I ↪ U)
    (R : DemandRouting (completeGraph U) (Sum.elim a target) (Sum.elim b other)) :
    DemandRouting (completeGraph V) (Sum.elim (e ∘ a) x) (e ∘ Sum.elim b other) := by
  let P := starPrefix e x hx a target
  let Q := R.map (completeEmbeddingHom e) e.injective
  apply P.append Q
  intro i j
  cases i with
  | inl k => simp [P,starPrefix]
  | inr i => exact cliqueHop_disjoint_inside e (x i) (hx i) (target i) (R.route j)

theorem mapped_walk_disjoint_graph (e : U ↪ V) (B : SimpleGraph V)
    (hB : ∀ u v, ¬B.Adj (e u) (e v)) {a b : U} (p : (completeGraph U).Walk a b) :
    Disjoint (p.map (completeEmbeddingHom e)).edgeSet B.edgeSet := by
  apply Set.disjoint_left.mpr
  intro d hd hBd
  rw [Walk.edgeSet_map] at hd
  obtain ⟨q,hq,rfl⟩ := hd
  induction q using Sym2.inductionOn with
  | _ u v => exact hB u v hBd

theorem cliqueHop_disjoint_graph (B : SimpleGraph V) (x y : V) (hB : ¬B.Adj x y) :
    Disjoint (cliqueHop x y).edgeSet B.edgeSet := by
  apply Set.disjoint_left.mpr
  intro d hd hBd
  have he := (cliqueHop_edge x y d).mp hd
  rw [he.2] at hBd
  exact hB hBd

theorem starDemandPullback_avoids (e : U ↪ V) (x : I → V) (hx : ∀ i u, x i≠e u)
    (a b : K → U) (other : I → U) (target : I ↪ U)
    (R : DemandRouting (completeGraph U) (Sum.elim a target) (Sum.elim b other))
    (B : SimpleGraph V) (hB : ∀ u v, ¬B.Adj (e u) (e v))
    (hstar : ∀ i, ¬B.Adj (x i) (e (target i))) :
    ∀ j, Disjoint ((starDemandPullback e x hx a b other target R).route j).edgeSet B.edgeSet := by
  intro j
  change Disjoint (((starPrefix e x hx a target).route j).append
    ((R.route j).map (completeEmbeddingHom e))).edgeSet B.edgeSet
  rw [Walk.edgeSet_append]
  apply Disjoint.union_left
  · cases j with
    | inl k => simp [starPrefix]
    | inr i => exact cliqueHop_disjoint_graph B (x i) (e (target i)) (hstar i)
  · exact mapped_walk_disjoint_graph e B hB _

end
end Cycle13
