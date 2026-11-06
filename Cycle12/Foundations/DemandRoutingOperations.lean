import Cycle12.Foundations.CliqueHop

namespace Cycle13
open SimpleGraph
noncomputable section

namespace DemandRouting
variable {U V I J : Type} {G : SimpleGraph U} {H : SimpleGraph V} {a b c : I → U}

def map (R : DemandRouting G a b) (f : G →g H) (hf : Function.Injective f) :
    DemandRouting H (f ∘ a) (f ∘ b) where
  route i := (R.route i).map f
  disjoint := by
    intro i j hij
    rw [Walk.edgeSet_map,Walk.edgeSet_map]
    exact Set.disjoint_image_of_injective (Sym2.map.injective hf) (R.disjoint hij)

def append (R : DemandRouting G a b) (S : DemandRouting G b c)
    (hcross : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) : DemandRouting G a c where
  route i := (R.route i).append (S.route i)
  disjoint := by
    intro i j hij
    rw [Walk.edgeSet_append,Walk.edgeSet_append]
    exact ((R.disjoint hij).union_right (hcross i j)).union_left
      ((hcross j i).symm.union_right (S.disjoint hij))

def sum {d e : J → U} (R : DemandRouting G a b) (S : DemandRouting G d e)
    (hcross : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) :
    DemandRouting G (Sum.elim a d) (Sum.elim b e) where
  route i := match i with
    | .inl i => R.route i
    | .inr j => S.route j
  disjoint := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact R.disjoint (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hcross i j
    | inr i =>
      cases j with
      | inl j => exact (hcross j i).symm
      | inr j => exact S.disjoint (fun h => hij (congrArg Sum.inr h))

end DemandRouting

abbrev completeEmbeddingHom {U V : Type} (e : U ↪ V) : completeGraph U →g completeGraph V where
  toFun := e
  map_rel' := fun h => e.injective.ne h

theorem cliqueHop_disjoint_inside {U V : Type} (e : U ↪ V) (x : V)
    (hx : ∀ u, x≠e u) (y : U) {a b : U} (p : (completeGraph U).Walk a b) :
    Disjoint (cliqueHop x (e y)).edgeSet (p.map (completeEmbeddingHom e)).edgeSet := by
  apply Set.disjoint_left.mpr
  intro d hd hp
  have hd := (cliqueHop_edge x (e y) d).mp hd
  rw [hd.2] at hp
  have hs := (p.map (completeEmbeddingHom e)).fst_mem_support_of_mem_edges hp
  rw [Walk.support_map] at hs
  obtain ⟨u,hu,he⟩ := List.mem_map.mp hs
  exact hx u he.symm

theorem indexed_star_hops_disjoint {U V I : Type} (e : U ↪ V) (x : I → V)
    (hx : ∀ i u, x i≠e u) (target : I ↪ U) :
    Pairwise (fun i j => Disjoint (cliqueHop (x i) (e (target i))).edgeSet
      (cliqueHop (x j) (e (target j))).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro d hi hj
  have hi := (cliqueHop_edge _ _ d).mp hi
  have hj := (cliqueHop_edge _ _ d).mp hj
  rcases Sym2.eq_iff.mp (hi.2.symm.trans hj.2) with h | h
  · exact hij (target.injective (e.injective h.2))
  · exact hx i (target j) h.1

end
end Cycle13
