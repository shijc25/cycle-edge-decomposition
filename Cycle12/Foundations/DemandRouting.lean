import Cycle12.Foundations.IndexedFactorization

/-! Indexed demand routes and the exact pullback through simultaneous
edge lifts. Paths may be shortened after composition without creating
shared edges. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure DemandRouting {V I : Type} (G : SimpleGraph V) (a b : I → V) where
  route : ∀ i, G.Walk (a i) (b i)
  disjoint : Pairwise (fun i j => Disjoint (route i).edgeSet (route j).edgeSet)

namespace DemandRouting
variable {V I J : Type} {G : SimpleGraph V} {a b : I → V}

def restrict (R : DemandRouting G a b) (e : J ↪ I) :
    DemandRouting G (a ∘ e) (b ∘ e) where
  route i := R.route (e i)
  disjoint _ _ h := R.disjoint (e.injective.ne h)

theorem simple_paths (R : DemandRouting G a b) :
    ∃ p : ∀ i, G.Walk (a i) (b i), (∀ i, (p i).IsPath) ∧
      Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet) := by
  classical
  exact ⟨fun i => (R.route i).bypass,fun i => Walk.bypass_isPath _,
    fun i j h => (R.disjoint h).mono (Walk.edges_bypass_subset_edges _) (Walk.edges_bypass_subset_edges _)⟩

end DemandRouting

variable {V I : Type} [DecidableEq I]

abbrev LiftIndex (F : Finset I) := {i // i∉F} ⊕ (F × Bool)

abbrev liftLeft (a : I → V) (hub : I → V) (F : Finset I) : LiftIndex F → V
  | .inl i => a i.val
  | .inr (i,false) => a i.val
  | .inr (i,true) => hub i.val

abbrev liftRight (b : I → V) (hub : I → V) (F : Finset I) : LiftIndex F → V
  | .inl i => b i.val
  | .inr (i,false) => hub i.val
  | .inr (i,true) => b i.val

def pullbackLiftWalk {G : SimpleGraph V} {a b hub : I → V} {F : Finset I}
    (R : DemandRouting G (liftLeft a hub F) (liftRight b hub F)) (i : I) : G.Walk (a i) (b i) :=
  if hi : i∈F then
    (R.route (.inr (⟨i,hi⟩,false))).append (R.route (.inr (⟨i,hi⟩,true)))
  else R.route (.inl ⟨i,hi⟩)

theorem pullbackLiftWalk_disjoint {G : SimpleGraph V} {a b hub : I → V} {F : Finset I}
    (R : DemandRouting G (liftLeft a hub F) (liftRight b hub F)) :
    Pairwise (fun i j => Disjoint (pullbackLiftWalk R i).edgeSet (pullbackLiftWalk R j).edgeSet) := by
  intro i j hij
  have hcross : ∀ (x y : Bool) (hi : i∈F) (hj : j∈F),
      Disjoint (R.route (.inr (⟨i,hi⟩,x))).edgeSet (R.route (.inr (⟨j,hj⟩,y))).edgeSet := by
    intro x y hi hj
    apply R.disjoint
    intro h
    exact hij (congrArg (fun z : F × Bool => z.1.val) (Sum.inr.inj h))
  have hpos : ∀ (i : I) (hi : i∈F), pullbackLiftWalk R i=
      (R.route (.inr (⟨i,hi⟩,false))).append (R.route (.inr (⟨i,hi⟩,true))) := by
    intro i hi
    exact dite_eq_left hi
  have hneg : ∀ (i : I) (hi : i∉F), pullbackLiftWalk R i=R.route (.inl ⟨i,hi⟩) := by
    intro i hi
    exact dite_eq_right hi
  by_cases hi : i∈F <;> by_cases hj : j∈F
  · rw [hpos i hi,hpos j hj,Walk.edgeSet_append,Walk.edgeSet_append]
    exact ((hcross false false hi hj).union_right (hcross false true hi hj)).union_left
      ((hcross true false hi hj).union_right (hcross true true hi hj))
  · rw [hpos i hi,hneg j hj,Walk.edgeSet_append]
    apply Disjoint.union_left <;> apply R.disjoint <;> intro h <;> cases h
  · rw [hneg i hi,hpos j hj,Walk.edgeSet_append]
    apply Disjoint.union_right <;> apply R.disjoint <;> intro h <;> cases h
  · rw [hneg i hi,hneg j hj]
    apply R.disjoint
    intro h
    exact hij (congrArg Subtype.val (Sum.inl.inj h))

def DemandRouting.pullback_lift {G : SimpleGraph V} {a b hub : I → V} {F : Finset I}
    (R : DemandRouting G (liftLeft a hub F) (liftRight b hub F)) : DemandRouting G a b :=
  ⟨pullbackLiftWalk R,pullbackLiftWalk_disjoint R⟩

end
end Cycle13
