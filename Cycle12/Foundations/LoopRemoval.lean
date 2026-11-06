import Cycle12.Foundations.DemandPartition

/-! Loops are resolved by empty walks. Removing them never increases a
degree, so residual demands may retain formal loops during accounting. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype I] [DecidableEq I] [DecidableEq V]

def loopRouting (G : SimpleGraph V) (a b : I → V) (h : ∀ i, a i=b i) : DemandRouting G a b where
  route i := (.nil : G.Walk (a i) (a i)).copy rfl (h i)
  disjoint := by intro i j hij; simp

theorem loopRouting_edgeSet (G : SimpleGraph V) (a b : I → V) (h : ∀ i, a i=b i) (i : I) :
    ((loopRouting G a b h).route i).edgeSet=∅ := by simp [loopRouting]

def DemandRouting.restore_loops {G : SimpleGraph V} {a b : I → V}
    (R : DemandRouting G (fun i : {i // a i≠b i} => a i.val) (fun i => b i.val)) :
    DemandRouting G a b := by
  let L := loopRouting G (fun i : {i // ¬a i≠b i} => a i.val) (fun i => b i.val)
    (fun i => Classical.not_not.mp i.property)
  have hcross : ∀ i j, Disjoint (R.route i).edgeSet (L.route j).edgeSet := by
    intro i j
    rw [loopRouting_edgeSet]
    simp
  exact (R.sum L hcross).relabel (Equiv.sumCompl (fun i => a i≠b i))
    (by intro i; cases i <;> exact Or.inl ⟨rfl,rfl⟩)

theorem nonloop_degree_le (a b : I → V) (v : V) :
    Suppression.incidenceDegree (fun i : {i // a i≠b i} => a i.val) (fun i => b i.val) v ≤
      Suppression.incidenceDegree a b v := by
  let weight : I → ℕ := fun i => (if a i=v then 1 else 0)+(if b i=v then 1 else 0)
  change (∑ i : {i // a i≠b i}, weight i.val) ≤ ∑ i, weight i
  rw [← sum_subtype (univ.filter (fun i => a i≠b i)) (p:=fun i => a i≠b i)
    (fun i => by simp) weight]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

end
end Cycle13
