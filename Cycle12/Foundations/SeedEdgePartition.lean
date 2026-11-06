import Cycle12.Foundations.HubProtection
import Cycle12.Foundations.DemandRelabel

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

abbrev SeedInterior (w : Fin 3 ↪ V) := {v : V // ∀ r, v≠w r}
abbrev SeedKeep (a b : I → V) (w : Fin 3 ↪ V) := {i // ¬seedEdgePred a b w i}
abbrev SeedStar (a b : I → V) (w : Fin 3 ↪ V) := {i // seedEdgePred a b w i}
abbrev seedInteriorEmbedding (w : Fin 3 ↪ V) : SeedInterior w ↪ V :=
  ⟨Subtype.val,Subtype.val_injective⟩

def seedKeepLeft (a b : I → V) (w : Fin 3 ↪ V) (i : SeedKeep a b w) : SeedInterior w :=
  ⟨a i.val,fun r h => i.property ⟨r,Or.inl h⟩⟩
def seedKeepRight (a b : I → V) (w : Fin 3 ↪ V) (i : SeedKeep a b w) : SeedInterior w :=
  ⟨b i.val,fun r h => i.property ⟨r,Or.inr h⟩⟩

def seedSplitEquiv (a b : I → V) (w : Fin 3 ↪ V) :
    SeedKeep a b w ⊕ SeedStar a b w ≃ I :=
  (Equiv.sumComm _ _).trans (Equiv.sumCompl (seedEdgePred a b w))

namespace SeedEdgeData
variable {a b : I → V} {w : Fin 3 ↪ V} (D : SeedEdgeData a b w)

def otherVertex (i : SeedStar a b w) : SeedInterior w := ⟨D.other i,D.other_ne i⟩

theorem group_eq_of_incident (i : SeedStar a b w) (r : Fin 3)
    (hi : a i.val=w r ∨ b i.val=w r) : D.group i=r := by
  rcases D.ends i with h | h <;> rcases hi with hi | hi
  · exact w.injective (h.1.symm.trans hi)
  · exact (D.other_ne i r (h.2.symm.trans hi)).elim
  · exact (D.other_ne i r (h.2.symm.trans hi)).elim
  · exact w.injective (h.1.symm.trans hi)

theorem fiber_card (r : Fin 3) :
    (univ.filter (fun i => D.group i=r)).card=(indexedIncident a b (w r)).card := by
  apply card_bij (fun i _ => i.val)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2 ▸ D.group_incident i⟩
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    have hi := (mem_filter.mp hi).2
    let j : SeedStar a b w := ⟨i,⟨r,hi⟩⟩
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,D.group_eq_of_incident j r hi⟩,rfl⟩

theorem fiber_degree (hne : ∀ i, a i≠b i) (r : Fin 3) :
    (univ.filter (fun i => D.group i=r)).card=Suppression.incidenceDegree a b (w r) := by
  rw [D.fiber_card,indexedIncident_card_eq a b hne]

theorem fiber_degree_general (r : Fin 3) :
    (univ.filter (fun i => D.group i=r)).card=Suppression.incidenceDegree a b (w r) := by
  rw [D.fiber_card]
  have hno : ∀ i, ¬(a i=w r ∧ b i=w r) := by
    intro i hi
    let j : SeedStar a b w := ⟨i,⟨r,Or.inl hi.1⟩⟩
    rcases D.ends j with hh | hh
    · exact D.other_ne j r (hh.2.symm.trans hi.2)
    · exact D.other_ne j r (hh.2.symm.trans hi.1)
  have hp : ∀ i, (if a i=w r ∨ b i=w r then (1:ℕ) else 0)=
      (if a i=w r then 1 else 0)+(if b i=w r then 1 else 0) := by
    intro i
    by_cases ha : a i=w r <;> by_cases hb : b i=w r
    · exact (hno i ⟨ha,hb⟩).elim
    all_goals simp [ha,hb]
  have hh := sum_congr (s₁:=(univ : Finset I)) rfl (fun i _ => hp i)
  simpa only [sum_boole,Nat.cast_id,indexedIncident,Suppression.incidenceDegree] using hh

theorem split_endpoints (j : SeedKeep a b w ⊕ SeedStar a b w) :
    ((Sum.elim ((seedInteriorEmbedding w) ∘ seedKeepLeft a b w) (w ∘ D.group)) j=a (seedSplitEquiv a b w j) ∧
      ((seedInteriorEmbedding w) ∘ Sum.elim (seedKeepRight a b w) D.otherVertex) j=b (seedSplitEquiv a b w j)) ∨
    ((Sum.elim ((seedInteriorEmbedding w) ∘ seedKeepLeft a b w) (w ∘ D.group)) j=b (seedSplitEquiv a b w j) ∧
      ((seedInteriorEmbedding w) ∘ Sum.elim (seedKeepRight a b w) D.otherVertex) j=a (seedSplitEquiv a b w j)) := by
  cases j with
  | inl j => exact Or.inl ⟨rfl,rfl⟩
  | inr j =>
    rcases D.ends j with h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.1.symm,h.2.symm⟩

theorem split_degree (v : V) :
    Suppression.incidenceDegree
      (Sum.elim ((seedInteriorEmbedding w) ∘ seedKeepLeft a b w) (w ∘ D.group))
      ((seedInteriorEmbedding w) ∘ Sum.elim (seedKeepRight a b w) D.otherVertex) v=
      Suppression.incidenceDegree a b v :=
  incidence_relabel a b _ _ (seedSplitEquiv a b w) D.split_endpoints v

end SeedEdgeData
end
end Cycle13
