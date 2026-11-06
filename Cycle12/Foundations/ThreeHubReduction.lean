import Cycle12.Foundations.SeedReduction
import Cycle12.Foundations.DemandPartition

/-! A complete three-hub reduction with explicit local capacity. All old
interior demands are retained. Protected vertices receive no extra degree
and their induced independent set is preserved. The route implication is
proved by actual walks, including parallel demands. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

set_option maxHeartbeats 1000000 in
theorem exists_three_hub_reduction (a b : I → V)
    (w : Fin 3 ↪ V) (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    (F : Finset I) (hF : ∀ v, indexedDegreeOn a b F v ≤ 2)
    (B : Finset V) (hB : B.card ≤ 3)
    (hquota : ∀ r, Suppression.incidenceDegree a b (w r)+5 ≤
      Fintype.card V/3+indexedDegreeOn a b F (w r)) :
    ∃ D : SeedEdgeData (remainderLeft a F) (remainderLeft b F) w,
    ∃ target : SeedStar (remainderLeft a F) (remainderLeft b F) w ↪ SeedInterior w,
      (∀ i, (target i).val∉B) ∧
      (∀ v : SeedInterior w,
        Suppression.incidenceDegree (D.residualLeft target) D.residualRight v+
          indexedDegreeOn a b F v.val ≤ Suppression.incidenceDegree a b v.val+1) ∧
      (∀ v : SeedInterior w, v.val∈B →
        Suppression.incidenceDegree (D.residualLeft target) D.residualRight v+
          indexedDegreeOn a b F v.val=Suppression.incidenceDegree a b v.val) ∧
      ((∀ i, i∉F → ¬(a i∈B ∧ b i∈B)) →
        ∀ j, ¬((D.residualLeft target j).val∈B ∧ (D.residualRight j).val∈B)) ∧
      (DemandRouting (completeGraph (SeedInterior w)) (D.residualLeft target) D.residualRight →
        Nonempty (DemandRouting (completeGraph V) a b)) := by
  obtain ⟨f,hfixed,hbalanced⟩ := exists_cyclic_balanced_lifting_coloring
    (factorLeft a F) (factorLeft b F) w (fun r s i => hsep r s i.val)
    (by intro v; rw [indexedDegreeOn_subtype]; exact hF v)
  let D := seedEdgeData (remainderLeft a F) (remainderLeft b F) w (fun r s i => hsep r s i.val)
  have hfi : Function.Injective (fun r => f (.inl (w r))) := by
    intro r s h
    change f (.inl (w r))=f (.inl (w s)) at h
    rw [hfixed,hfixed] at h
    exact shiftThree.injective h
  have hq : ∀ r, Suppression.incidenceDegree (remainderLeft a F) (remainderLeft b F) (w r)+5 ≤
      Fintype.card V/3 := by
    intro r
    have h := hquota r
    have he := remainder_degree_add_factor a b F (w r)
    omega
  obtain ⟨target,ht⟩ := exists_seed_targets (remainderLeft a F) (remainderLeft b F)
    w D (fun v => f (.inl v)) hbalanced hfi B hB hq
  refine ⟨D,target,fun i => (ht i).2,?_,?_,?_,?_⟩
  · intro v
    have h := D.residual_degree_le target v
    have he := remainder_degree_add_factor a b F v.val
    omega
  · intro v hv
    have h := D.residual_protected_degree target v (by
      intro i he
      exact (ht i).2 (congrArg Subtype.val he ▸ hv))
    have he := remainder_degree_add_factor a b F v.val
    omega
  · intro hBsep
    exact D.residual_preserves_independent target B (fun i => (ht i).2)
      (fun i => hBsep i.val i.property)
  · intro R
    let P := indexedHubGraph (factorLeft a F) (factorLeft b F) (fun i => w (f (.inr i)))
    let Rold := D.pullbackResidual target R
    let Rfactor := hubColorRouting (factorLeft a F) (factorLeft b F) w f hfixed
    have hPinside : ∀ u v : SeedInterior w, ¬P.Adj u.val v.val := by
      intro u v h
      rcases indexedHubGraph_touches_hubs _ _ _ h with hu | hv
      · obtain ⟨i,hi⟩ := hu
        exact u.property _ hi.symm
      · obtain ⟨i,hi⟩ := hv
        exact v.property _ hi.symm
    have hPstar : ∀ i, ¬P.Adj (w (D.group i)) (target i).val := by
      intro i
      exact colored_hub_avoids_class (factorLeft a F) (factorLeft b F) w f
        (D.group i) (target i).val (target i).property (ht i).1
    have havoid := D.pullbackResidual_avoids target R P hPinside hPstar
    have hused : ∀ i : F, (Rfactor.route i).edgeSet ⊆ P.edgeSet := by
      intro i e he
      exact (indexedHubGraph_edge _ _ _ e).mpr ⟨i,he⟩
    exact ⟨combineFactorRouting a b F Rfactor Rold (fun i j =>
      (havoid j).symm.mono_left (hused i))⟩

end
end Cycle13
