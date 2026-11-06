import Cycle12.Foundations.SeedEdgePartition
import Cycle12.Foundations.FiberTargets

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem balanced_available_of_seed_injective (f : V → Fin 3)
    (hf : ∀ r s, colorSize f r ≤ colorSize f s+2)
    (w : Fin 3 ↪ V) (hw : Function.Injective (fun r => f (w r)))
    (B : Finset V) (hB : B.card ≤ 3) (r : Fin 3) :
    Fintype.card V/3 ≤ ((univ.filter (fun v => f v=r))\((univ.image w)∪B)).card+5 := by
  let A := univ.filter (fun v => f v=r)
  have hwcard : (A∩(univ.image w)).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨s,hs,rfl⟩ := mem_image.mp (mem_inter.mp hx).2
    obtain ⟨t,ht,rfl⟩ := mem_image.mp (mem_inter.mp hy).2
    have he := (mem_filter.mp (mem_inter.mp hx).1).2.trans
      (mem_filter.mp (mem_inter.mp hy).1).2.symm
    exact congrArg w (hw he)
  have hloss : (A∩((univ.image w)∪B)).card ≤ 4 := by
    rw [inter_union_distrib_left]
    have hh := card_union_le (A∩(univ.image w)) (A∩B)
    have hAB := card_le_card (inter_subset_right (s₁:=A) (s₂:=B))
    omega
  have he := card_sdiff_add_card_inter A ((univ.image w)∪B)
  have hlo := balanced_three_class_lower f hf r
  change Fintype.card V/3 ≤ A.card+1 at hlo
  change Fintype.card V/3 ≤ (A\((univ.image w)∪B)).card+5
  omega

theorem seedInterior_available_card (f : V → Fin 3) (w : Fin 3 ↪ V) (B : Finset V) (r : Fin 3) :
    (univ.filter (fun v : SeedInterior w => f v.val=r ∧ v.val∉B)).card=
      ((univ.filter (fun v => f v=r))\((univ.image w)∪B)).card := by
  apply card_bij (fun v _ => v.val)
  · intro v hv
    have hv := (mem_filter.mp hv).2
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,hv.1⟩,?_⟩
    intro h
    rcases mem_union.mp h with h | h
    · obtain ⟨s,hs,he⟩ := mem_image.mp h
      exact v.property s he.symm
    · exact hv.2 h
  · intro v hv u hu he
    exact Subtype.ext he
  · intro v hv
    have hv := mem_sdiff.mp hv
    have hnon : ∀ r, v≠w r := by
      intro r he
      exact hv.2 (mem_union_left B (mem_image.mpr ⟨r,mem_univ _,he.symm⟩))
    refine ⟨⟨v,hnon⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv.1).2,?_⟩,rfl⟩
    intro hB
    exact hv.2 (mem_union_right _ hB)

theorem exists_seed_targets (a b : I → V) (w : Fin 3 ↪ V)
    (D : SeedEdgeData a b w) (f : V → Fin 3)
    (hf : ∀ r s, colorSize f r ≤ colorSize f s+2)
    (hw : Function.Injective (fun r => f (w r))) (B : Finset V) (hB : B.card ≤ 3)
    (hquota : ∀ r, Suppression.incidenceDegree a b (w r)+5 ≤ Fintype.card V/3) :
    ∃ target : SeedStar a b w ↪ SeedInterior w,
      ∀ i, f (target i).val=D.group i ∧ (target i).val∉B := by
  apply exists_fiber_targets D.group (fun v : SeedInterior w => f v.val) (fun v => v.val∉B)
  intro r
  rw [D.fiber_degree_general]
  have he := seedInterior_available_card f w B r
  have ha := balanced_available_of_seed_injective f hf w hw B hB r
  have hq := hquota r
  simp only [← Set.ncard_coe_finset,coe_filter,coe_univ,coe_sdiff,coe_union,coe_image] at he ha ⊢
  rw [he]
  omega

end
end Cycle13
