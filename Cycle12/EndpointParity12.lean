import Cycle12.Foundations.DistinctEndpointPaths
import Cycle12.Foundations.PathEndpointLoad

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I]

theorem path_endpoint_parity {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet))
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v) := by
  have hh := trail_partition_even_degree_iff G (fun i => (P i).walk)
    (fun i => (P i).isPath.isTrail) hd hc v
  rw [endpointLoad_eq_incident_card _ _ (fun i => (P i).endpoints_ne)]
  have hf : (univ.filter (fun i => (P i).start = v ∨ (P i).finish = v)) =
      (univ.filter (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))) := by
    ext i
    simp only [mem_filter,mem_univ,true_and]
    have hn := (P i).endpoints_ne
    tauto
  rw [hf]
  exact hh

/-- Odd-degree vertices have exactly one endpoint in every path partition
whose endpoint load is at most two. Isolates have no endpoints. -/
theorem path_endpoint_control {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet))
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ v, endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v ≤ 2) :
    (∀ v, Odd (G.degree v) → endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v = 1) ∧
    (∀ v, G.degree v = 0 → endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v = 0) := by
  constructor
  · intro v hv
    have hp := path_endpoint_parity P hd hc v
    have ho : Odd (endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v) := by
      rw [← Nat.not_even_iff_odd,← hp]
      exact Nat.not_even_iff_odd.mpr hv
    obtain ⟨j,hj⟩ := ho
    have hh := hl v
    omega
  · intro v hv
    have hb := endpointLoad_le_original_degree G _ _ (fun i => (P i).walk)
      (fun i => (P i).endpoints_ne) hd v
    omega

/-- Endpoint-controlled Lovász partition for the second pass. Every
positive-degree vertex outside `A` is odd, so it consumes one connector. -/
theorem endpoint_partition_outside_odd (G : SimpleGraph V) (A : Finset V)
    (hodd : ∀ v, v ∉ A → 0 < G.degree v → Odd (G.degree v)) :
    ∃ k : ℕ, ∃ P : Fin k → PositiveSimplePath G,
      Pairwise (fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = G.edgeSet ∧
      (∀ v, endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v ≤ 2) ∧
      (∀ v, v ∉ A → endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v ≤ 1) ∧
      2*k ≤ Fintype.card V+A.card := by
  obtain ⟨k,P,hd,hc,hl,_⟩ := endpoint_path_partition G
  have hload : ∀ v, endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v ≤ 2 := by
    intro v
    rw [endpointLoad_eq_incident_card _ _ (fun i => (P i).endpoints_ne)]
    exact hl v
  obtain ⟨hoddload,hzero⟩ := path_endpoint_control P hd hc hload
  have hout : ∀ v, v ∉ A → endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v ≤ 1 := by
    intro v hv
    by_cases hz : G.degree v = 0
    · rw [hzero v hz]; omega
    · rw [hoddload v (hodd v hv (Nat.pos_of_ne_zero hz))]
  have hbound := sum_le_sum (s := univ) (f := fun v =>
      endpointLoad (fun i => (P i).start) (fun i => (P i).finish) v)
    (g := fun v => if v ∈ A then 2 else 1) (fun v _ => by
      by_cases hv : v ∈ A
      · simpa only [if_pos hv] using hload v
      · simpa only [if_neg hv] using hout v hv)
  rw [sum_endpointLoad,Fintype.card_fin] at hbound
  have hsum : (∑ v : V, if v ∈ A then 2 else 1) = Fintype.card V+A.card := by
    have he : (fun v : V => if v ∈ A then 2 else 1) = fun v => 1+if v ∈ A then 1 else 0 := by
      funext v
      by_cases hv : v ∈ A <;> simp [hv]
    rw [he,sum_add_distrib]
    simp
  exact ⟨k,P,hd,hc,hload,hout,hsum ▸ hbound⟩

/-- The virtual-hub augmentation has a genuine path partition with every
old vertex an endpoint exactly once; its paths have distinct endpoints. -/
theorem augmented_distinct_endpoint_partition (G : SimpleGraph V) :
    ∃ P : DistinctEndpointPaths (evenAugmentation G),
      2*P.count ≤ Fintype.card V+1 ∧
      ∀ v : V, endpointLoad (fun i => (P.paths i).start) (fun i => (P.paths i).finish) (some v) = 1 := by
  obtain ⟨P⟩ := distinct_endpoint_paths_of_almost_all_odd (evenAugmentation G) none (by
    intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some x => exact evenAugmentation_old_odd G x)
  have hb : 2*P.count ≤ Fintype.card V+1 := by simpa only [Fintype.card_option] using P.count_bound
  let S : Finset (Option V) := univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,card_image_of_injective _ (Option.some_injective V),card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    exact evenAugmentation_old_odd G v
  obtain ⟨_,hl⟩ := tight_odd_trail_partition (evenAugmentation G) S (fun i => (P.paths i).walk)
    (fun i => (P.paths i).isPath.isTrail) P.disjoint P.cover ho
    (by simpa only [Fintype.card_fin,hS] using hb)
  refine ⟨P,hb,?_⟩
  intro v
  have hh := hl (some v) (mem_image.mpr ⟨v,mem_univ _,rfl⟩)
  rw [endpointLoad_eq_incident_card _ _ (fun i => (P.paths i).endpoints_ne)]
  convert hh using 1
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  have hne := (P.paths i).endpoints_ne
  tauto

end
end Cycle12
