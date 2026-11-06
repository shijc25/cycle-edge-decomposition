import Cycle12.ReservedPathFamily12
import Cycle12.EndpointParity12
import Cycle12.Foundations.WeightedPacking

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W T : Type} [Fintype V] [Fintype W] [Fintype T]

/-- The endpoint-controlled second pass uses exactly the spokes reserved
before the first pass. Every positive-degree vertex outside A is odd and
therefore requires only one slot; vertices in A require at most two. -/
theorem second_pass_reservoir_packing [Nonempty V]
    (J : SimpleGraph W) (G H R : SimpleGraph V) (hHG : H ≤ G)
    (f : J →g G) (hf : Function.Injective f) (A : Finset W)
    (hodd : ∀ w, w ∉ A → 0 < J.degree w → Odd (J.degree w))
    (U : Finset V) (hfar : ∀ w, f w ∉ U) {z upper : ℝ} (hU : ReservoirSample H U z upper)
    (root tip : T → V) (htip : ∀ t, tip t ∈ U ∧ H.Adj (root t) (tip t))
    (hR : ∀ t, R.Adj (root t) (tip t))
    (hinj : Function.Injective (fun t => s(root t,tip t)))
    (hinside : ∀ x ∈ U, ∀ y ∈ U, H.Adj x y → R.Adj x y)
    (hload : ∀ v, ((univ.filter (fun t => tip t = v)).card:ℝ) ≤ z/64)
    (hslots : ∀ w, (if w ∈ A then 2 else 1) ≤ Fintype.card {t // root t = f w})
    (hz : 8192 ≤ z) (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) :
    ∃ P : CyclePacking G,
      2*P.count ≤ Fintype.card W+A.card ∧
      Sym2.map f '' J.edgeSet ⊆ P.used ∧
      P.used ⊆ (Sym2.map f '' J.edgeSet) ∪ R.edgeSet := by
  obtain ⟨k,P,hd,hc,hall,hout,hk⟩ := endpoint_partition_outside_odd J A hodd
  let source : Fin k × Bool → V := fun t => f (if t.2 then (P t.1).finish else (P t.1).start)
  let Q : ∀ i, G.Walk (source (i,false)) (source (i,true)) := fun i => (P i).walk.map f
  have hne : ∀ i, source (i,false) ≠ source (i,true) := fun i he => (P i).endpoints_ne (hf he)
  have hQ : ∀ i, (Q i).IsPath := fun i => (P i).isPath.map hf
  have hedge : ∀ i, (Q i).edgeSet = Sym2.map f '' (P i).walk.edgeSet :=
    fun i => Walk.edgeSet_map _ _
  have hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) := by
    intro i j hij
    rw [hedge,hedge]
    exact (Set.disjoint_image_iff (Sym2.map.injective hf)).mpr (hd hij)
  have hQU : ∀ i, ∀ v ∈ (Q i).support, v ∉ U := by
    intro i v hv
    change v ∈ ((P i).walk.map f).support at hv
    rw [Walk.support_map] at hv
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
    exact hfar w
  have hcapacity : ∀ v, Fintype.card {t // source t = v} ≤ Fintype.card {t // root t = v} := by
    intro v
    by_cases hv : v ∈ Set.range f
    · obtain ⟨w,rfl⟩ := hv
      have he : Fintype.card {t // source t = f w} =
          Cycle13.endpointLoad (fun i => (P i).start) (fun i => (P i).finish) w := by
        calc
          _ = Fintype.card {t : Fin k × Bool // (if t.2 then (P t.1).finish else (P t.1).start) = w} :=
            Fintype.card_congr (Equiv.subtypeEquivRight (fun t => by
              change f _ = f w ↔ _
              exact hf.eq_iff))
          _ = _ := by
            convert endpoint_bool_fiber_card (fun i : Fin k => (P i).start) (fun i => (P i).finish) w using 1
      rw [he]
      apply le_trans _ (hslots w)
      by_cases hw : w ∈ A
      · simpa only [if_pos hw] using hall w
      · simpa only [if_neg hw] using hout w hw
    · letI : IsEmpty {t // source t = v} := ⟨fun t => hv
        ⟨if t.val.2 then (P t.val.1).finish else (P t.val.1).start,t.property⟩⟩
      rw [Fintype.card_eq_zero]
      exact Nat.zero_le _
  have hcard : k ≤ Fintype.card V := by
    have ha := Finset.card_le_univ A
    have hv := Fintype.card_le_of_injective f hf
    omega
  have hI : 2112*(Fintype.card (Fin k):ℝ) ≤ z^2 := by
    simp only [Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard)
      (by norm_num : (0:ℝ) ≤ 2112)).trans hsquare
  obtain ⟨C,hC,hCC,hQC,hCR⟩ := close_paths_with_reserved_spokes G H R hHG U hU root tip htip hR hinj
    hinside hload source Q hne hQ hQQ hQU hcapacity hz hlog hI
  let S : CyclePacking G := ⟨k,fun i => (C i).edgeSet,fun i => ⟨_,C i,hC i,rfl⟩,hCC⟩
  have hcover : (⋃ i, (Q i).edgeSet) = Sym2.map f '' J.edgeSet := by
    simp only [hedge,←Set.image_iUnion,hc]
  refine ⟨S,hk,?_,?_⟩
  · rw [←hcover]
    apply Set.iUnion_subset
    intro i
    exact (hQC i).trans (Set.subset_iUnion (fun i => (C i).edgeSet) i)
  · intro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    rcases hCR i hi with hi | hi
    · exact Or.inl (hcover ▸ Set.mem_iUnion.mpr ⟨i,hi⟩)
    · exact Or.inr hi

end
end Cycle12
