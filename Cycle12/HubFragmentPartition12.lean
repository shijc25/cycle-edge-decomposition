import Cycle12.HubFragments12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai OAI.ErdosGallai.Lovasz
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W]

/-- A genuine Lovász partition after deleting a virtual hub. The old edges
are partitioned into at most `(n+1)/2` fragments; split fragments have
pairwise distinct near roots, and all outer endpoint loads are at most two. -/
theorem hub_fragment_partition (G : SimpleGraph V) :
    ∃ k : ℕ, ∃ F : Fin k → HubFragment G,
      2*k ≤ Fintype.card V+1 ∧
      Pairwise (fun i j => Disjoint (F i).body (F j).body) ∧
      (⋃ i, (F i).body) = G.edgeSet ∧
      (∀ v, (univ.filter (fun t : Fin k × Bool => (F t.1).outer t.2 = v)).card ≤ 2) ∧
      Function.Injective (fun t : {i // (F i).IsSplit} × Bool => (F t.1.val).near t.1.property t.2) := by
  obtain ⟨P,hk,_⟩ := augmented_distinct_endpoint_partition G
  obtain ⟨T,hd,hcover,hinj⟩ := HubFrames.frame_partition P none
  let F : Fin P.count → HubFragment G := fun i => frameFragment G (T i)
  have hmem : ∀ i e, e ∈ (F i).body ↔ Sym2.map some e ∈ (T i).path.walk.edgeSet :=
    fun i e => frameFragment_body G (T i) e
  refine ⟨P.count,F,hk,?_,?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    exact Set.disjoint_left.mp (hd hij) ((hmem i e).mp hi) ((hmem j e).mp hj)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      have he := hcover ▸ Set.mem_iUnion.mpr ⟨i,(hmem i e).mp hi⟩
      induction e using Sym2.inductionOn with | _ a b => exact he
    · intro he
      have he' : Sym2.map some e ∈ (evenAugmentation G).edgeSet := by
        induction e using Sym2.inductionOn with | _ a b => exact he
      rw [←hcover] at he'
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he'
      exact ⟨i,(hmem i e).mpr hi⟩
  · intro v
    have he : univ.filter (fun t : Fin P.count × Bool => (F t.1).outer t.2 = v) =
        univ.filter (fun t : Fin P.count × Bool => HubFrames.outer (T t.1) t.2 = some v) := by
      ext t
      simp only [mem_filter,mem_univ,true_and]
      rw [←frameFragment_outer G (T t.1) t.2]
      exact Option.some_inj.symm
    rw [he]
    convert HubFrames.outer_load T hd hinj (some v) using 1
    congr 1
    ext t
    simp only [mem_filter,mem_univ,true_and]
  · rintro ⟨i,b⟩ ⟨j,c⟩ he
    let ii : {i // HubFrames.IsThrough (T i)} := ⟨i.val,(frameFragment_isSplit G (T i)).mp i.property⟩
    let jj : {i // HubFrames.IsThrough (T i)} := ⟨j.val,(frameFragment_isSplit G (T j)).mp j.property⟩
    have hroot : HubFrames.near (T ii.val) ii.property b = HubFrames.near (T jj.val) jj.property c := by
      have hh := congrArg some he
      simpa only [F,frameFragment_near] using hh
    have ht := HubFrames.through_roots_injective T hd (a₁ := (ii,b)) (a₂ := (jj,c)) hroot
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun t => t.1.val) ht)
    · simpa only using (congrArg (fun t : {i // HubFrames.IsThrough (T i)} × Bool => t.2) ht)

/-- Embed the complete fragment ledger into an ambient graph without
changing the path count or endpoint capacities. -/
theorem mapped_hub_fragment_partition (J : SimpleGraph W) (G : SimpleGraph V)
    (f : J →g G) (hf : Function.Injective f) :
    ∃ k : ℕ, ∃ F : Fin k → HubFragment G,
      2*k ≤ Fintype.card W+1 ∧
      Pairwise (fun i j => Disjoint (F i).body (F j).body) ∧
      (⋃ i, (F i).body) = Sym2.map f '' J.edgeSet ∧
      (∀ i, (F i).support ⊆ Set.range f) ∧
      (∀ v, (univ.filter (fun t : Fin k × Bool => (F t.1).outer t.2 = v)).card ≤ 2) ∧
      Function.Injective (fun t : {i // (F i).IsSplit} × Bool => (F t.1.val).near t.1.property t.2) := by
  obtain ⟨k,F,hk,hd,hc,hl,hn⟩ := hub_fragment_partition J
  let M : Fin k → HubFragment G := fun i => (F i).map f hf
  refine ⟨k,M,hk,?_,?_,?_,?_,?_⟩
  · intro i j hij
    simp only [M,HubFragment.map_body]
    exact (Set.disjoint_image_iff (Sym2.map.injective hf)).mpr (hd hij)
  · simp only [M,HubFragment.map_body,←Set.image_iUnion,hc]
  · intro i
    rw [show (M i).support = f '' (F i).support from (F i).map_support f hf]
    exact Set.image_subset_range _ _
  · intro v
    by_cases hv : v ∈ Set.range f
    · obtain ⟨w,rfl⟩ := hv
      simpa only [M,HubFragment.map_outer,hf.eq_iff] using hl w
    · have he : univ.filter (fun t : Fin k × Bool => (M t.1).outer t.2 = v) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        have hh := (mem_filter.mp ht).2
        exact hv ⟨(F t.1).outer t.2,by simpa only [M,HubFragment.map_outer] using hh⟩
      rw [he,card_empty]
      omega
  · rintro ⟨i,b⟩ ⟨j,c⟩ he
    let ii : {i // (F i).IsSplit} := ⟨i.val,((F i).map_isSplit f hf).mp i.property⟩
    let jj : {i // (F i).IsSplit} := ⟨j.val,((F j).map_isSplit f hf).mp j.property⟩
    have hroot : (F ii.val).near ii.property b = (F jj.val).near jj.property c := by
      apply hf
      simpa only [M,HubFragment.map_near] using he
    have ht := hn (a₁ := (ii,b)) (a₂ := (jj,c)) hroot
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun t => t.1.val) ht)
    · simpa only using (congrArg (fun t : {i // (F i).IsSplit} × Bool => t.2) ht)

end
end Cycle12
