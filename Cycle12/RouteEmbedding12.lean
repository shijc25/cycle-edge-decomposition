import Cycle12.GroupedDemandData12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I T : Type} [Fintype V] [Fintype W] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq W] [DecidableEq I] [DecidableEq T]

theorem routeInterior_map_injective {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {a b : V} (p : G.Walk a b) :
    routeInterior (p.map f)=(routeInterior p).image f := by
  ext w
  simp only [mem_image,mem_routeInterior_iff,Walk.support_map,List.mem_map]
  constructor
  · rintro ⟨⟨v,hv,rfl⟩,ha,hb⟩
    exact ⟨v,⟨hv,fun he => ha (congrArg f he),fun he => hb (congrArg f he)⟩,rfl⟩
  · rintro ⟨v,⟨hv,ha,hb⟩,rfl⟩
    exact ⟨⟨v,hv,rfl⟩,fun he => ha (hf he),fun he => hb (hf he)⟩

theorem groupPorts_image (f : V → W) (group : I → T) (a b : I → V) (t : T) :
    groupPorts group (fun i => f (a i)) (fun i => f (b i)) t=
      (groupPorts group a b t).image f := by
  simp only [groupPorts,Finset.image_union,Finset.image_image,Function.comp_def]

theorem endpointLoad_map_embedding (f : V ↪ W) (a b : I → V) (v : V) :
    endpointLoad (fun i => f (a i)) (fun i => f (b i)) (f v)=endpointLoad a b v := by
  simp only [endpointLoad,f.injective.eq_iff]

theorem disjoint_finset_image {S T : Finset V} (f : V → W) (hf : Function.Injective f)
    (hd : Disjoint S T) : Disjoint (S.image f) (T.image f) := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  obtain ⟨v,hv,he⟩ := mem_image.mp hw
  obtain ⟨u,hu,he'⟩ := mem_image.mp hw'
  have h := hf (he.trans he'.symm)
  subst u
  exact Finset.disjoint_left.mp hd hv hu

theorem disjoint_set_image {S T : Set V} (f : V → W) (hf : Function.Injective f)
    (hd : Disjoint S T) : Disjoint (f '' S) (f '' T) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨v,hv,he⟩ ⟨u,hu,he'⟩
  have h := hf (he.trans he'.symm)
  subst u
  exact Set.disjoint_left.mp hd hv hu

end
end Cycle12
