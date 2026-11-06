import Cycle12.FanApex

namespace Cycle12
open SimpleGraph
variable {V : Type}

def originalFanVertex : ({none}ᶜ : Set (Option V)) → V
  | ⟨none,h⟩ => False.elim (h rfl)
  | ⟨some v,_⟩ => v

theorem originalFanVertex_injective : Function.Injective (originalFanVertex (V:=V)) := by
  rintro ⟨u,hu⟩ ⟨v,hv⟩ he
  cases u with
  | none => exact (hu rfl).elim
  | some u =>
    cases v with
    | none => exact (hv rfl).elim
    | some v =>
      change u=v at he
      subst v
      rfl

def fanOriginalHom (G : SimpleGraph V) (S : Finset V) :
    (fanApex G S).induce ({none}ᶜ : Set (Option V)) →g G where
  toFun := originalFanVertex
  map_rel' := by
    rintro ⟨u,hu⟩ ⟨v,hv⟩ he
    cases u with
    | none => exact (hu rfl).elim
    | some u =>
      cases v with
      | none => exact (hv rfl).elim
      | some v => exact he

theorem fan_original_comp (G : SimpleGraph V) (S : Finset V) :
    (fanApexHom G S).comp (fanOriginalHom G S)=
      (SimpleGraph.Embedding.induce (G:=fanApex G S) ({none}ᶜ : Set (Option V))).toHom := by
  apply DFunLike.ext
  rintro ⟨u,hu⟩
  cases u with
  | none => exact (hu rfl).elim
  | some u => rfl

/-- A path in the apex graph that avoids the apex is a path of the
original graph, with exactly the same length and vertex support. -/
theorem fan_path_remove_apex (G : SimpleGraph V) (S : Finset V) {x b : V}
    (p : (fanApex G S).Walk (some x) (some b)) (hp : p.IsPath)
    (havoid : none ∉ p.support) :
    ∃ q : G.Walk x b, q.IsPath ∧
      (∀ z, z∈q.support ↔ some z∈p.support) ∧ q.length=p.length := by
  have hin : ∀ z∈p.support, z∈({none}ᶜ : Set (Option V)) := by
    intro z hz he
    exact havoid (he ▸ hz)
  let r := p.induce ({none}ᶜ : Set (Option V)) hin
  let q : G.Walk x b := r.map (fanOriginalHom G S)
  have hback := Walk.map_induce p hin
  have hr : r.IsPath := Walk.IsPath.of_map (by rw [hback]; exact hp)
  have hq : q.IsPath := hr.map originalFanVertex_injective
  have hs₀ := congrArg Walk.support hback
  erw [Walk.support_map] at hs₀
  have hs : q.support.map some=p.support := by
    calc
      _=(r.support.map (fanOriginalHom G S)).map some :=
        congrArg (List.map some) (Walk.support_map (fanOriginalHom G S) r)
      _=r.support.map Subtype.val := by
        rw [List.map_map]
        apply congrArg (fun f => r.support.map f)
        funext z
        have hh := DFunLike.congr_fun (fan_original_comp G S) z
        exact hh
      _=p.support := hs₀
  have hl₀ := congrArg Walk.length hback
  erw [Walk.length_map] at hl₀
  have hl : q.length=p.length := (Walk.length_map (fanOriginalHom G S) r).trans hl₀
  refine ⟨q,hq,?_,hl⟩
  intro z
  erw [← hs]
  change z∈q.support ↔ some z∈q.support.map some
  simp

theorem fan_apex_path_hits (G : SimpleGraph V) (S : Finset V) {x : V}
    (p : (fanApex G S).Walk (some x) none) :
    ∃ y∈S, some y∈p.support := by
  obtain ⟨w,hw,r,he⟩ := Walk.exists_eq_cons_of_ne (by simp : (none:Option V)≠some x) p.reverse
  cases w with
  | none => exact hw.elim
  | some y =>
    have hy : y∈S := hw
    refine ⟨y,hy,?_⟩
    have hm : some y∈p.reverse.support := by rw [he]; simp
    simpa only [Walk.support_reverse,List.mem_reverse] using hm

end Cycle12
