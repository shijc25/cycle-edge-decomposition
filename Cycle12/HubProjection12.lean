import Cycle12.EndpointParity12
import Cycle12.ReservoirArmSplice12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

def oldVertex : {x : Option V // x ≠ none} → V
  | ⟨some v,_⟩ => v
  | ⟨none,h⟩ => False.elim (h rfl)

@[simp] theorem some_oldVertex (x : {x : Option V // x ≠ none}) :
    some (oldVertex x) = x.val := by
  rcases x with ⟨x,h⟩
  cases x with
  | none => exact (h rfl).elim
  | some v => rfl

def oldHom (G : SimpleGraph V) :
    (evenAugmentation G).induce {x | x ≠ none} →g G where
  toFun := oldVertex
  map_rel' := by
    intro x y h
    have hx := some_oldVertex x
    have hy := some_oldVertex y
    change (evenAugmentation G).Adj x.val y.val at h
    rw [←hx,←hy] at h
    exact h

theorem oldVertex_injective : Function.Injective (oldVertex (V := V)) := by
  intro x y h
  apply Subtype.ext
  rw [←some_oldVertex x,←some_oldVertex y,h]

/-- Remove the virtual vertex from a path which avoids it. No positivity
assumption is made, so an isolated arm is retained faithfully. -/
def projectOldPath {G : SimpleGraph V} (P : SimplePathPiece (evenAugmentation G))
    (h : none ∉ P.walk.support) : SimplePathPiece G := by
  let hw : ∀ x ∈ P.walk.support, x ∈ ({x | x ≠ none} : Set (Option V)) := by
    intro x hx he
    exact h (he ▸ hx)
  let q := P.walk.induce {x | x ≠ none} hw
  refine ⟨oldVertex ⟨P.start,hw _ P.walk.start_mem_support⟩,
    oldVertex ⟨P.finish,hw _ P.walk.end_mem_support⟩,q.map (oldHom G),?_⟩
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    apply List.Nodup.of_map Subtype.val
    simpa only [q,Walk.support_induce,List.attachWith_map_subtype_val] using P.isPath.support_nodup
  exact hq.map oldVertex_injective

@[simp] theorem projectOldPath_start {G : SimpleGraph V}
    (P : SimplePathPiece (evenAugmentation G)) (h : none ∉ P.walk.support) :
    some (projectOldPath P h).start = P.start := some_oldVertex _

@[simp] theorem projectOldPath_finish {G : SimpleGraph V}
    (P : SimplePathPiece (evenAugmentation G)) (h : none ∉ P.walk.support) :
    some (projectOldPath P h).finish = P.finish := some_oldVertex _

theorem projectOldPath_support {G : SimpleGraph V}
    (P : SimplePathPiece (evenAugmentation G)) (h : none ∉ P.walk.support) :
    (projectOldPath P h).walk.support.map some = P.walk.support := by
  change ((P.walk.induce _ _).map (oldHom G)).support.map some = _
  rw [Walk.support_map,List.map_map]
  have he : (some ∘ (oldHom G)) = (Subtype.val : {x : Option V // x ≠ none} → Option V) := by
    funext x
    exact some_oldVertex x
  rw [he]
  rw [Walk.support_induce]
  exact List.attachWith_map_subtype_val _

theorem projectOldPath_edges {G : SimpleGraph V}
    (P : SimplePathPiece (evenAugmentation G)) (h : none ∉ P.walk.support) :
    Sym2.map some '' (projectOldPath P h).walk.edgeSet = P.walk.edgeSet := by
  change Sym2.map some '' ((P.walk.induce _ _).map (oldHom G)).edgeSet = _
  rw [Walk.edgeSet_map,Set.image_image]
  have he : (Sym2.map some ∘ Sym2.map (oldHom G)) =
      Sym2.map (Subtype.val : {x : Option V // x ≠ none} → Option V) := by
    funext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [Function.comp_def,oldHom]
  change (Sym2.map some ∘ Sym2.map (oldHom G)) '' (P.walk.induce _ _).edgeSet = _
  rw [he]
  have hh := congrArg Walk.edgeSet (Walk.map_induce P.walk
    (s := {x | x ≠ none}) (fun x hx he => h (he ▸ hx)))
  rw [Walk.edgeSet_map] at hh
  change Sym2.map (Subtype.val : {x : Option V // x ≠ none} → Option V) ''
    (P.walk.induce _ _).edgeSet = _ at hh
  exact hh

end
end Cycle12
