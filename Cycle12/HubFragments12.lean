import Cycle12.HubFramePorts12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai OAI.ErdosGallai.Lovasz
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

inductive HubFragment (G : SimpleGraph V) where
  | path (P : SimplePathPiece G)
  | split (L R : SimplePathPiece G) (disjoint : L.walk.support.Disjoint R.walk.support)

namespace HubFragment

def outer : HubFragment G → Bool → V
  | .path P,b => if b then P.finish else P.start
  | .split L R _,b => if b then R.finish else L.finish

def body : HubFragment G → Set (Sym2 V)
  | .path P => P.walk.edgeSet
  | .split L R _ => L.walk.edgeSet ∪ R.walk.edgeSet

def support : HubFragment G → Set V
  | .path P => {v | v ∈ P.walk.support}
  | .split L R _ => {v | v ∈ L.walk.support ∨ v ∈ R.walk.support}

def IsSplit : HubFragment G → Prop
  | .path _ => False
  | .split _ _ _ => True

def near : (F : HubFragment G) → F.IsSplit → Bool → V
  | .split L R _,_,b => if b then R.start else L.start

lemma outer_mem_support (F : HubFragment G) (b : Bool) : F.outer b ∈ F.support := by
  cases F with
  | path P => cases b <;> first | exact P.walk.start_mem_support | exact P.walk.end_mem_support
  | split L R hd =>
    cases b
    · exact Or.inl L.walk.end_mem_support
    · exact Or.inr R.walk.end_mem_support

lemma near_mem_support (F : HubFragment G) (h : F.IsSplit) (b : Bool) : F.near h b ∈ F.support := by
  cases F with
  | path P => exact h.elim
  | split L R hd =>
    cases b
    · exact Or.inl L.walk.start_mem_support
    · exact Or.inr R.walk.start_mem_support

lemma endpoints_mem_support (F : HubFragment G) {x y : V} (he : s(x,y) ∈ F.body) :
    x ∈ F.support ∧ y ∈ F.support := by
  cases F with
  | path P => exact ⟨P.walk.fst_mem_support_of_mem_edges he,P.walk.snd_mem_support_of_mem_edges he⟩
  | split L R hd =>
    rcases he with he | he
    · exact ⟨Or.inl (L.walk.fst_mem_support_of_mem_edges he),Or.inl (L.walk.snd_mem_support_of_mem_edges he)⟩
    · exact ⟨Or.inr (R.walk.fst_mem_support_of_mem_edges he),Or.inr (R.walk.snd_mem_support_of_mem_edges he)⟩

def map (f : G →g H) (hf : Function.Injective f) : HubFragment G → HubFragment H
  | .path P => .path ⟨f P.start,f P.finish,P.walk.map f,P.isPath.map hf⟩
  | .split L R hd => .split
    ⟨f L.start,f L.finish,L.walk.map f,L.isPath.map hf⟩
    ⟨f R.start,f R.finish,R.walk.map f,R.isPath.map hf⟩ (by
      rw [Walk.support_map,Walk.support_map]
      intro v hv hw
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hw
      exact hd hx (hf hxy ▸ hy))

@[simp] lemma map_outer (F : HubFragment G) (f : G →g H) (hf : Function.Injective f) (b : Bool) :
    (F.map f hf).outer b = f (F.outer b) := by cases F <;> cases b <;> rfl

@[simp] lemma map_body (F : HubFragment G) (f : G →g H) (hf : Function.Injective f) :
    (F.map f hf).body = Sym2.map f '' F.body := by
  cases F <;> simp only [map,body,Walk.edgeSet_map,Set.image_union]

@[simp] lemma map_support (F : HubFragment G) (f : G →g H) (hf : Function.Injective f) :
    (F.map f hf).support = f '' F.support := by
  cases F <;> ext v <;> simp only [map,support,Set.mem_ofPred_eq,Walk.support_map,List.mem_map,Set.mem_image]
  constructor
  · rintro (⟨x,hx,hv⟩ | ⟨x,hx,hv⟩)
    · exact ⟨x,Or.inl hx,hv⟩
    · exact ⟨x,Or.inr hx,hv⟩
  · rintro ⟨x,hx,hv⟩
    exact hx.elim (fun h => Or.inl ⟨x,h,hv⟩) (fun h => Or.inr ⟨x,h,hv⟩)

@[simp] lemma map_isSplit (F : HubFragment G) (f : G →g H) (hf : Function.Injective f) :
    (F.map f hf).IsSplit ↔ F.IsSplit := by cases F <;> rfl

@[simp] lemma map_near (F : HubFragment G) (f : G →g H) (hf : Function.Injective f)
    (h : (F.map f hf).IsSplit) (b : Bool) :
    (F.map f hf).near h b = f (F.near ((F.map_isSplit f hf).mp h) b) := by
  cases F with
  | path P => exact h.elim
  | split L R hd => cases b <;> rfl

end HubFragment

variable [Fintype V]

def frameFragment (G : SimpleGraph V) : Frame (evenAugmentation G) none → HubFragment G
  | .away P h => .path (projectOldPath ⟨_,_,P.walk,P.isPath⟩ h)
  | .tip A => .path (projectOldPath ⟨_,_,A.walk,A.isPath⟩ A.avoids)
  | .through A B hd => .split
      (projectOldPath ⟨_,_,A.walk,A.isPath⟩ A.avoids)
      (projectOldPath ⟨_,_,B.walk,B.isPath⟩ B.avoids) (by
        intro v hv hw
        apply hd (a := some v)
        · rw [←projectOldPath_support ⟨_,_,A.walk,A.isPath⟩ A.avoids]
          exact List.mem_map.mpr ⟨v,hv,rfl⟩
        · rw [←projectOldPath_support ⟨_,_,B.walk,B.isPath⟩ B.avoids]
          exact List.mem_map.mpr ⟨v,hw,rfl⟩)

@[simp] theorem frameFragment_outer (G : SimpleGraph V) (F : Frame (evenAugmentation G) none) (b : Bool) :
    some ((frameFragment G F).outer b) = HubFrames.outer F b := by
  cases F <;> cases b <;> first | exact projectOldPath_start _ _ | exact projectOldPath_finish _ _

@[simp] theorem frameFragment_isSplit (G : SimpleGraph V) (F : Frame (evenAugmentation G) none) :
    (frameFragment G F).IsSplit ↔ HubFrames.IsThrough F := by cases F <;> rfl

@[simp] theorem frameFragment_near (G : SimpleGraph V) (F : Frame (evenAugmentation G) none)
    (h : (frameFragment G F).IsSplit) (b : Bool) :
    some ((frameFragment G F).near h b) =
      HubFrames.near F ((frameFragment_isSplit G F).mp h) b := by
  cases F with
  | away P hp => exact h.elim
  | tip A => exact h.elim
  | through A B hd => cases b <;> exact projectOldPath_start _ _

/-- Exact edge ledger when deleting the hub: every old edge, and only an
old edge of the original path, belongs to the projected fragment. -/
theorem frameFragment_body (G : SimpleGraph V) (F : Frame (evenAugmentation G) none) (e : Sym2 V) :
    e ∈ (frameFragment G F).body ↔ Sym2.map some e ∈ F.path.walk.edgeSet := by
  have hmem : ∀ (P : SimplePathPiece (evenAugmentation G)) (h : none ∉ P.walk.support),
      e ∈ (projectOldPath P h).walk.edgeSet ↔ Sym2.map some e ∈ P.walk.edgeSet := by
    intro P h
    rw [←projectOldPath_edges P h]
    constructor
    · intro he; exact ⟨e,he,rfl⟩
    · rintro ⟨a,ha,he⟩
      exact Sym2.map.injective (Option.some_injective V) he ▸ ha
  have hstar : ∀ x : Option V, Sym2.map some e ≠ s(none,x) := by
    intro x he
    have hh : none ∈ Sym2.map some e := he ▸ (by simp)
    induction e using Sym2.inductionOn with
    | _ a b => simpa using hh
  cases F with
  | away P hp => exact hmem _ hp
  | tip A =>
    change e ∈ (projectOldPath ⟨_,_,A.walk,A.isPath⟩ A.avoids).walk.edgeSet ↔
      Sym2.map some e ∈ (Walk.cons A.adj A.walk).edgeSet
    rw [Walk.edgeSet_cons]
    simp only [Set.mem_insert_iff,hstar,false_or]
    exact hmem _ A.avoids
  | through A B hd =>
    change (e ∈ (projectOldPath ⟨_,_,A.walk,A.isPath⟩ A.avoids).walk.edgeSet ∨
      e ∈ (projectOldPath ⟨_,_,B.walk,B.isPath⟩ B.avoids).walk.edgeSet) ↔
      Sym2.map some e ∈ (A.join B hd).walk.edgeSet
    rw [Arm.join_edges]
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,hstar,or_false]
    exact or_congr (hmem _ A.avoids) (hmem _ B.avoids)

end
end Cycle12
