import Cycle12.HubProjection12

namespace Cycle12.HubFrames
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai OAI.ErdosGallai.Lovasz
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} {G : SimpleGraph V} {hub : V}

def endpoint (F : Frame G hub) (b : Bool) : V := if b then F.path.finish else F.path.start

def outer (F : Frame G hub) : Bool → V
  | b => match F with
    | .away P _ => if b then P.finish else P.start
    | .tip A => if b then A.far else A.near
    | .through A B _ => if b then B.far else A.far

def tipPort (F : Frame G hub) (b : Bool) : Prop :=
  match F with | .tip _ => b = false | _ => False

def IsThrough : Frame G hub → Prop
  | .through _ _ _ => True
  | _ => False

def near : (F : Frame G hub) → IsThrough F → Bool → V
  | .through A B _, _, b => if b then B.near else A.near

lemma outer_ne_hub (F : Frame G hub) (b : Bool) : outer F b ≠ hub := by
  cases F with
  | away P hp =>
    cases b
    · intro h; exact hp (h ▸ P.walk.start_mem_support)
    · intro h; exact hp (h ▸ P.walk.end_mem_support)
  | tip A =>
    cases b
    · exact A.adj.ne.symm
    · exact A.far_ne_center
  | through A B hd => cases b <;> exact Arm.far_ne_center _

lemma outer_eq_endpoint (F : Frame G hub) (b : Bool) (h : ¬tipPort F b) :
    outer F b = endpoint F b := by
  cases F <;> cases b <;> simp_all [outer,endpoint,tipPort,Frame.path,Arm.tip,Arm.join]

lemma tipPort_edge (F : Frame G hub) (b : Bool) (h : tipPort F b) :
    s(hub,outer F b) ∈ F.path.walk.edgeSet := by
  cases F <;> cases b <;> simp_all [tipPort,outer,Frame.path,Arm.tip,Walk.edgeSet_cons]

lemma tipPort_unique (F : Frame G hub) {b c : Bool} (hb : tipPort F b) (hc : tipPort F c) : b = c := by
  cases F <;> simp_all [tipPort]

lemma near_edge (F : Frame G hub) (h : IsThrough F) (b : Bool) :
    s(hub,near F h b) ∈ F.path.walk.edgeSet := by
  cases F with
  | away P hp => exact h.elim
  | tip A => exact h.elim
  | through A B hd =>
    cases b <;> simp [near,Frame.path,Arm.join_edges]

lemma near_injective (F : Frame G hub) (h : IsThrough F) : Function.Injective (near F h) := by
  cases F with
  | away P hp => exact h.elim
  | tip A => exact h.elim
  | through A B hd =>
    intro b c he
    have hn := Arm.near_ne A B hd
    cases b <;> cases c <;> simp_all [near]

lemma near_ne_hub (F : Frame G hub) (h : IsThrough F) (b : Bool) : near F h b ≠ hub := by
  cases F with
  | away P hp => exact h.elim
  | tip A => exact h.elim
  | through A B hd =>
    cases b
    · exact A.adj.ne.symm
    · exact B.adj.ne.symm

/-- Reorienting the Lovász paths around the hub preserves both their edge
partition and injectivity of all original endpoint occurrences. -/
theorem frame_partition [Fintype V] (P : DistinctEndpointPaths G) (hub : V) :
    ∃ F : Fin P.count → Frame G hub,
      Pairwise (fun i j => Disjoint (F i).path.walk.edgeSet (F j).path.walk.edgeSet) ∧
      (⋃ i, (F i).path.walk.edgeSet) = G.edgeSet ∧
      Function.Injective (fun k : Fin P.count × Bool => endpoint (F k.1) k.2) := by
  have hex : ∀ i, ∃ F : Frame G hub, F.path.walk.edgeSet = (P.paths i).walk.edgeSet ∧
      ∀ v, (F.path.start = v ∨ F.path.finish = v) ↔
        ((P.paths i).start = v ∨ (P.paths i).finish = v) := by
    intro i
    exact PathPiece.exists_frame ⟨_,_,(P.paths i).walk,(P.paths i).isPath,(P.paths i).positive⟩ hub
  choose F he hend using hex
  refine ⟨F,by simpa only [he] using P.disjoint,by simpa only [he] using P.cover,?_⟩
  have hm : ∀ i b, (F i).path.start = endpoint (F i) b ∨ (F i).path.finish = endpoint (F i) b := by
    intro i b; cases b <;> simp [endpoint]
  have horig : ∀ i b, ∃ c : Bool,
      (if c then (P.paths i).start else (P.paths i).finish) = endpoint (F i) b := by
    intro i b
    rcases (hend i _).mp (hm i b) with hs | ht
    · exact ⟨true,hs⟩
    · exact ⟨false,ht⟩
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  obtain ⟨bi,hbi⟩ := horig i b
  obtain ⟨cj,hcj⟩ := horig j c
  have hij : i = j := congrArg Prod.fst (P.endpoint_injective (a₁ := (i,bi)) (a₂ := (j,cj)) (hbi.trans (h.trans hcj.symm)))
  subst j
  have hbc : b = c := by
    have hn := (F i).path.ends_ne
    cases b <;> cases c <;> simp_all [endpoint]
  subst c
  rfl

/-- Through-hub demands have distinct roots, because each hub edge was
used by exactly one original path. -/
theorem through_roots_injective (F : I → Frame G hub)
    (hd : Pairwise (fun i j => Disjoint (F i).path.walk.edgeSet (F j).path.walk.edgeSet)) :
    Function.Injective (fun k : {i // IsThrough (F i)} × Bool => near (F k.1.val) k.1.property k.2) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  change near (F i.val) i.property b = near (F j.val) j.property c at he
  have hij : i = j := by
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (near_edge (F i) i.property b)
      (he.symm ▸ near_edge (F j) j.property c)
  subst j
  have hbc : b = c := near_injective (F i) i.property he
  subst c
  rfl

/-- One old endpoint and, possibly, one deleted hub edge are the only
sources of endpoint load after the hub replacement. -/
theorem outer_load [Fintype I] (F : I → Frame G hub)
    (hd : Pairwise (fun i j => Disjoint (F i).path.walk.edgeSet (F j).path.walk.edgeSet))
    (hi : Function.Injective (fun k : I × Bool => endpoint (F k.1) k.2)) (v : V) :
    (univ.filter (fun k : I × Bool => outer (F k.1) k.2 = v)).card ≤ 2 := by
  let A := univ.filter (fun k : I × Bool => outer (F k.1) k.2 = v ∧ tipPort (F k.1) k.2)
  let B := univ.filter (fun k : I × Bool => outer (F k.1) k.2 = v ∧ ¬tipPort (F k.1) k.2)
  have ha : A.card ≤ 1 := by
    apply card_le_one.mpr
    intro k hk l hl
    obtain ⟨hk,hkt⟩ := (mem_filter.mp hk).2
    obtain ⟨hl,hlt⟩ := (mem_filter.mp hl).2
    have hkl : k.1 = l.1 := by
      by_contra hn
      have hke := tipPort_edge (F k.1) k.2 hkt
      have hle := tipPort_edge (F l.1) l.2 hlt
      rw [hk] at hke
      rw [hl] at hle
      exact Set.disjoint_left.mp (hd hn) hke hle
    apply Prod.ext hkl
    exact tipPort_unique (F l.1) (hkl ▸ hkt) hlt
  have hb : B.card ≤ 1 := by
    apply card_le_one.mpr
    intro k hk l hl
    obtain ⟨hk,hkt⟩ := (mem_filter.mp hk).2
    obtain ⟨hl,hlt⟩ := (mem_filter.mp hl).2
    apply hi
    change endpoint (F k.1) k.2 = endpoint (F l.1) l.2
    rw [←outer_eq_endpoint (F k.1) k.2 hkt,←outer_eq_endpoint (F l.1) l.2 hlt,hk,hl]
  have he : univ.filter (fun k : I × Bool => outer (F k.1) k.2 = v) = A ∪ B := by
    ext k
    simp only [A,B,mem_filter,mem_univ,true_and,mem_union]
    tauto
  rw [he]
  exact (card_union_le _ _).trans (by omega)

end
end Cycle12.HubFrames
