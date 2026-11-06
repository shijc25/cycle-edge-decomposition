import Cycle12.Foundations.WeightedPacking

/-! Copies of a rooted graph identified at one vertex. A simple cycle lies
entirely in one copy. No numerical decomposition bound is assumed here. -/
namespace Cycle13
namespace Wedge
open SimpleGraph
variable {I W : Type}

def forget : Option (I × W) → Option W := Option.map Prod.snd

def compatible : Option (I × W) → Option (I × W) → Prop
  | some x, some y => x.1 = y.1
  | _, _ => True

def graph (G : SimpleGraph (Option W)) (I : Type) : SimpleGraph (Option (I × W)) where
  Adj x y := G.Adj (forget x) (forget y) ∧ compatible x y
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    cases x <;> cases y <;> simp_all [compatible]⟩
  loopless := ⟨by
    intro x h
    exact G.irrefl h.1⟩

def embed (i : I) : Option W → Option (I × W) := Option.map (fun w => (i, w))

@[simp] theorem forget_embed (i : I) (x : Option W) : forget (embed i x) = x := by
  cases x <;> rfl

theorem embed_injective (i : I) : Function.Injective (embed (W := W) i) :=
  Function.LeftInverse.injective (forget_embed i)

def embedHom (G : SimpleGraph (Option W)) (i : I) : G →g graph G I where
  toFun := embed i
  map_rel' := by
    intro x y h
    refine ⟨by simpa using h, ?_⟩
    cases x <;> cases y <;> simp [embed, compatible]

def forgetHom (G : SimpleGraph (Option W)) : graph G I →g G where
  toFun := forget
  map_rel' := fun h => h.1

def branch (i : I) : Set (Option (I × W)) :=
  {x | match x with | none => True | some y => y.1 = i}

@[simp] theorem none_mem_branch (i : I) : (none : Option (I × W)) ∈ branch i := trivial

@[simp] theorem some_mem_branch (i j : I) (w : W) :
    some (j, w) ∈ branch i ↔ j = i := Iff.rfl

@[simp] theorem embed_mem_branch (i : I) (x : Option W) : embed i x ∈ branch i := by
  cases x <;> simp [embed]

theorem embed_forget {i : I} {x : Option (I × W)} (hx : x ∈ branch i) :
    embed i (forget x) = x := by
  cases x with
  | none => rfl
  | some x =>
    rcases x with ⟨j,w⟩
    change j = i at hx
    subst j
    rfl

theorem forget_injOn_branch (i : I) : Set.InjOn (forget (I := I) (W := W)) (branch i) := by
  intro x hx y hy h
  rw [← embed_forget hx, ← embed_forget hy, h]

theorem adj_propagates_branch {G : SimpleGraph (Option W)} {i : I}
    {x y : Option (I × W)} (hxy : (graph G I).Adj x y)
    (hx : x ∈ branch i) (hx0 : x ≠ none) : y ∈ branch i := by
  cases x with
  | none => exact (hx0 rfl).elim
  | some x =>
    cases y with
    | none => trivial
    | some y =>
      change x.1 = i at hx
      change y.1 = i
      exact hxy.2.symm.trans hx

theorem walk_avoiding_root_in_branch {G : SimpleGraph (Option W)} {i : I}
    {x y : Option (I × W)} (p : (graph G I).Walk x y)
    (hx : x ∈ branch i) (havoid : none ∉ p.support) :
    ∀ z ∈ p.support, z ∈ branch i := by
  induction p with
  | nil => simpa using hx
  | @cons x y z h p ih =>
    have hx0 : x ≠ none := by
      intro he
      exact havoid (by simp [he])
    have hy := adj_propagates_branch h hx hx0
    have hp : none ∉ p.support := fun hn => havoid (by simp [hn])
    intro w hw
    simp only [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hx
    · exact ih hy hp w hw

theorem path_to_root_in_branch {G : SimpleGraph (Option W)} {i : I}
    {x y : Option (I × W)} (p : (graph G I).Walk x y)
    (hp : p.IsPath) (hy : y = none) (hx : x ∈ branch i) :
    ∀ z ∈ p.support, z ∈ branch i := by
  induction p with
  | nil => simpa using hx
  | @cons x y z h p ih =>
    have hx0 : x ≠ none := by
      intro he
      have hnil := hp.nil_iff_eq.mpr (he.trans hy.symm)
      exact Walk.not_nil_cons hnil
    have hy := adj_propagates_branch h hx hx0
    have hp' : p.IsPath := by simpa using hp.tail
    intro w hw
    simp only [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hx
    · exact ih hp' ‹z = none› hy w hw

theorem cycle_at_root_in_branch {G : SimpleGraph (Option W)}
    (p : (graph G I).Walk none none) (hp : p.IsCycle) :
    ∃ i : I, ∀ x ∈ p.support, x ∈ branch i := by
  cases p with
  | nil => exact (hp.not_nil Walk.Nil.nil).elim
  | @cons _ y _ h p =>
    cases y with
    | none => exact ((graph G I).irrefl h).elim
    | some y =>
      rcases y with ⟨i,w⟩
      refine ⟨i, ?_⟩
      have ht := path_to_root_in_branch p (by simpa using hp.isPath_tail) rfl
        (i := i) (by simp)
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · trivial
      · exact ht x hx

/-- A simple cycle cannot traverse two copies of the one-vertex wedge. -/
theorem cycle_in_branch {G : SimpleGraph (Option W)} {v : Option (I × W)}
    (p : (graph G I).Walk v v) (hp : p.IsCycle) :
    ∃ i : I, ∀ x ∈ p.support, x ∈ branch i := by
  classical
  by_cases hroot : none ∈ p.support
  · obtain ⟨i, hi⟩ := cycle_at_root_in_branch (p.rotate none hroot) (hp.rotate _)
    exact ⟨i, fun x hx => hi x ((p.mem_support_rotate_iff none hroot).mpr hx)⟩
  · cases v with
    | none => exact (hroot p.start_mem_support).elim
    | some v =>
      exact ⟨v.1, walk_avoiding_root_in_branch p (by simp [branch]) hroot⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem map_cycle_to_base {G : SimpleGraph (Option W)} {v : Option (I × W)}
    (p : (graph G I).Walk v v) (hp : p.IsCycle) :
    (p.map (forgetHom G)).IsCycle := by
  obtain ⟨i, hi⟩ := cycle_in_branch p hp
  let q := p.induce (branch i) hi
  let f := (forgetHom G).comp (SimpleGraph.Embedding.induce (branch i)).toHom
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (forget_injOn_branch i x.2 y.2 hxy)
  have hq : q.IsCycle := Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    (by simpa [q] using hp)
  have hm := hq.map hf
  simpa [f, q, ← Walk.map_map, forgetHom] using hm

theorem copy_edge_iff (G : SimpleGraph (Option W)) (i : I)
    (x y : Option (I × W)) :
    s(x,y) ∈ Sym2.map (embedHom G i) '' G.edgeSet ↔
      (graph G I).Adj x y ∧ x ∈ branch i ∧ y ∈ branch i := by
  constructor
  · rintro ⟨e, he, heq⟩
    induction e using Sym2.ind with
    | _ a b =>
      have hadj := (embedHom G i).map_adj he
      have ha := embed_mem_branch i a
      have hb := embed_mem_branch i b
      change s(embed i a, embed i b) = s(x,y) at heq
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hadj, ha, hb⟩
      · exact ⟨hadj.symm, hb, ha⟩
  · rintro ⟨hxy, hx, hy⟩
    refine ⟨s(forget x, forget y), hxy.1, ?_⟩
    change s(embed i (forget x), embed i (forget y)) = s(x,y)
    rw [embed_forget hx, embed_forget hy]

theorem copy_edges_disjoint (G : SimpleGraph (Option W)) :
    Pairwise (fun i j : I => Disjoint (Sym2.map (embedHom G i) '' G.edgeSet)
      (Sym2.map (embedHom G j) '' G.edgeSet)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hadj, hxi, hyi⟩ := (copy_edge_iff G i x y).mp hei
    obtain ⟨_, hxj, hyj⟩ := (copy_edge_iff G j x y).mp hej
    cases x with
    | some x => exact hij (hxi.symm.trans hxj)
    | none =>
      cases y with
      | none => exact (graph G I).irrefl hadj
      | some y => exact hij (hyi.symm.trans hyj)

theorem copy_edges_cover (G : SimpleGraph (Option W)) :
    (⋃ i : I, Sym2.map (embedHom G i) '' G.edgeSet) = (graph G I).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      exact (copy_edge_iff G i x y).mp hi |>.1
    · intro hxy
      apply Set.mem_iUnion.mpr
      cases x with
      | some x =>
        refine ⟨x.1, (copy_edge_iff G x.1 _ _).mpr ⟨hxy, rfl, ?_⟩⟩
        exact adj_propagates_branch hxy rfl (by simp)
      | none =>
        cases y with
        | none => exact ((graph G I).irrefl hxy).elim
        | some y => exact ⟨y.1, (copy_edge_iff G y.1 _ _).mpr ⟨hxy, trivial, rfl⟩⟩

theorem cycle_lifts_from_copy (G : SimpleGraph (Option W))
    (v : Option (I × W)) (p : (graph G I).Walk v v) (hp : p.IsCycle) :
    ∃ (i : I) (u : Option W) (q : G.Walk u u), q.IsCycle ∧
      p.edgeSet = Sym2.map (embedHom G i) '' q.edgeSet := by
  obtain ⟨i, hi⟩ := cycle_in_branch p hp
  refine ⟨i, (forgetHom G) v, p.map (forgetHom G), map_cycle_to_base p hp, ?_⟩
  rw [Walk.edgeSet_map]
  ext e
  constructor
  · intro he
    refine ⟨Sym2.map (forgetHom G) e, ⟨e, he, rfl⟩, ?_⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hx := hi x (p.fst_mem_support_of_mem_edges he)
      have hy := hi y (p.snd_mem_support_of_mem_edges he)
      change s(embed i (forget x), embed i (forget y)) = s(x,y)
      rw [embed_forget hx, embed_forget hy]
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    induction d using Sym2.ind with
    | _ x y =>
      have hx := hi x (p.fst_mem_support_of_mem_edges hd)
      have hy := hi y (p.snd_mem_support_of_mem_edges hd)
      change s(embed i (forget x), embed i (forget y)) ∈ p.edgeSet
      rwa [embed_forget hx, embed_forget hy]

end Wedge
end Cycle13
