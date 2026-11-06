import OAI.Combinatorics.CycleDecomposition.DepthFirstSearch

/-! A complete depth-first forest, retaining the discovery paths.  The
balanced DFS state in the upstream proof does not retain this information.
Here every graph edge is proved to join comparable discovery paths. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure NormalDFSForest (G : SimpleGraph V) where
  path : V → List V
  head : ∀ v, (path v).head? = some v
  nodup : ∀ v, (path v).Nodup
  chain : ∀ v, (path v).IsChain G.Adj
  coherent : ∀ v u, u ∈ path v → path u <:+ path v
  comparable : ∀ u v, G.Adj u v → path u <:+ path v ∨ path v <:+ path u

namespace NormalDFSForest
variable {G : SimpleGraph V}

theorem self_mem (F : NormalDFSForest G) (v : V) : v ∈ F.path v := by
  have hh := F.head v
  cases he : F.path v with
  | nil => simp [he] at hh
  | cons a L => simp [he] at hh; simp [he,hh]

theorem nonempty (F : NormalDFSForest G) (v : V) : F.path v ≠ [] := by
  intro h
  have hh := F.head v
  simp [h] at hh

theorem ancestor_iff (F : NormalDFSForest G) (u v : V) :
    u ∈ F.path v ↔ F.path u <:+ F.path v :=
  ⟨F.coherent v u, fun h => h.subset (F.self_mem u)⟩

theorem ancestor_trans (F : NormalDFSForest G) {u v w : V}
    (hu : u ∈ F.path v) (hv : v ∈ F.path w) : u ∈ F.path w :=
  (F.coherent w v hv).subset hu

theorem ancestor_antisymm (F : NormalDFSForest G) {u v : V}
    (hu : u ∈ F.path v) (hv : v ∈ F.path u) : u=v := by
  have h₁ := F.coherent v u hu
  have h₂ := F.coherent u v hv
  have he := h₁.eq_of_length_le h₂.length_le
  have hh := congrArg List.head? he
  simpa only [F.head,Option.some.injEq] using hh

theorem edge_ancestor (F : NormalDFSForest G) {u v : V} (h : G.Adj u v) :
    u ∈ F.path v ∨ v ∈ F.path u :=
  (F.comparable u v h).imp ((F.ancestor_iff u v).mpr) ((F.ancestor_iff v u).mpr)

end NormalDFSForest

private structure RecordedDFS (G : SimpleGraph V) where
  state : OAI.ErdosGallai.Scale.DFSState G
  path : V → List V
  head : ∀ v, v ∉ state.unexplored → (path v).head? = some v
  nodup : ∀ v, v ∉ state.unexplored → (path v).Nodup
  chain : ∀ v, v ∉ state.unexplored → (path v).IsChain G.Adj
  closed : ∀ v, v ∉ state.unexplored → ∀ u ∈ path v, u ∉ state.unexplored
  coherent : ∀ v, v ∉ state.unexplored → ∀ u ∈ path v, path u <:+ path v
  stack_paths : ∀ v L, v::L <:+ state.stack → path v=v::L
  comparable : ∀ u v, u ∉ state.unexplored → v ∉ state.unexplored →
    G.Adj u v → path u <:+ path v ∨ path v <:+ path u

namespace RecordedDFS
variable {G : SimpleGraph V}

private theorem stack_seen (s : RecordedDFS G) {v : V} (hv : v ∈ s.state.stack) :
    v ∉ s.state.unexplored :=
  fun h => Finset.disjoint_left.mp s.state.s_u (List.mem_toFinset.mpr hv) h

private theorem seen_cases (s : RecordedDFS G) {v : V} (hv : v ∉ s.state.unexplored) :
    v ∈ s.state.finished ∨ v ∈ s.state.stack := by
  have h : v ∈ s.state.finished ∪ s.state.stack.toFinset ∪ s.state.unexplored := by
    rw [s.state.cover]
    simp
  simpa only [Finset.mem_union,List.mem_toFinset,or_false,hv] using h

private theorem path_suffix_stack (s : RecordedDFS G) {v : V} (hv : v ∈ s.state.stack) :
    s.path v <:+ s.state.stack := by
  obtain ⟨a,b,he⟩ := List.mem_iff_append.mp hv
  have hs : v::b <:+ s.state.stack := ⟨a,he.symm⟩
  rw [s.stack_paths v b hs]
  exact hs

/-- Discovery, including the restart of a new component. -/
private theorem discover (s : RecordedDFS G) (w : V) (hw : w ∈ s.state.unexplored)
    (hchain : (w::s.state.stack).IsChain G.Adj) :
    ∃ t : RecordedDFS G,
      t.state.unexplored.card+1=s.state.unexplored.card ∧
      t.state.stack.length=s.state.stack.length+1 := by
  let d := s.state
  have hws : w ∉ d.stack := fun h => Finset.disjoint_left.mp d.s_u
    (List.mem_toFinset.mpr h) hw
  have hwf : w ∉ d.finished := fun h => Finset.disjoint_left.mp d.f_u h hw
  let d' : OAI.ErdosGallai.Scale.DFSState G := {
    stack := w::d.stack
    finished := d.finished
    unexplored := d.unexplored.erase w
    nodup := List.nodup_cons.mpr ⟨hws,d.nodup⟩
    chain := hchain
    f_s := by simpa using And.intro hwf d.f_s
    f_u := d.f_u.mono_right (Finset.erase_subset _ _)
    s_u := by
      rw [List.toFinset_cons,Finset.disjoint_insert_left]
      exact ⟨by simp,d.s_u.mono_left le_rfl |>.mono_right (Finset.erase_subset _ _)⟩
    cover := by
      ext x
      have hx : x ∈ d.finished ∪ d.stack.toFinset ∪ d.unexplored := by rw [d.cover]; simp
      simp only [Finset.mem_union] at hx
      simp only [List.toFinset_cons,Finset.mem_union,Finset.mem_insert,
        Finset.mem_erase,Finset.mem_univ,iff_true]
      by_cases hxw : x=w
      · exact Or.inl (Or.inr (Or.inl hxw))
      · rcases hx with (h|h)|h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr ⟨hxw,h⟩
    separation := by
      intro x hx y hy
      exact d.separation x hx y (Finset.mem_of_mem_erase hy) }
  have old_seen : ∀ x, x ≠ w → x ∉ d'.unexplored → x ∉ d.unexplored := by
    intro x hx hxu h
    exact hxu (Finset.mem_erase.mpr ⟨hx,h⟩)
  let p := Function.update s.path w (w::d.stack)
  have pw : p w=w::d.stack := by simp [p]
  have po : ∀ x, x ≠ w → p x=s.path x := by intro x hx; simp [p,hx]
  refine ⟨{
    state := d'
    path := p
    head := ?_
    nodup := ?_
    chain := ?_
    closed := ?_
    coherent := ?_
    stack_paths := ?_
    comparable := ?_ },Finset.card_erase_add_one hw,rfl⟩
  · intro x hx
    by_cases he : x=w
    · subst x; simp only [pw,List.head?_cons]
    · rw [po x he]; exact s.head x (old_seen x he hx)
  · intro x hx
    by_cases he : x=w
    · subst x; rw [pw]; exact List.nodup_cons.mpr ⟨hws,d.nodup⟩
    · rw [po x he]; exact s.nodup x (old_seen x he hx)
  · intro x hx
    by_cases he : x=w
    · subst x; rw [pw]; exact hchain
    · rw [po x he]; exact s.chain x (old_seen x he hx)
  · intro x hx y hy
    by_cases he : x=w
    · subst x
      rw [pw] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Finset.notMem_erase _ _
      · exact fun h => s.stack_seen hy (Finset.mem_of_mem_erase h)
    · rw [po x he] at hy
      exact fun h => s.closed x (old_seen x he hx) y hy (Finset.mem_of_mem_erase h)
  · intro x hx y hy
    by_cases he : x=w
    · subst x
      rw [pw] at hy ⊢
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [pw]
      · have hyw : y ≠ w := fun h => hws (h ▸ hy)
        rw [po y hyw]
        exact (s.path_suffix_stack hy).trans (List.suffix_cons _ _)
    · rw [po x he] at hy ⊢
      have hyo := s.closed x (old_seen x he hx) y hy
      have hyw : y ≠ w := fun h => hyo (h.symm ▸ hw)
      rw [po y hyw]
      exact s.coherent x (old_seen x he hx) y hy
  · intro x L hs
    change x::L <:+ w::d.stack at hs
    rcases List.suffix_cons_iff.mp hs with he | hs
    · have hx : x=w := (List.cons.inj he).1
      subst x
      rw [pw,he]
    · have hx : x ≠ w := fun h => hws (h ▸ hs.subset (by simp))
      rw [po x hx]
      exact s.stack_paths x L hs
  · intro x y hx hy hxy
    have adj_stack : ∀ z, z ≠ w → z ∉ d'.unexplored → G.Adj w z → z ∈ d.stack := by
      intro z hzw hz hwz
      rcases s.seen_cases (old_seen z hzw hz) with hz | hz
      · exact (d.separation z hz w hw hwz.symm).elim
      · exact hz
    by_cases hxw : x=w
    · subst x
      have hyw : y ≠ w := (G.ne_of_adj hxy).symm
      rw [pw,po y hyw]
      exact Or.inr ((s.path_suffix_stack (adj_stack y hyw hy hxy)).trans (List.suffix_cons _ _))
    by_cases hyw : y=w
    · subst y
      rw [pw,po x hxw]
      exact Or.inl ((s.path_suffix_stack (adj_stack x hxw hx hxy.symm)).trans (List.suffix_cons _ _))
    rw [po x hxw,po y hyw]
    exact s.comparable x y (old_seen x hxw hx) (old_seen y hyw hy) hxy

private theorem finish (s : RecordedDFS G) (v : V) (L : List V)
    (hs : s.state.stack=v::L)
    (hn : ∀ w ∈ s.state.unexplored, ¬G.Adj v w) :
    ∃ t : RecordedDFS G, t.state.unexplored=s.state.unexplored ∧
      t.state.stack.length+1=s.state.stack.length := by
  let d := s.state
  have hvf : v ∉ d.finished := fun hv => Finset.disjoint_left.mp d.f_s hv (by simp [d,hs])
  have hvu : v ∉ d.unexplored := s.stack_seen (by simp [hs])
  have hL : L.toFinset ⊆ d.stack.toFinset := by simp [d,hs]
  have hnd : v ∉ L ∧ L.Nodup := by simpa only [hs,List.nodup_cons] using s.state.nodup
  let d' : OAI.ErdosGallai.Scale.DFSState G := {
    stack := L
    finished := insert v d.finished
    unexplored := d.unexplored
    nodup := hnd.2
    chain := (hs ▸ d.chain).of_cons
    f_s := Finset.disjoint_insert_left.mpr ⟨by simpa using hnd.1,d.f_s.mono_right hL⟩
    f_u := Finset.disjoint_insert_left.mpr ⟨hvu,d.f_u⟩
    s_u := d.s_u.mono_left hL
    cover := by simpa [d,hs,Finset.insert_union] using d.cover
    separation := by
      intro x hx y hy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hn y hy
      · exact d.separation x hx y hy }
  refine ⟨{
    state := d'
    path := s.path
    head := s.head
    nodup := s.nodup
    chain := s.chain
    closed := s.closed
    coherent := s.coherent
    stack_paths := ?_
    comparable := s.comparable },rfl,?_⟩
  · intro x K hx
    apply s.stack_paths
    exact hx.trans (by rw [hs]; exact List.suffix_cons _ _)
  · change L.length+1=s.state.stack.length
    simp only [hs,List.length_cons]

private theorem completes (s : RecordedDFS G) :
    ∃ t : RecordedDFS G, t.state.unexplored=∅ := by
  generalize hm : 2*s.state.unexplored.card+s.state.stack.length=m
  induction m using Nat.strong_induction_on generalizing s with
  | h m ih =>
    by_cases hu : s.state.unexplored=∅
    · exact ⟨s,hu⟩
    cases hs : s.state.stack with
    | nil =>
      obtain ⟨w,hw⟩ := Finset.nonempty_iff_ne_empty.mpr hu
      obtain ⟨t,ht,hl⟩ := s.discover w hw (by simp [hs])
      exact ih _ (by simp only [hs,List.length_nil] at hm hl; omega) t rfl
    | cons v L =>
      by_cases hn : ∃ w ∈ s.state.unexplored, G.Adj v w
      · obtain ⟨w,hw,hvw⟩ := hn
        obtain ⟨t,ht,hl⟩ := s.discover w hw (by rw [hs]; exact List.IsChain.cons_cons hvw.symm (hs ▸ s.state.chain))
        exact ih _ (by omega) t rfl
      · have hn' : ∀ w ∈ s.state.unexplored, ¬G.Adj v w := by
          intro w hw hvw
          exact hn ⟨w,hw,hvw⟩
        obtain ⟨t,ht,hl⟩ := s.finish v L hs hn'
        exact ih _ (by rw [ht]; omega) t rfl

end RecordedDFS

/-- Every finite simple graph has a normal depth-first forest. The forest
is constructed by terminating discovery/pop transitions, not postulated. -/
theorem exists_normalDFSForest (G : SimpleGraph V) : Nonempty (NormalDFSForest G) := by
  let d : OAI.ErdosGallai.Scale.DFSState G :=
    ⟨[],∅,univ,by simp,by simp,by simp,by simp,by simp,by simp,by simp⟩
  let s : RecordedDFS G := {
    state := d
    path := fun _ => []
    head := by simp [d]
    nodup := by simp
    chain := by simp
    closed := by simp
    coherent := by simp
    stack_paths := by intro v L h; simpa [d] using h
    comparable := by simp [d] }
  obtain ⟨t,ht⟩ := s.completes
  exact ⟨{
    path := t.path
    head := fun v => t.head v (by simp [ht])
    nodup := fun v => t.nodup v (by simp [ht])
    chain := fun v => t.chain v (by simp [ht])
    coherent := fun v u hu => t.coherent v (by simp [ht]) u hu
    comparable := fun u v huv => t.comparable u v (by simp [ht]) (by simp [ht]) huv }⟩

end
end Cycle13
