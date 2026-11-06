import Cycle12.Foundations.ListEdgeColoring
import Cycle12.Foundations.OrderedLinks
import Cycle12.Foundations.ImmersionPaths

/-! List edge colours as actual two-edge reservoir paths, including exact
control of the reservoir neighbours lost at each branch. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure ReservoirLinks {W V : Type} (R : SimpleGraph W) (G : SimpleGraph V)
    (D : Finset V) (φ : W ↪ V) where
  color : R.lineGraph.Coloring V
  mem : ∀ e, color e ∈ D
  adjacent : ∀ e v, v ∈ e.val → G.Adj (φ v) (color e)

theorem exists_reservoir_links_of_coloring {W V : Type} [Fintype W] [DecidableEq V]
    (R : SimpleGraph W) (G : SimpleGraph V) (D : Finset V) (φ : W ↪ V)
    (k : ℕ) (hcolor : ∀ L : R.edgeSet → Finset V,
      (∀ e, k ≤ (L e).card) → ∃ f : R.lineGraph.Coloring V, ∀ e, f e ∈ L e)
    (hroom : ∀ x y, R.Adj x y →
      k + missingNeighbors G D (φ x) + missingNeighbors G D (φ y) ≤ D.card) :
    Nonempty (ReservoirLinks R G D φ) := by
  classical
  let L := fun e : R.edgeSet => commonChoices G D (φ e.val.out.1) (φ e.val.out.2)
  have hout : ∀ e : R.edgeSet, s(e.val.out.1,e.val.out.2)=e.val := fun e => e.val.out_eq
  obtain ⟨f,hf⟩ := hcolor L (by
    intro e
    have he : R.Adj e.val.out.1 e.val.out.2 := by
      change s(e.val.out.1,e.val.out.2) ∈ R.edgeSet
      rw [hout]
      exact e.property
    have h₁ := hroom _ _ he
    have h₂ := commonChoices_card G D (φ e.val.out.1) (φ e.val.out.2)
    change k ≤ (commonChoices G D (φ e.val.out.1) (φ e.val.out.2)).card
    omega)
  refine ⟨⟨f,fun e => (mem_filter.mp (hf e)).1,?_⟩⟩
  intro e v hv
  rw [← hout] at hv
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact (mem_filter.mp (hf e)).2.1
  · exact (mem_filter.mp (hf e)).2.2

theorem exists_reservoir_links {W V : Type} [Fintype W] [DecidableEq V]
    (R : SimpleGraph W) (G : SimpleGraph V) (D : Finset V) (φ : W ↪ V)
    (hroom : ∀ x y, R.Adj x y →
      Fintype.card W + missingNeighbors G D (φ x) + missingNeighbors G D (φ y) ≤ D.card) :
    Nonempty (ReservoirLinks R G D φ) :=
  exists_reservoir_links_of_coloring R G D φ _ (exists_list_edge_coloring R) hroom

theorem exists_reservoir_links_supported {W V : Type} [Fintype W] [DecidableEq V]
    (R : SimpleGraph W) (G : SimpleGraph V) (D : Finset V) (φ : W ↪ V)
    (S : Finset W) (hs : R.support ⊆ (S : Set W))
    (hroom : ∀ x y, R.Adj x y →
      S.card + missingNeighbors G D (φ x) + missingNeighbors G D (φ y) ≤ D.card) :
    Nonempty (ReservoirLinks R G D φ) :=
  exists_reservoir_links_of_coloring R G D φ _
    (exists_list_edge_coloring_supported R S hs) hroom

namespace ReservoirLinks
variable {W V : Type} [DecidableEq V] {R : SimpleGraph W} {G : SimpleGraph V}
    {D : Finset V} {φ : W ↪ V} (L : ReservoirLinks R G D φ)

def walk {x y : W} (h : R.Adj x y) : G.Walk (φ x) (φ y) :=
  (L.adjacent ⟨s(x,y),h⟩ x (Sym2.mem_mk_left _ _)).toWalk.append
    (L.adjacent ⟨s(x,y),h⟩ y (Sym2.mem_mk_right _ _)).symm.toWalk

def used : Set (Sym2 V) := {e | ∃ (d : R.edgeSet) (v : W),
  v ∈ d.val ∧ e=s(φ v,L.color d)}

def residue : SimpleGraph V := G.deleteEdges L.used

lemma walk_isPath (hout : ∀ v, φ v ∉ D) {x y : W} (h : R.Adj x y) :
    (L.walk h).IsPath := by
  have hx : φ x ≠ L.color ⟨s(x,y),h⟩ := fun e => hout x (e ▸ L.mem _)
  have hy : φ y ≠ L.color ⟨s(x,y),h⟩ := fun e => hout y (e ▸ L.mem _)
  simp [walk,Walk.isPath_def,Adj.toWalk,Walk.support_append,hx,hy.symm,φ.injective.ne h.ne]

lemma walk_edges_used {x y : W} (h : R.Adj x y) : (L.walk h).edgeSet ⊆ L.used := by
  intro e he
  simp only [walk,Walk.edgeSet_append,Adj.toWalk,Walk.edgeSet_cons,Walk.edgeSet_nil,
    Set.mem_union,Set.mem_insert_iff,Set.mem_empty_iff_false,or_false] at he
  rcases he with rfl | rfl
  · exact ⟨⟨s(x,y),h⟩,x,Sym2.mem_mk_left _ _,rfl⟩
  · exact ⟨⟨s(x,y),h⟩,y,Sym2.mem_mk_right _ _,Sym2.eq_swap⟩

lemma used_edge_origin (hout : ∀ v, φ v ∉ D) {v : W} {w : V}
    (hw : w ∈ D) (he : s(φ v,w) ∈ L.used) :
    ∃ d : R.edgeSet, v ∈ d.val ∧ w=L.color d := by
  obtain ⟨d,u,hu,he⟩ := he
  rcases Sym2.eq_iff.mp he with ⟨hvu,hwc⟩ | ⟨hvc,hwu⟩
  · exact ⟨d,φ.injective hvu ▸ hu,hwc⟩
  · exact False.elim (hout v (hvc ▸ L.mem d))

lemma missing_residue_le [Fintype W] (hout : ∀ v, φ v ∉ D) (v : W) :
    missingNeighbors L.residue D (φ v) ≤ missingNeighbors G D (φ v) + R.degree v := by
  classical
  let F : R.incidenceSet v → V := fun d => L.color ⟨d.val,(R.incidenceSet_subset v) d.property⟩
  have hs : D.filter (fun w => ¬ L.residue.Adj (φ v) w) ⊆
      D.filter (fun w => ¬G.Adj (φ v) w) ∪ univ.image F := by
    intro w hw
    have hwD := (mem_filter.mp hw).1
    by_cases hG : G.Adj (φ v) w
    · have he : s(φ v,w) ∈ L.used := by
        have hn := (mem_filter.mp hw).2
        simpa [residue,deleteEdges_adj,hG] using hn
      obtain ⟨d,hvd,rfl⟩ := L.used_edge_origin hout hwD he
      apply mem_union_right
      apply mem_image.mpr
      exact ⟨⟨d.val,⟨d.property,hvd⟩⟩,mem_univ _,rfl⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hwD,hG⟩)
  have h₁ := card_le_card hs
  have h₂ := card_union_le (D.filter (fun w => ¬G.Adj (φ v) w)) (univ.image F)
  have h₃ := card_image_le (s := univ) (f := F)
  have h₄ : (univ : Finset (R.incidenceSet v)).card=R.degree v := by
    rw [card_univ,card_incidenceSet_eq_degree]
  unfold missingNeighbors
  omega

lemma walk_disjoint (hout : ∀ v, φ v ∉ D) {x y a b : W}
    (h : R.Adj x y) (k : R.Adj a b) (hne : s(x,y) ≠ s(a,b)) :
    Disjoint (L.walk h).edgeSet (L.walk k).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he hk
  have horigin : ∀ {u v : W} (h : R.Adj u v), ∀ e ∈ (L.walk h).edgeSet,
      ∃ z, z ∈ s(u,v) ∧ e=s(φ z,L.color ⟨s(u,v),h⟩) := by
    intro u v h e he
    simp only [walk,Walk.edgeSet_append,Adj.toWalk,Walk.edgeSet_cons,Walk.edgeSet_nil,
      Set.mem_union,Set.mem_insert_iff,Set.mem_empty_iff_false,or_false] at he
    rcases he with he | he
    · exact ⟨u,Sym2.mem_mk_left _ _,he⟩
    · exact ⟨v,Sym2.mem_mk_right _ _,he.trans Sym2.eq_swap⟩
  obtain ⟨u,hu,heu⟩ := horigin h e he
  obtain ⟨v,hv,hev⟩ := horigin k e hk
  rcases Sym2.eq_iff.mp (heu.symm.trans hev) with ⟨huv,hcol⟩ | ⟨huc,hcv⟩
  · apply L.color.valid (lineGraph_adj_iff_exists.mpr
      ⟨fun he => hne (congrArg Subtype.val he),u,hu,?_⟩) hcol
    exact φ.injective huv ▸ hv
  · exact hout u (huc ▸ L.mem _)

lemma walk_avoids (hout : ∀ v, φ v ∉ D) {x y : W} (h : R.Adj x y) (v : W)
    (hv : φ v ∈ (L.walk h).support) : v=x ∨ v=y := by
  simp only [walk,Adj.toWalk,Walk.support_append,Walk.support_cons,Walk.support_nil,
    List.tail_cons,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
  rcases hv with (h | h) | h
  · exact Or.inl (φ.injective h)
  · exact False.elim (hout v (h ▸ L.mem _))
  · exact Or.inr (φ.injective h)

def routing (hout : ∀ v, φ v ∉ D) : EdgeRouting R G where
  vertex := φ
  route := L.walk
  disjoint := L.walk_disjoint hout
  avoids := L.walk_avoids hout

end ReservoirLinks
end
end Cycle13
