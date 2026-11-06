import Cycle12.Foundations.ForestBound

/-! A short edge-count proof that a connected bichromatic component of
maximum degree two has color-class imbalance at most one. This avoids a
path/cycle classification when balancing edge-color classes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]

lemma connected_bipartite_parts_balance (H : SimpleGraph V) (hH : H.Connected)
    (S T : Finset V) (hb : H.IsBipartiteWith S T)
    (hdeg : ∀ v ∈ T, H.degree v ≤ 2) : S.card ≤ T.card+1 := by
  have hv := hH.card_vert_le_card_edgeSet_add_one
  have he : H.edgeFinset.card ≤ 2*T.card := by
    rw [← H.isBipartiteWith_sum_degrees_eq_card_edges' hb]
    calc
      _ ≤ ∑ _v ∈ T, 2 := sum_le_sum hdeg
      _ = _ := by simp [Nat.mul_comm]
  have hs : S.card+T.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint (Finset.disjoint_coe.mp hb.disjoint)]
    exact card_le_univ _
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hv
  omega

def twoColorGraph (H : SimpleGraph V) (f : V → C) (a b : C) : SimpleGraph V :=
  H.between {v | f v = a} {v | f v = b}

def colorSize (f : V → C) (a : C) : ℕ := (univ.filter (fun v => f v=a)).card

def componentColorSize (H : SimpleGraph V) (f : V → C) (a : C)
    (c : H.ConnectedComponent) : ℕ :=
  (univ.filter (fun v : c => f v.val=a)).card

theorem sum_component_colorSize (H : SimpleGraph V) (f : V → C) (a : C) :
    ∑ c : H.ConnectedComponent, componentColorSize H f a c = colorSize f a := by
  have hs : ∑ c : H.ConnectedComponent, ∑ v : c, (if f v.val=a then 1 else 0 : ℕ) =
      ∑ v : V, (if f v=a then 1 else 0 : ℕ) := by
    calc
      _ = ∑ x : (Σ c : H.ConnectedComponent, c), (if f x.2.val=a then 1 else 0 : ℕ) :=
        (Fintype.sum_sigma _).symm
      _ = _ := (componentVertexEquiv H).sum_comp (fun v : V => if f v=a then (1 : ℕ) else 0)
  simpa only [sum_boole, Nat.cast_id, componentColorSize, colorSize] using hs

theorem twoColor_component_balance (H : SimpleGraph V) (f : V → C) (a b : C)
    (hab : a ≠ b) (hdeg : ∀ v, (twoColorGraph H f a b).degree v ≤ 2)
    (c : (twoColorGraph H f a b).ConnectedComponent) :
    componentColorSize _ f a c ≤ componentColorSize _ f b c+1 := by
  let S := univ.filter (fun v : c => f v.val=a)
  let T := univ.filter (fun v : c => f v.val=b)
  have hb : c.toSimpleGraph.IsBipartiteWith S T := by
    refine ⟨Set.disjoint_left.mpr ?_, ?_⟩
    · intro v hvS hvT
      have ha : f v.val=a := (mem_filter.mp hvS).2
      have hb : f v.val=b := (mem_filter.mp hvT).2
      exact hab (ha.symm.trans hb)
    · intro v w hvw
      have h : (twoColorGraph H f a b).Adj v.val w.val := hvw
      rcases h.2 with h | h
      · exact Or.inl ⟨mem_filter.mpr ⟨mem_univ _, h.1⟩, mem_filter.mpr ⟨mem_univ _, h.2⟩⟩
      · exact Or.inr ⟨mem_filter.mpr ⟨mem_univ _, h.1⟩, mem_filter.mpr ⟨mem_univ _, h.2⟩⟩
  apply connected_bipartite_parts_balance c.toSimpleGraph c.connected_toSimpleGraph S T hb
  intro v _
  rw [component_degree_eq]
  exact hdeg v.val

/-- A larger color class supplies a component on which exactly one vertex
can be transferred to the smaller class by exchanging the two colors. -/
theorem exists_unbalanced_twoColor_component (H : SimpleGraph V) (f : V → C) (a b : C)
    (hab : a ≠ b) (hdeg : ∀ v, (twoColorGraph H f a b).degree v ≤ 2)
    (hsize : colorSize f b < colorSize f a) :
    ∃ c : (twoColorGraph H f a b).ConnectedComponent,
      componentColorSize _ f a c = componentColorSize _ f b c+1 := by
  have hex : ∃ c : (twoColorGraph H f a b).ConnectedComponent,
      componentColorSize _ f b c < componentColorSize _ f a c := by
    by_contra h
    push Not at h
    have hs := sum_le_sum (fun c (_ : c ∈ (univ : Finset (twoColorGraph H f a b).ConnectedComponent)) => h c)
    rw [sum_component_colorSize, sum_component_colorSize] at hs
    exact (not_le_of_gt hsize) hs
  obtain ⟨c, hc⟩ := hex
  exact ⟨c, by have hb := twoColor_component_balance H f a b hab hdeg c; omega⟩

end
end Cycle13
