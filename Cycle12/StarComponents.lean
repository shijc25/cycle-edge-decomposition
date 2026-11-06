import Cycle12.SixCycleExternalStars

namespace Cycle12
open SimpleGraph

/-- A vertex property closed under adjacency is preserved by actual walks. -/
theorem reachable_preserves_adj_closed {W : Type} (H : SimpleGraph W) (P : W → Prop)
    (hclosed : ∀ u v, P u → H.Adj u v → P v)
    {a b : W} (ha : P a) (hab : H.Reachable a b) : P b := by
  have main : ∀ {u v : W}, (H.Walk u v) → P u → P v := by
    intro u v p
    induction p with
    | nil => intro hu; exact hu
    | @cons u v w huv p ih =>
      intro hu
      exact ih (hclosed u v hu huv)
  obtain ⟨p⟩ := hab
  exact main p ha

theorem connected_star_of_neighbor_leaves {W : Type} (H : SimpleGraph W)
    (hconn : H.Connected) (a : W)
    (hleaf : ∀ x, H.Adj a x → ∀ y, H.Adj x y → y=a) :
    ∀ x, x≠a → ∀ y, H.Adj x y ↔ y=a := by
  let P : W → Prop := fun x => x=a ∨ H.Adj a x
  have hclosed : ∀ u v, P u → H.Adj u v → P v := by
    intro u v hu huv
    rcases hu with rfl | hu
    · exact Or.inr huv
    · exact Or.inl (hleaf u hu v huv)
  intro x hxa y
  have hx := reachable_preserves_adj_closed H P hclosed (a:=a) (b:=x)
    (Or.inl rfl) (hconn a x)
  have hax : H.Adj a x := hx.resolve_left hxa
  constructor
  · exact hleaf x hax y
  · rintro rfl
    exact hax.symm

/-- The local two-path leaf property classifies every connected graph as a
star, including the singleton and the one-edge cases. -/
theorem connected_star_of_two_path_leaves {W : Type} (H : SimpleGraph W)
    (hconn : H.Connected)
    (hleaf : ∀ x y z, H.Adj x y → H.Adj y z → x≠z →
      ∀ w, H.Adj x w → w=y) :
    ∃ a, ∀ x, x≠a → ∀ y, H.Adj x y ↔ y=a := by
  classical
  by_cases hbranch : ∃ a x z, H.Adj a x ∧ H.Adj a z ∧ x≠z
  · obtain ⟨a,x,z,hax,haz,hxz⟩ := hbranch
    refine ⟨a,connected_star_of_neighbor_leaves H hconn a ?_⟩
    intro v hav w hvw
    by_cases hvx : v=x
    · subst v
      exact hleaf x a z hax.symm haz hxz w hvw
    · exact hleaf v a x hav.symm hax hvx w hvw
  · obtain ⟨a⟩ := hconn.nonempty
    refine ⟨a,connected_star_of_neighbor_leaves H hconn a ?_⟩
    intro v hav w hvw
    by_contra hwa
    exact hbranch ⟨v,a,w,hav.symm,hvw,Ne.symm hwa⟩

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every component of the induced graph outside a six-cycle is a star.
The center and every leaf are actual vertices of that component. -/
theorem six_cycle_exterior_components_are_stars (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (D : (G.induce {v | v∉c.support}).ConnectedComponent) :
    ∃ a : D, ∀ x : D, x≠a → ∀ y : D, D.toSimpleGraph.Adj x y ↔ y=a := by
  apply connected_star_of_two_path_leaves D.toSimpleGraph D.connected_toSimpleGraph
  intro x y z hxy hyz hxz w hxw
  have hxy' : x.val.val≠y.val.val := (show G.Adj x.val.val y.val.val from hxy).ne
  have hyz' : y.val.val≠z.val.val := (show G.Adj y.val.val z.val.val from hyz).ne
  have hxz' : x.val.val≠z.val.val := fun he => hxz (Subtype.ext (Subtype.ext he))
  have hn : [x.val.val,y.val.val,z.val.val].Nodup := by
    simp [List.nodup_cons,hxy',hyz',hxz']
  have hh := six_cycle_external_two_path_endpoints_are_leaves G hconn hrobust c hc hlen hshort
    x.val.property y.val.property z.val.property hn hxy hyz
  exact Subtype.ext (Subtype.ext (hh.1 w.val.val w.val.property hxw))

end
end Cycle12
