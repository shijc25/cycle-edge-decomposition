import Cycle12.SixCycleTwins

namespace Cycle12
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every exterior edge has two distinct cycle attachments, one at each
end. Equal singleton attachments have already been excluded by connectivity. -/
theorem six_cycle_external_edge_distinct_attachments (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hxy : G.Adj x y) :
    ∃ a∈c.support, ∃ b∈c.support, a≠b ∧ G.Adj x a ∧ G.Adj y b := by
  classical
  obtain ⟨a,ha,hxa⟩ := six_cycle_dominates G hconn hrobust hshort c hc hlen x hx
  obtain ⟨b,hb,hyb⟩ := six_cycle_dominates G hconn hrobust hshort c hc hlen y hy
  by_contra hn
  have hab : a=b := by
    by_contra hab
    exact hn ⟨a,ha,b,hb,hab,hxa,hyb⟩
  subst b
  have hX : ∀ v∈c.support, G.Adj x v ↔ v=a := by
    intro v hv
    constructor
    · intro hxv
      by_contra hva
      exact hn ⟨v,hv,a,ha,hva,hxv,hyb⟩
    · rintro rfl
      exact hxa
  have hY : ∀ v∈c.support, G.Adj y v ↔ v=a := by
    intro v hv
    constructor
    · intro hyv
      by_contra hva
      exact hn ⟨a,ha,v,hv,Ne.symm hva,hxa,hyv⟩
    · rintro rfl
      exact hyb
  exact six_cycle_no_equal_single_attachments G hconn hrobust c hc hlen hshort
    ha hx hy hxy hX hY

/-- Complete neighborhoods of an exterior two-vertex component. Only the
two optional reverse attachments remain; their values distinguish a path,
a triangle leg, and a diamond. -/
theorem six_cycle_external_edge_full_shape (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hxy : G.Adj x y)
    (hXout : ∀ v, v∉c.support → G.Adj x v → v=y)
    (hYout : ∀ v, v∉c.support → G.Adj y v → v=x) :
    ∃ a, ∃ ha:a∈c.support, ∃ b∈c.support, a≠b ∧
      (c.rotate a ha).getVert 3=b ∧
      (∀ v, G.Adj x v ↔ v=y ∨ v=a ∨ (G.Adj x b ∧ v=b)) ∧
      (∀ v, G.Adj y v ↔ v=x ∨ v=b ∨ (G.Adj y a ∧ v=a)) := by
  obtain ⟨a,ha,b,hb,hab,hxa,hyb⟩ := six_cycle_external_edge_distinct_attachments
    G hconn hrobust c hc hlen hshort hx hy hxy
  have hopp := six_cycle_external_edge_opposite hc hlen hshort ha hb hab hx hy hxa hxy hyb
  obtain ⟨hX,hY⟩ := six_cycle_external_edge_attachment_pair hc hlen hshort ha hb hab hx hy hxa hxy hyb
  refine ⟨a,ha,b,hb,hab,hopp,?_,?_⟩
  · intro v
    constructor
    · intro hxv
      by_cases hv : v∈c.support
      · rcases hX v hv hxv with he | he
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr ⟨he ▸ hxv,he⟩)
      · exact Or.inl (hXout v hv hxv)
    · rintro (rfl | rfl | ⟨h,rfl⟩)
      · exact hxy
      · exact hxa
      · exact h
  · intro v
    constructor
    · intro hyv
      by_cases hv : v∈c.support
      · rcases hY v hv hyv with he | he
        · exact Or.inr (Or.inr ⟨he ▸ hyv,he⟩)
        · exact Or.inr (Or.inl he)
      · exact Or.inl (hYout v hv hyv)
    · rintro (rfl | rfl | ⟨h,rfl⟩)
      · exact hxy.symm
      · exact hyb
      · exact h

end Cycle12
