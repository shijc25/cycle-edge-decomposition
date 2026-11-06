import Cycle12.StarComponents

namespace Cycle12
open SimpleGraph

/-- Deleting any one vertex cannot isolate a different vertex when a third
vertex remains. The witness is an actual neighbor in the original graph. -/
theorem robust_neighbor_avoiding_vertex {V : Type} (G : SimpleGraph V)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {x a b : V} (hxa : x≠a) (hba : b≠a) (hbx : b≠x) :
    ∃ y, G.Adj x y ∧ y≠a := by
  classical
  by_contra hn
  have hsingle : ∀ y, G.Adj x y → y=a := by
    intro y hy
    by_contra hya
    exact hn ⟨y,hy,hya⟩
  let H := G.induce ({a}ᶜ : Set V)
  let P : ({a}ᶜ : Set V) → Prop := fun v => v.val=x
  have hclosed : ∀ u v, P u → H.Adj u v → P v := by
    intro u v hu huv
    have hxv : G.Adj x v.val := by simpa only [P] using hu ▸ huv
    exact False.elim (v.property (hsingle v.val hxv))
  have hh := reachable_preserves_adj_closed H P hclosed
    (a:=⟨x,hxa⟩) (b:=⟨b,hba⟩) rfl (hrobust a ⟨x,hxa⟩ ⟨b,hba⟩)
  exact hbx hh

end Cycle12
