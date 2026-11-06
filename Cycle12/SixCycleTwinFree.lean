import Cycle12.SixCycleEdgeShape
import Cycle12.SixCycleIndependentClassification

namespace Cycle12
open SimpleGraph

def NoDegreeTwoTwins {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ a b x y, a≠b → (∀ v, G.Adj x v ↔ v=a ∨ v=b) →
    (∀ v, G.Adj y v ↔ v=a ∨ v=b) → x=y

/-- After the degree-two twin reduction, the exterior of any six-cycle
is a matching and isolated vertices. No change of the core cycle is needed. -/
theorem six_cycle_twin_free_exterior_matching {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (htwin : NoDegreeTwoTwins G)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7) :
    ∀ x y z, x∉c.support → y∉c.support → z∉c.support →
      G.Adj x y → G.Adj x z → y=z := by
  intro x y z hx hy hz hxy hxz
  classical
  by_contra hyz
  have hn : [y,x,z].Nodup := by
    simp [List.nodup_cons,hxy.ne.symm,hxz.ne,hyz]
  obtain ⟨a,ha,hY,hZ⟩ := six_cycle_external_two_path_twins
    G hconn hrobust c hc hlen hshort hy hx hz hn hxy.symm hxz
  have hax : a≠x := fun he => hx (he ▸ ha)
  exact hyz (htwin a x y z hax hY hZ)

/-- Every pair attachment type has multiplicity at most one once the
corresponding actual twin configuration has been removed. -/
theorem six_pair_attachment_unique {V : Type} {G : SimpleGraph V}
    (htwin : NoDegreeTwoTwins G) {f : Fin 6 ↪ V} {i : Fin 11}
    (hi : i.val<9) {x y : V}
    (hx : SixAttachmentVertex G f i x) (hy : SixAttachmentVertex G f i y) : x=y := by
  have hpair : ∃ a b, a≠b ∧ sixAttachment i={a,b} := by
    have hh : ∀ i : Fin 11, i.val<9 → ∃ a b, a≠b ∧ sixAttachment i={a,b} := by
      decide +kernel
    exact hh i hi
  obtain ⟨a,b,hab,hpair⟩ := hpair
  apply htwin (f a) (f b) x y (f.injective.ne hab)
  · intro v
    rw [hx.2,hpair]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨k,(rfl | rfl),he⟩
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · rintro (rfl | rfl)
      · exact ⟨a,Or.inl rfl,rfl⟩
      · exact ⟨b,Or.inr rfl,rfl⟩
  · intro v
    rw [hy.2,hpair]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨k,(rfl | rfl),he⟩
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · rintro (rfl | rfl)
      · exact ⟨a,Or.inl rfl,rfl⟩
      · exact ⟨b,Or.inr rfl,rfl⟩

end Cycle12
