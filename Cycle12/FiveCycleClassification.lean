import Cycle12.FiveCycleNeighborhood
import Cycle12.FiveCycleFrame

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V}

/-- The permitted diagonal pairs in an arbitrary ambient graph all share
a hub. At most two different external neighborhoods occur. -/
theorem five_cycle_common_hub (f : Fin 5 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hshort : Cycle13.NoCycleAtLeast G 6)
    (hpair : ∀ x, (∀ i, x≠f i) →
      ∃ k : Fin 5, ∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+2)) :
    ∃ h : Fin 5, ∀ x, (∀ i, x≠f i) →
      (∀ v, G.Adj x v ↔ v=f h ∨ v=f (h+2)) ∨
      (∀ v, G.Adj x v ↔ v=f h ∨ v=f (h+3)) := by
  let S : Finset (Fin 5) := univ.filter (fun k => ∃ x,
    (∀ i, x≠f i) ∧ ∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+2))
  have hfamily : ∀ i∈S, ∀ j∈S, i=j ∨ i=j+2 ∨ j=i+2 := by
    intro i hi j hj
    obtain ⟨x,hx,hX⟩ := (mem_filter.mp hi).2
    obtain ⟨y,hy,hY⟩ := (mem_filter.mp hj).2
    have hxa : G.Adj x (f i) := (hX _).mpr (Or.inl rfl)
    have hxc : G.Adj x (f (i+2)) := (hX _).mpr (Or.inr rfl)
    have hyb : G.Adj y (f j) := (hY _).mpr (Or.inl rfl)
    have hyd : G.Adj y (f (j+2)) := (hY _).mpr (Or.inr rfl)
    rcases five_ring_index_alternatives i j with he | he | he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
    · subst j
      exact False.elim (five_cycle_no_adjacent_pair_types f hcycle hshort hx hy i hxa hxc hyb hyd)
    · subst i
      exact False.elim (five_cycle_no_adjacent_pair_types f hcycle hshort hy hx j hyb hyd hxa hxc)
  obtain ⟨h,hh⟩ := five_ring_pairwise_family S hfamily
  refine ⟨h,?_⟩
  intro x hx
  obtain ⟨k,hk⟩ := hpair x hx
  have hkS : k∈S := mem_filter.mpr ⟨mem_univ _,x,hx,hk⟩
  rcases hh k hkS with rfl | rfl
  · exact Or.inl hk
  · right
    have hwrap : (h+3)+2=h := by fin_cases h <;> decide
    intro v
    simpa only [hwrap,or_comm] using hk v

/-- The complete infinite H-family classification for circumference five.
The five core vertices retain arbitrary chords permitted by the circumference
hypothesis; every other vertex has exactly one of two specified neighborhoods. -/
theorem five_cycle_common_hub_classification [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 6)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=5) :
    ∃ (f : Fin 5 ↪ V) (h : Fin 5),
      (∀ i, G.Adj (f i) (f (i+1))) ∧
      (∀ x, x∈c.support ↔ ∃ i, f i=x) ∧
      (∀ x, (∀ i, x≠f i) →
        (∀ v, G.Adj x v ↔ v=f h ∨ v=f (h+2)) ∨
        (∀ v, G.Adj x v ↔ v=f h ∨ v=f (h+3))) := by
  obtain ⟨f,hcycle,hsupport⟩ := five_cycle_frame hc hlen
  have hshort' : Cycle13.NoCycleAtLeast G (c.length+1) := by simpa only [hlen] using hshort
  have hxout : ∀ x, (∀ i, x≠f i) → x∉c.support := by
    intro x hx hh
    obtain ⟨i,hi⟩ := (hsupport x).mp hh
    exact hx i hi.symm
  have hout : ∀ x y, (∀ i, x≠f i) → (∀ i, y≠f i) → ¬G.Adj x y := by
    intro x y hx hy
    exact short_longest_cycle_outside_independent G hconn hrobust c hc (by omega)
      hshort' (hxout x hx) (hxout y hy)
  have hpair : ∀ x, (∀ i, x≠f i) →
      ∃ k : Fin 5, ∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+2) := by
    intro x hx
    obtain ⟨a,ha,b,hb,hab,hxa,hxb⟩ :=
      short_longest_cycle_two_neighbors G hconn hrobust c hc (by omega) hshort' x (hxout x hx)
    obtain ⟨i,rfl⟩ := (hsupport a).mp ha
    obtain ⟨j,rfl⟩ := (hsupport b).mp hb
    exact five_cycle_external_pair f hcycle hshort hout hx
      ⟨i,j,fun he => hab (congrArg f he),hxa,hxb⟩
  obtain ⟨h,hH⟩ := five_cycle_common_hub f hcycle hshort hpair
  exact ⟨f,h,hcycle,hsupport,hH⟩

end
end Cycle12
