import HaxellLib.Haxell

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V ι τ : Type*} [DecidableEq V] [DecidableEq τ]
variable {G : SimpleGraph V} {a b : V}

/-- Endpoints do not consume the vertex/team resource. -/
def routeInterior (p : G.Walk a b) : Finset V :=
  (p.support.toFinset.erase a).erase b

theorem routeInterior_card_le (p : G.Walk a b) :
    (routeInterior p).card ≤ p.length := by
  have ha : a ∈ p.support.toFinset := by simp
  have hcard := List.toFinset_card_le p.support
  rw [p.length_support] at hcard
  unfold routeInterior
  have hh : ((p.support.toFinset.erase a).erase b).card ≤ (p.support.toFinset.erase a).card := Finset.card_erase_le
  rw [Finset.card_erase_of_mem ha] at hh
  omega

theorem mem_routeInterior_iff (p : G.Walk a b) (v : V) :
    v ∈ routeInterior p ↔ v ∈ p.support ∧ v ≠ a ∧ v ≠ b := by
  simp only [routeInterior,Finset.mem_erase,List.mem_toFinset]
  tauto

/-- A route consumes its edges globally, and its interior vertices only
within its own team. The two sorts of resource are kept disjoint. -/
def routeResources (team : τ) (p : G.Walk a b) : Finset (Sym2 V ⊕ (τ × V)) :=
  p.edges.toFinset.map ⟨Sum.inl,Sum.inl_injective⟩ ∪
    (routeInterior p).map ⟨fun v => Sum.inr (team,v),by intro x y h; exact (Prod.mk.inj (Sum.inr.inj h)).2⟩

theorem routeResources_card_le (team : τ) (p : G.Walk a b) :
    (routeResources team p).card ≤ 2*p.length := by
  have h₁ := List.toFinset_card_le p.edges
  rw [p.length_edges] at h₁
  have h₂ := routeInterior_card_le p
  calc
    _ ≤ (p.edges.toFinset.map ⟨Sum.inl,Sum.inl_injective⟩).card+
        ((routeInterior p).map ⟨fun v => Sum.inr (team,v),by intro x y h; exact (Prod.mk.inj (Sum.inr.inj h)).2⟩).card :=
      Finset.card_union_le _ _
    _ ≤ 2*p.length := by simp only [Finset.card_map]; omega

theorem routeResources_disjoint_edges {c d : V} {team team' : τ}
    {p : G.Walk a b} {q : G.Walk c d}
    (h : Disjoint (routeResources team p) (routeResources team' q)) :
    Disjoint p.edges.toFinset q.edges.toFinset := by
  rw [Finset.disjoint_left] at h ⊢
  intro e hp hq
  apply h (a:=Sum.inl e)
  · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨e,hp,rfl⟩)
  · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨e,hq,rfl⟩)

theorem routeResources_disjoint_interiors {c d : V} {team : τ}
    {p : G.Walk a b} {q : G.Walk c d}
    (h : Disjoint (routeResources team p) (routeResources team q)) :
    Disjoint (routeInterior p) (routeInterior q) := by
  rw [Finset.disjoint_left] at h ⊢
  intro v hp hq
  apply h (a:=Sum.inr (team,v))
  · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v,hp,rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v,hq,rfl⟩)

/-- The Haxell resource argument produces actual simple paths, with edge
disjointness across all demands and interior disjointness within each team.
`Good` can record hard avoidance and a bound on soft intersections.
The remaining graph obligation is explicit: an uncovered candidate must
exist for every small resource cover. -/
theorem haxell_select_routes [Fintype ι]
    (source target : ι → V) (team : ι → τ)
    (Good : ∀ i, G.Walk (source i) (target i) → Prop)
    {ell : ℕ} (hell : 0 < ell)
    (havoid : ∀ I : Finset ι, I.Nonempty →
      ∀ Z : Finset (Sym2 V ⊕ (τ × V)), Z.card < 4*ell*I.card →
      ∃ i ∈ I, ∃ p : G.Walk (source i) (target i),
        p.IsPath ∧ p.length ≤ ell ∧ Good i p ∧ Disjoint (routeResources (team i) p) Z) :
    ∃ p : ∀ i, G.Walk (source i) (target i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ ell ∧ Good i (p i)) ∧
      (∀ i j, i ≠ j → Disjoint (p i).edges.toFinset (p j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j →
        Disjoint (routeInterior (p i)) (routeInterior (p j))) := by
  classical
  let H : ι → Finset (Sym2 V ⊕ (τ × V)) → Prop := fun i e =>
    ∃ p : G.Walk (source i) (target i),
      p.IsPath ∧ p.length ≤ ell ∧ Good i p ∧ e=routeResources (team i) p
  have hsize : ∀ i e, H i e → e.card ≤ 2*ell := by
    rintro i e ⟨p,hp,hlen,hgood,rfl⟩
    exact (routeResources_card_le _ _).trans (Nat.mul_le_mul_left _ hlen)
  have hcond : ∀ I : Finset ι, I.Nonempty →
      ∀ Z : Finset (Sym2 V ⊕ (τ × V)), Z.card ≤ 2*(2*ell)*(I.card-1) →
      ∃ i ∈ I, ∃ e, H i e ∧ Disjoint e Z := by
    intro I hI Z hZ
    have hcard : 0 < I.card := hI.card_pos
    have hZ' : Z.card < 4*ell*I.card := by
      have he : I.card=I.card-1+1 := by omega
      nlinarith
    obtain ⟨i,hi,p,hp,hlen,hgood,hdis⟩ := havoid I hI Z hZ'
    exact ⟨i,hi,routeResources (team i) p,⟨p,hp,hlen,hgood,rfl⟩,hdis⟩
  obtain ⟨f,hf,hdis⟩ := Lovasz.Haxell.haxell hsize hcond
  choose p hp hlen hgood he using hf
  refine ⟨p,fun i => ⟨hp i,hlen i,hgood i⟩,?_,?_⟩
  · intro i j hij
    have hh := hdis i j hij
    rw [he i,he j] at hh
    exact routeResources_disjoint_edges hh
  · intro i j hij ht
    have hh := hdis i j hij
    rw [he i,he j,ht] at hh
    exact routeResources_disjoint_interiors hh

end
end Cycle13
