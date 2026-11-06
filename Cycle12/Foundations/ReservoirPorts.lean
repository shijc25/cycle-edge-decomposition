import Cycle12.Foundations.CutMenger

/-! A port graph for routing sources into a reservoir. Original edges are
vertices, so vertex-disjoint port paths cannot reuse an original edge.
Two edge vertices are adjacent only at a common reservoir vertex. This
explicitly prevents transit through an outside source. -/
namespace Cycle13.ReservoirPorts
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev Vertex (G : SimpleGraph V) (A B : Finset V) (c : ℕ) :=
  A ⊕ (G.edgeSet ⊕ (B × Fin c))

def Adj (G : SimpleGraph V) (A U B : Finset V) (c : ℕ) :
    Vertex G A B c → Vertex G A B c → Prop
  | .inl a, .inr (.inl e) => ∃ u ∈ U, e.val = s(a.val, u)
  | .inr (.inl e), .inl a => ∃ u ∈ U, e.val = s(a.val, u)
  | .inr (.inl e), .inr (.inl f) => e ≠ f ∧ ∃ u ∈ U, u ∈ e.val ∧ u ∈ f.val
  | .inr (.inl e), .inr (.inr q) => q.1.val ∈ e.val
  | .inr (.inr q), .inr (.inl e) => q.1.val ∈ e.val
  | _, _ => False

def graph (G : SimpleGraph V) (A U B : Finset V) (c : ℕ) :
    SimpleGraph (Vertex G A B c) where
  Adj := Adj G A U B c
  symm := ⟨by
    intro x y h
    rcases x with a | x <;> rcases y with b | y
    · exact h
    · rcases y with e | q <;> exact h
    · rcases x with e | q <;> exact h
    · rcases x with e | q <;> rcases y with f | r
      · exact ⟨Ne.symm h.1, by
          obtain ⟨u, hu, he, hf⟩ := h.2
          exact ⟨u, hu, hf, he⟩⟩
      · exact h
      · exact h
      · exact h⟩
  loopless := ⟨by
    intro x
    rcases x with a | x
    · exact not_false
    · rcases x with e | q
      · exact fun h => h.1 rfl
      · exact not_false⟩

def sources (G : SimpleGraph V) (A B : Finset V) (c : ℕ) : Finset (Vertex G A B c) :=
  univ.image Sum.inl

def targets (G : SimpleGraph V) (A B : Finset V) (c : ℕ) : Finset (Vertex G A B c) :=
  univ.image (fun q => Sum.inr (Sum.inr q))

def Reach (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (X : Finset (Vertex G A B c)) (v : Vertex G A B c) : Prop :=
  Menger.Aux.R (graph G A U B c) (sources G A B c) X v

theorem Reach.not_mem {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)} {v : Vertex G A B c}
    (h : Reach G A U B c X v) : v ∉ X := Menger.Aux.R.not_mem h

theorem Reach.step {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)} {v w : Vertex G A B c}
    (h : Reach G A U B c X v) (hvw : (graph G A U B c).Adj v w) (hw : w ∉ X) :
    Reach G A U B c X w := by
  obtain ⟨a, ha, p, hp⟩ := h
  refine ⟨a, ha, p.concat hvw, ?_⟩
  intro z hz
  simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
  rcases hz with hz | rfl
  · exact hp z hz
  · exact hw

theorem source_reach {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)} (a : A) (ha : Sum.inl a ∉ X) :
    Reach G A U B c X (Sum.inl a) :=
  Menger.Aux.R.of_mem (by simp [sources]) ha

def side (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (X : Finset (Vertex G A B c)) : Finset V :=
  U.filter (fun u => ∃ e : G.edgeSet, Reach G A U B c X (Sum.inr (Sum.inl e)) ∧ u ∈ e.val)

theorem side_subset (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (X : Finset (Vertex G A B c)) : side G A U B c X ⊆ U := filter_subset _ _

theorem reachable_incident_edge {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)} {v : V} (hv : v ∈ side G A U B c X)
    (f : G.edgeSet) (hvf : v ∈ f.val) (hf : Sum.inr (Sum.inl f) ∉ X) :
    Reach G A U B c X (Sum.inr (Sum.inl f)) := by
  obtain ⟨hvU, e, he, hve⟩ := mem_filter.mp hv
  by_cases h : e = f
  · simpa only [h] using he
  · exact he.step ⟨h, v, hvU, hve, hvf⟩ hf

/-- Every internal reservoir edge across the reachable-side cut is
represented by a vertex of the separator. -/
theorem boundary_edge_in_separator {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)} {x y : V}
    (hx : x ∈ side G A U B c X) (hyU : y ∈ U) (hy : y ∉ side G A U B c X)
    (hxy : G.Adj x y) : Sum.inr (Sum.inl (⟨s(x,y), hxy⟩ : G.edgeSet)) ∈ X := by
  by_contra h
  have hr := reachable_incident_edge hx ⟨s(x,y), hxy⟩ (Sym2.mem_mk_left _ _) h
  exact hy (mem_filter.mpr ⟨hyU, ⟨⟨s(x,y), hxy⟩, hr, Sym2.mem_mk_right _ _⟩⟩)

/-- A surviving source cannot have an undeleted attachment edge to the
unreachable part of the reservoir. -/
theorem attachment_edge_in_separator {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)} (a : A) (ha : Sum.inl a ∉ X)
    {u : V} (hu : u ∈ U) (huS : u ∉ side G A U B c X) (hau : G.Adj a.val u) :
    Sum.inr (Sum.inl (⟨s(a.val,u), hau⟩ : G.edgeSet)) ∈ X := by
  by_contra h
  have hr := (source_reach (U := U) a ha).step
    (show (graph G A U B c).Adj (Sum.inl a)
      (Sum.inr (Sum.inl ⟨s(a.val,u), hau⟩)) from ⟨u, hu, rfl⟩) h
  exact huS (mem_filter.mpr ⟨hu, ⟨⟨s(a.val,u), hau⟩, hr, Sym2.mem_mk_right _ _⟩⟩)

theorem no_target_reach {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)}
    (hsep : Menger.Separates (graph G A U B c) (sources G A B c) (targets G A B c) X)
    (q : B × Fin c) : ¬ Reach G A U B c X (Sum.inr (Sum.inr q)) := by
  rintro ⟨a, ha, p, hp⟩
  obtain ⟨v, hv, hvp⟩ := hsep a ha _ (by simp [targets]) p
  exact hp v hvp hv

/-- All capacity slots of a reachable branch must be in the separator. -/
theorem branch_slot_in_separator {G : SimpleGraph V} {A U B : Finset V} {c : ℕ}
    {X : Finset (Vertex G A B c)}
    (hsep : Menger.Separates (graph G A U B c) (sources G A B c) (targets G A B c) X)
    (b : B) (hb : b.val ∈ side G A U B c X) (j : Fin c) :
    Sum.inr (Sum.inr (b, j)) ∈ X := by
  by_contra h
  obtain ⟨_, e, he, hbe⟩ := mem_filter.mp hb
  exact no_target_reach hsep (b,j) (he.step hbe h)

end
end Cycle13.ReservoirPorts
