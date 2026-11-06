import Cycle12.SixAttachmentCompatibility

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V}

def SixAttachmentVertex (G : SimpleGraph V) (f : Fin 6 ↪ V) (i : Fin 11) (x : V) : Prop :=
  (∀ k, x≠f k) ∧ ∀ v, G.Adj x v ↔ ∃ k∈sixAttachment i, f k=v

theorem six_attachment_vertex_adj_frame {f : Fin 6 ↪ V} {i : Fin 11} {x : V}
    (hx : SixAttachmentVertex G f i x) (k : Fin 6) :
    G.Adj x (f k) ↔ k∈sixAttachment i := by
  rw [hx.2]
  simp only [f.injective.eq_iff,exists_eq_right]

theorem six_attachment_vertex_type_unique {f : Fin 6 ↪ V} {i j : Fin 11} {x : V}
    (hi : SixAttachmentVertex G f i x) (hj : SixAttachmentVertex G f j x) : i=j := by
  apply six_attachment_injective
  ext k
  exact (six_attachment_vertex_adj_frame hi k).symm.trans (six_attachment_vertex_adj_frame hj k)

/-- Every isolated exterior vertex is assigned one of the eleven exact
full-neighborhood types. No order bound is assumed. -/
theorem six_isolated_attachment_type (f : Fin 6 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7) {x : V} (hx : ∀ i, x≠f i)
    (hisolated : ∀ v, (∀ i, v≠f i) → ¬G.Adj x v) :
    ∃ i, SixAttachmentVertex G f i x := by
  let S : Finset (Fin 6) := univ.filter (fun i => G.Adj x (f i))
  have htwo : ∃ i∈S, ∃ j∈S, i≠j := by
    obtain ⟨i,j,hij,hi,hj⟩ := six_frame_isolated_two_neighbors f hrobust hx hisolated
    exact ⟨i,by simpa only [S,mem_filter,mem_univ,true_and] using hi,
      j,by simpa only [S,mem_filter,mem_univ,true_and] using hj,hij⟩
  have hind : ∀ i, i∈S → i+1∉S := by
    intro i hi hj
    exact six_cycle_no_consecutive_neighbors f hcycle hshort hx i
      (mem_filter.mp hi).2 (mem_filter.mp hj).2
  obtain ⟨i,hi⟩ := six_attachment_complete S htwo hind
  refine ⟨i,hx,?_⟩
  intro v
  rw [←hi]
  constructor
  · intro hv
    have hcover : ∃ k, f k=v := by
      by_contra hn
      exact hisolated v (fun k he => hn ⟨k,he.symm⟩) hv
    obtain ⟨k,rfl⟩ := hcover
    exact ⟨k,by simpa only [S,mem_filter,mem_univ,true_and] using hv,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact (mem_filter.mp hk).2

/-- One of fourteen finite families contains the attachment types of all
isolated vertices outside this particular six-cycle. The core need not be
reselected, even when exterior edge components are also present. -/
theorem six_isolated_attachment_family (f : Fin 6 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7) :
    ∃ t : Fin 14, ∀ x, (∀ k, x≠f k) →
      (∀ v, (∀ k, v≠f k) → ¬G.Adj x v) →
      ∃ i∈sixAttachmentFamily t, SixAttachmentVertex G f i x := by
  let S : Finset (Fin 11) := univ.filter (fun i => ∃ x, SixAttachmentVertex G f i x)
  have hcomp : ∀ i∈S, ∀ j∈S, SixPairCompatible i j := by
    intro i hi j hj
    by_cases hij : i=j
    · subst j
      exact six_pair_compatible_refl i
    obtain ⟨x,hx⟩ := (mem_filter.mp hi).2
    obtain ⟨y,hy⟩ := (mem_filter.mp hj).2
    have hxy : x≠y := by
      intro he
      subst y
      exact hij (six_attachment_vertex_type_unique hx hy)
    apply six_actual_attachments_compatible f hcycle hshort hx.1 hy.1 hxy i j
    · intro k hk
      exact (six_attachment_vertex_adj_frame hx k).mpr hk
    · intro k hk
      exact (six_attachment_vertex_adj_frame hy k).mpr hk
  obtain ⟨t,ht⟩ := six_compatible_family_cover S hcomp
  refine ⟨t,?_⟩
  intro x hx hisolated
  obtain ⟨i,hi⟩ := six_isolated_attachment_type f hcycle hrobust hshort hx hisolated
  exact ⟨i,ht (by simpa only [S,mem_filter,mem_univ,true_and] using ⟨x,hi⟩),hi⟩

/-- Complete infinite classification when the exterior of the chosen
six-cycle is independent, including arbitrary edges between core vertices. -/
theorem six_cycle_independent_exterior_classification (f : Fin 6 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hout : ∀ x y, (∀ k, x≠f k) → (∀ k, y≠f k) → ¬G.Adj x y) :
    ∃ t : Fin 14, ∀ x, (∃ k, f k=x) ∨
      ∃ i∈sixAttachmentFamily t, SixAttachmentVertex G f i x := by
  obtain ⟨t,ht⟩ := six_isolated_attachment_family f hcycle hrobust hshort
  refine ⟨t,?_⟩
  intro x
  by_cases hx : ∃ k, f k=x
  · exact Or.inl hx
  · have hxo : ∀ k, x≠f k := fun k he => hx ⟨k,he.symm⟩
    exact Or.inr (ht x hxo (fun v hv => hout x v hxo hv))

end
end Cycle12
