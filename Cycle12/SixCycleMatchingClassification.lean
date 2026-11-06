import Cycle12.SixCycleCommonHubs

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V}

def SixEdgeComponent (G : SimpleGraph V) (f : Fin 6 ↪ V) (x y : V) : Prop :=
  (∀ i, x≠f i) ∧ (∀ i, y≠f i) ∧ G.Adj x y ∧
    ((G.Adj x (f 0) ∧ G.Adj y (f 3)) ∨ (G.Adj x (f 3) ∧ G.Adj y (f 0))) ∧
    (∀ v, G.Adj x v ↔ v=y ∨ (v=f 0 ∧ G.Adj x (f 0)) ∨ (v=f 3 ∧ G.Adj x (f 3))) ∧
    (∀ v, G.Adj y v ↔ v=x ∨ (v=f 0 ∧ G.Adj y (f 0)) ∨ (v=f 3 ∧ G.Adj y (f 3)))

theorem full_neighbors_of_three_candidates {x y a b : V} (hxy : G.Adj x y)
    (hbound : ∀ v, G.Adj x v → v=y ∨ v=a ∨ v=b) :
    ∀ v, G.Adj x v ↔ v=y ∨ (v=a ∧ G.Adj x a) ∨ (v=b ∧ G.Adj x b) := by
  intro v
  constructor
  · intro hv
    rcases hbound v hv with he | he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨he,he ▸ hv⟩)
    · exact Or.inr (Or.inr ⟨he,he ▸ hv⟩)
  · rintro (rfl | ⟨rfl,h⟩ | ⟨rfl,h⟩)
    · exact hxy
    · exact h
    · exact h

/-- The existence of one exterior three-edge ear reduces all isolated
attachment types to one of four compatible families on the same core. -/
theorem six_ear_isolated_attachment_family
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    {x y : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i)
    (hxa : G.Adj x (f 0)) (hxy : G.Adj x y) (hyb : G.Adj y (f 3)) :
    ∃ t : Fin 4, ∀ z, (∀ k, z≠f k) →
      (∀ v, (∀ k, v≠f k) → ¬G.Adj z v) →
      ∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i z := by
  let S : Finset (Fin 11) := univ.filter (fun i => ∃ z, SixAttachmentVertex G f i z)
  have hallow : S⊆sixEarAllowed := by
    intro i hi
    obtain ⟨z,hz⟩ := (mem_filter.mp hi).2
    exact six_actual_ear_attachment_allowed f hcycle hshort hx hy hxa hxy hyb hz
  have hcomp : ∀ i∈S, ∀ j∈S, SixPairCompatible i j := by
    intro i hi j hj
    by_cases hij : i=j
    · subst j
      exact six_pair_compatible_refl i
    obtain ⟨z,hz⟩ := (mem_filter.mp hi).2
    obtain ⟨w,hw⟩ := (mem_filter.mp hj).2
    have hzw : z≠w := by
      intro he
      subst w
      exact hij (six_attachment_vertex_type_unique hz hw)
    apply six_actual_attachments_compatible f hcycle hshort hz.1 hw.1 hzw i j
    · intro k hk
      exact (six_attachment_vertex_adj_frame hz k).mpr hk
    · intro k hk
      exact (six_attachment_vertex_adj_frame hw k).mpr hk
  obtain ⟨t,ht⟩ := six_ear_family_cover S hallow hcomp
  refine ⟨t,?_⟩
  intro z hz hisolated
  obtain ⟨i,hi⟩ := six_isolated_attachment_type f hcycle hrobust hshort hz hisolated
  exact ⟨i,ht (by simpa only [S,mem_filter,mem_univ,true_and] using ⟨z,hi⟩),hi⟩

def SixIndependentFrame (G : SimpleGraph V) (f : Fin 6 ↪ V) : Prop :=
  ∃ t : Fin 14, ∀ x, (∃ k, f k=x) ∨
    ∃ i∈sixAttachmentFamily t, SixAttachmentVertex G f i x

def SixMatchingFrame (G : SimpleGraph V) (f : Fin 6 ↪ V) : Prop :=
  ∃ t : Fin 4, ∀ x, (∃ k, f k=x) ∨
    (∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i x) ∨
    ∃ y, SixEdgeComponent G f x y

variable [Fintype V] [DecidableEq V]

/-- Complete classification of a twin-free block with a six-cycle.
It permits arbitrary core chords, and specifies every exterior neighborhood
in the actual graph. Only a rotation, not a replacement, of the core is used. -/
theorem six_cycle_twin_free_classification (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (htwin : NoDegreeTwoTwins G)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7) :
    ∃ f : Fin 6 ↪ V, (∀ i, G.Adj (f i) (f (i+1))) ∧
      (∀ v, v∈c.support ↔ ∃ i, f i=v) ∧
      (SixIndependentFrame G f ∨ SixMatchingFrame G f) := by
  have hmatch := six_cycle_twin_free_exterior_matching G hconn hrobust htwin c hc hlen hshort
  by_cases hext : ∃ x y, x∉c.support ∧ y∉c.support ∧ G.Adj x y
  · obtain ⟨x,y,hx,hy,hxy⟩ := hext
    obtain ⟨f,hcycle,hsupport,hxa,hyb⟩ := six_cycle_choose_ear_frame
      G hconn hrobust c hc hlen hshort hx hy hxy
    have hout : ∀ z, z∉c.support → ∀ i, z≠f i := by
      intro z hz i he
      exact hz ((hsupport z).mpr ⟨i,he.symm⟩)
    have hcommon := six_cycle_matching_common_hubs G hconn hrobust c hc hlen hshort
      f hcycle hsupport hx hy hxa hxy hyb hmatch
    obtain ⟨t,ht⟩ := six_ear_isolated_attachment_family f hcycle hrobust hshort
      (hout x hx) (hout y hy) hxa hxy hyb
    refine ⟨f,hcycle,hsupport,Or.inr ⟨t,?_⟩⟩
    intro z
    by_cases hz : z∈c.support
    · exact Or.inl ((hsupport z).mp hz)
    by_cases hpartner : ∃ w, w∉c.support ∧ G.Adj z w
    · obtain ⟨w,hw,hzw⟩ := hpartner
      have hbound : ∀ {r s}, r∉c.support → s∉c.support → G.Adj r s →
          ∀ v, G.Adj r v → v=s ∨ v=f 0 ∨ v=f 3 := by
        intro r s hr hs hrs v hrv
        by_cases hv : v∈c.support
        · exact Or.inr (hcommon r s hr hs hrs v hv hrv)
        · exact Or.inl (hmatch r s v hr hs hv hrs hrv).symm
      have horient : (G.Adj z (f 0) ∧ G.Adj w (f 3)) ∨
          (G.Adj z (f 3) ∧ G.Adj w (f 0)) := by
        obtain ⟨a,ha,b,hb,hab,hza,hwb⟩ := six_cycle_external_edge_distinct_attachments
          G hconn hrobust c hc hlen hshort hz hw hzw
        have ha' := hcommon z w hz hw hzw a ha hza
        have hb' := hcommon w z hw hz hzw.symm b hb hwb
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact False.elim (hab rfl)
        · exact Or.inl ⟨hza,hwb⟩
        · exact Or.inr ⟨hza,hwb⟩
        · exact False.elim (hab rfl)
      exact Or.inr (Or.inr ⟨w,hout z hz,hout w hw,hzw,horient,
        full_neighbors_of_three_candidates hzw (hbound hz hw hzw),
        full_neighbors_of_three_candidates hzw.symm (hbound hw hz hzw.symm)⟩)
    · apply Or.inr ∘ Or.inl
      apply ht z (hout z hz)
      intro v hv hzv
      have hvc : v∉c.support := by
        intro hvc
        obtain ⟨i,hi⟩ := (hsupport v).mp hvc
        exact hv i hi.symm
      exact hpartner ⟨v,hvc,hzv⟩
  · obtain ⟨f,hcycle,hsupport⟩ := six_cycle_frame hc hlen
    refine ⟨f,hcycle,hsupport,Or.inl ?_⟩
    apply six_cycle_independent_exterior_classification f hcycle hrobust hshort
    intro x y hx hy hxy
    have hx' : x∉c.support := by
      intro h
      obtain ⟨i,hi⟩ := (hsupport x).mp h
      exact hx i hi.symm
    have hy' : y∉c.support := by
      intro h
      obtain ⟨i,hi⟩ := (hsupport y).mp h
      exact hy i hi.symm
    exact hext ⟨x,y,hx',hy',hxy⟩

end
end Cycle12
