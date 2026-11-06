import Cycle12.TerminalTripleReduction
import Cycle12.TerminalMixedEdgeReduction

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def sixAttachmentFiber (G : SimpleGraph V) (f : Fin 6 ↪ V) (i : Fin 11) : Finset V :=
  univ.filter (SixAttachmentVertex G f i)

def sixAttachmentCapacity (i : Fin 11) : ℕ := if i.val<9 then 1 else 2

theorem six_independent_family_capacity : ∀ t : Fin 14,
    ∑ i∈sixAttachmentFamily t, sixAttachmentCapacity i ≤ 5 := by decide +kernel

theorem six_matching_family_capacity : ∀ t : Fin 4,
    ∑ i∈sixAttachmentFamily (Fin.castLE (by decide) t), sixAttachmentCapacity i ≤ 3 := by decide +kernel

/-- Repeated attachment types are impossible in a minimal counterexample:
pair types occur at most once, alternating triples at most twice. -/
theorem six_attachment_fiber_bound (G : SimpleGraph V) (ih : TerminalProperInduction G)
    (hbad : ¬∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard)
    (f : Fin 6 ↪ V) (i : Fin 11) :
    (sixAttachmentFiber G f i).card ≤ sixAttachmentCapacity i := by
  have htwin := (terminal_induction_twins_or_bound G ih).resolve_right hbad
  by_cases hi : i.val<9
  · rw [sixAttachmentCapacity,if_pos hi]
    apply Finset.card_le_one.mpr
    intro x hx y hy
    exact six_pair_attachment_unique htwin hi (mem_filter.mp hx).2 (mem_filter.mp hy).2
  · rw [sixAttachmentCapacity,if_neg hi]
    by_contra hn
    obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp (by omega :
      2<(sixAttachmentFiber G f i).card)
    exact hbad (terminal_induction_three_alternating_spokes G ih f (by omega) hxy hxz hyz
      (mem_filter.mp hx).2 (mem_filter.mp hy).2 (mem_filter.mp hz).2)

/-- Count actual vertices using the six core labels, disjointness-free
union bounds for the attachment fibers, and an explicitly bounded remainder. -/
theorem six_attachment_cover_order (G : SimpleGraph V) (f : Fin 6 ↪ V)
    (S : Finset (Fin 11)) (E : Finset V)
    (hfibers : ∀ i∈S, (sixAttachmentFiber G f i).card ≤ sixAttachmentCapacity i)
    (hcover : ∀ x, (∃ k, f k=x) ∨ (∃ i∈S, SixAttachmentVertex G f i x) ∨ x∈E) :
    Fintype.card V ≤ 6+(∑ i∈S, sixAttachmentCapacity i)+E.card := by
  let C : Finset V := univ.map f
  let T : Finset V := S.biUnion (sixAttachmentFiber G f)
  have hC : C.card=6 := by simp [C]
  have hT : T.card≤∑ i∈S, sixAttachmentCapacity i := by
    exact (Finset.card_biUnion_le).trans (sum_le_sum (fun i hi => hfibers i hi))
  have hsub : (univ:Finset V)⊆C∪T∪E := by
    intro x _
    rcases hcover x with ⟨k,rfl⟩ | ⟨i,hi,hx⟩ | hx
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_map.mpr ⟨k,mem_univ _,rfl⟩))))
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_biUnion.mpr
        ⟨i,hi,mem_filter.mpr ⟨mem_univ _,hx⟩⟩))))
    · exact mem_union.mpr (Or.inr hx)
  have hn := Finset.card_le_card hsub
  rw [card_univ] at hn
  have h₁ := Finset.card_union_le (C∪T) E
  have h₂ := Finset.card_union_le C T
  omega

theorem six_independent_frame_counterexample_order (G : SimpleGraph V)
    (ih : TerminalProperInduction G)
    (hbad : ¬∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard)
    (f : Fin 6 ↪ V) (hf : SixIndependentFrame G f) : Fintype.card V≤11 := by
  obtain ⟨t,ht⟩ := hf
  have hh := six_attachment_cover_order G f (sixAttachmentFamily t) ∅
    (fun i _ => six_attachment_fiber_bound G ih hbad f i)
    (fun x => (ht x).imp_right Or.inl)
  have hb := six_independent_family_capacity t
  simp only [card_empty] at hh
  omega

/-- Full neighborhoods force distinct exterior edge components to have
four distinct vertices; two such components are then removable together. -/
theorem six_edge_components_cover_pair (G : SimpleGraph V)
    (ih : TerminalProperInduction G)
    (hbad : ¬∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard)
    (f : Fin 6 ↪ V) {x y z w : V}
    (hxy : SixEdgeComponent G f x y) (hzw : SixEdgeComponent G f z w) : z=x ∨ z=y := by
  by_contra hn
  have hzx : z≠x := fun he => hn (Or.inl he)
  have hzy : z≠y := fun he => hn (Or.inr he)
  have hxx := hxy.1
  have hyy := hxy.2.1
  have hzz := hzw.1
  have hwx : w≠x := by
    intro he
    have hxz : G.Adj x z := by simpa only [he] using hzw.2.2.1.symm
    rcases (hxy.2.2.2.2.1 z).mp hxz with h | ⟨h,_⟩ | ⟨h,_⟩
    · exact hzy h
    · exact hzz 0 h
    · exact hzz 3 h
  have hwy : w≠y := by
    intro he
    have hyz : G.Adj y z := by simpa only [he] using hzw.2.2.1.symm
    rcases (hxy.2.2.2.2.2 z).mp hyz with h | ⟨h,_⟩ | ⟨h,_⟩
    · exact hzx h
    · exact hzz 0 h
    · exact hzz 3 h
  have hnodes : [x,y,z,w].Nodup := by
    have hxy' := hxy.2.2.1.ne
    have hzw' := hzw.2.2.1.ne
    simp [List.nodup_cons,hxy',hzw',Ne.symm hzx,Ne.symm hzy,Ne.symm hwx,Ne.symm hwy]
  exact hbad (terminal_induction_two_edge_components G ih f hxy hzw hnodes)

theorem six_matching_frame_counterexample_order (G : SimpleGraph V)
    (ih : TerminalProperInduction G)
    (hbad : ¬∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard)
    (f : Fin 6 ↪ V) (hf : SixMatchingFrame G f) : Fintype.card V≤11 := by
  obtain ⟨t,ht⟩ := hf
  have hb := six_matching_family_capacity t
  by_cases he : ∃ x y, SixEdgeComponent G f x y
  · obtain ⟨x,y,hxy⟩ := he
    have hcover : ∀ z, (∃ k, f k=z) ∨
        (∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i z) ∨
        z∈({x,y}:Finset V) := by
      intro z
      rcases ht z with h | h | ⟨w,hzw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by
          simpa only [mem_insert,mem_singleton] using six_edge_components_cover_pair G ih hbad f hxy hzw))
    have hh := six_attachment_cover_order G f _ {x,y}
      (fun i _ => six_attachment_fiber_bound G ih hbad f i) hcover
    have hpair : ({x,y}:Finset V).card≤2 := Finset.card_le_two
    omega
  · have hcover : ∀ z, (∃ k, f k=z) ∨
        (∃ i∈sixAttachmentFamily (Fin.castLE (by decide) t), SixAttachmentVertex G f i z) ∨
        z∈(∅:Finset V) := by
      intro z
      rcases ht z with h | h | ⟨w,hzw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact False.elim (he ⟨z,w,hzw⟩)
    have hh := six_attachment_cover_order G f _ ∅
      (fun i _ => six_attachment_fiber_bound G ih hbad f i) hcover
    simp only [card_empty] at hh
    omega

end
end Cycle12
