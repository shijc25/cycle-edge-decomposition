import Cycle12.ContractedEdgeUniqueness12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I L : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- An edge of the union can belong only to its own endpoint-label class. -/
theorem classwise_union_adj (G : SimpleGraph V) (label : V → L)
    (R : Sym2 L → SimpleGraph V) (hR : ∀ e,R e ≤ edgeLabelGraph G label e) (x y : V) :
    (⨆ e,R e).Adj x y ↔ (R s(label x,label y)).Adj x y := by
  rw [iSup_adj]
  constructor
  · rintro ⟨e,he⟩
    have hlabel := (hR e he).2
    exact hlabel ▸ he
  · exact fun h => ⟨_,h⟩

/-- All independently prepared crossing classes can be united into one
actual simple quotient. The hypotheses are local outputs of the two
pairing passes and the original matching-group partition. -/
theorem classwise_contraction_unique (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (R : Sym2 (Option I) → SimpleGraph V)
    (hR : ∀ e,R e ≤ edgeLabelGraph G (blockLabel A) e)
    (hi : ∀ i,R s(some i,some i)=⊥)
    (hc : ∀ i j,i ≠ j → (R s(some i,some j)).edgeSet.ncard ≤ 1)
    (ho : ∀ i v,v∉blockUnion A → (R s(some i,none)).degree v ≤ 1) :
    let H := ⨆ e,R e
    H ≤ G ∧ (∀ {x y},H.Adj x y → contractVertex A x ≠ contractVertex A y) ∧
      Set.InjOn (Sym2.map (contractVertex A)) H.edgeSet := by
  dsimp only
  have hsub : (⨆ e,R e) ≤ G := by
    intro x y hxy
    obtain ⟨e,he⟩ := iSup_adj.mp hxy
    exact (hR e he).1
  refine ⟨hsub,?_⟩
  apply contracted_retained_edges (⨆ e,R e) A hd
  · intro i x y hx hy hxy
    have hx' := (blockLabel_eq_some A hd x i).mpr hx
    have hy' := (blockLabel_eq_some A hd y i).mpr hy
    have hh := (classwise_union_adj G (blockLabel A) R hR x y).mp hxy
    rw [hx',hy',hi i] at hh
    exact hh
  · intro i j hij e he f hf
    have hclass (d : Sym2 V)
        (hd : d∈(edgeLabelGraph (⨆ e,R e) (blockLabel A) s(some i,some j)).edgeSet) :
        d∈(R s(some i,some j)).edgeSet := by
      induction d using Sym2.inductionOn with
      | _ x y =>
        have hh := (classwise_union_adj G (blockLabel A) R hR x y).mp hd.1
        exact hd.2 ▸ hh
    exact Set.ncard_le_one_iff_subsingleton.mp (hc i j hij) (hclass e he) (hclass f hf)
  · intro i v hv x hx y hy
    have hv' := (blockLabel_eq_none A v).mpr hv
    have hneighbor (u : V) (hu : (⨆ e,R e).Adj v u ∧ u∈A i) :
        u∈(R s(some i,none)).neighborSet v := by
      have hh := (classwise_union_adj G (blockLabel A) R hR v u).mp hu.1
      rw [hv',(blockLabel_eq_some A hd u i).mpr hu.2,Sym2.eq_swap] at hh
      exact hh
    have hh := ho i v hv
    rw [←ncard_neighborSet] at hh
    exact Set.ncard_le_one_iff_subsingleton.mp hh (hneighbor x hx) (hneighbor y hy)

end
end Cycle12
