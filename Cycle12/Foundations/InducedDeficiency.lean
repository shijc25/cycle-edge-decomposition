import Cycle12.Foundations.EvenRemainder
import Cycle12.Foundations.GraphBranchCut

/-! Exact degree accounting across an induced subgraph boundary, and the
Eulerian deficiency bound after bounded-degree parity correction. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem induced_degree_add_cut (G : SimpleGraph V) (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v + (cutGraph G S).degree v.val = G.degree v.val := by
  have hu : G.neighborSet v.val =
      Subtype.val '' ((G.induce (S : Set V)).neighborSet v) ∪
        (cutGraph G S).neighborSet v.val := by
    ext w
    constructor
    · intro hw
      by_cases hs : w ∈ S
      · exact Or.inl ⟨⟨w,hs⟩,hw,rfl⟩
      · exact Or.inr ⟨hw,Or.inl ⟨v.property,hs⟩⟩
    · rintro (⟨w,hw,rfl⟩ | hw)
      · exact hw
      · exact hw.1
  have hd : Disjoint (Subtype.val '' ((G.induce (S : Set V)).neighborSet v))
      ((cutGraph G S).neighborSet v.val) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨x,hx,rfl⟩ hw
    rcases hw.2 with hw | hw
    · exact hw.2 x.property
    · exact hw.1 v.property
  simp only [← ncard_neighborSet]
  rw [hu,Set.ncard_union_eq hd,Set.ncard_image_of_injective _ Subtype.val_injective]

theorem induced_deficiency_le_cut_of_loss (G : SimpleGraph V) (S : Finset V)
    (H : SimpleGraph S) {d k : ℕ}
    (hmin : ∀ v∈S, d+k ≤ G.degree v)
    (hloss : ∀ v, (G.induce (S : Set V)).degree v ≤ H.degree v+k) :
    degreeDeficiency H d ≤ cutSize G S := by
  have hp : ∀ v : S, d-H.degree v ≤ (cutGraph G S).degree v.val := by
    intro v
    have hb := induced_degree_add_cut G S v
    have hm := hmin v v.property
    have hl := hloss v
    simp only [← ncard_neighborSet] at hb hm hl ⊢
    omega
  calc
    degreeDeficiency H d ≤ ∑ v : S, (cutGraph G S).degree v.val :=
      sum_le_sum (fun v _ => hp v)
    _ = ∑ v∈S, (cutGraph G S).degree v :=
      (Finset.sum_subtype (p := fun v : V => v∈S) S
        (fun _ => Iff.rfl) (fun v => (cutGraph G S).degree v)).symm
    _ = cutSize G S := (cutSize_eq_sum G S).symm

theorem exists_even_induced_deficiency (G : SimpleGraph V) (S : Finset V)
    (T : SimpleGraph S) {d k : ℕ}
    (hmin : ∀ v ∈ S, d+k ≤ G.degree v)
    (hTG : T ≤ G.induce (S : Set V)) (hT : T.Connected)
    (hdeg : ∀ v, T.degree v ≤ k) :
    ∃ H : SimpleGraph S, H ≤ G.induce (S : Set V) ∧
      (∀ v, Even (H.degree v)) ∧ degreeDeficiency H d ≤ cutSize G S := by
  obtain ⟨H,hHG,heven,hloss⟩ :=
    exists_even_remainder_degree_bound (G.induce (S : Set V)) T hTG hT hdeg
  refine ⟨H,hHG,heven,?_⟩
  have hp : ∀ v : S, d-H.degree v ≤ (cutGraph G S).degree v.val := by
    intro v
    have hb := induced_degree_add_cut G S v
    have hm := hmin v v.property
    have hl := hloss v
    simp only [← ncard_neighborSet] at hb hm hl ⊢
    omega
  calc
    degreeDeficiency H d ≤ ∑ v : S, (cutGraph G S).degree v.val :=
      sum_le_sum (fun v _ => hp v)
    _ = ∑ v ∈ S, (cutGraph G S).degree v :=
      (Finset.sum_subtype (p := fun v : V => v ∈ S) S
        (fun _ => Iff.rfl) (fun v => (cutGraph G S).degree v)).symm
    _ = cutSize G S := (cutSize_eq_sum G S).symm

end
end Cycle13
