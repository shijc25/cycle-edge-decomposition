import Cycle12.RectangularIncidence
import Cycle12.GraphDependencySquares

namespace Cycle12
open Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem bipartite_column_count (G : SimpleGraph V) (A : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (Aᶜ:Set V)) (v : V) :
    incidenceColumnCount (fun i : A => G.neighborFinset i.val) v=
      if v∈A then 0 else G.degree v := by
  by_cases hv : v∈A
  · rw [if_pos hv]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hadj := (G.mem_neighborFinset i.val v).mp (mem_filter.mp hi).2
    have hnot := hG.mem_of_mem_adj i.property hadj
    exact hnot hv
  · rw [if_neg hv,← G.card_neighborFinset_eq_degree v]
    apply card_bij (fun i _ => i.val)
    · intro i hi
      exact (G.mem_neighborFinset v i.val).mpr
        ((G.mem_neighborFinset i.val v).mp (mem_filter.mp hi).2).symm
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro w hw
      have hadj := (G.mem_neighborFinset v w).mp hw
      have hwA : w∈A := hG.mem_of_mem_adj' hv hadj.symm
      refine ⟨⟨w,hwA⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
      exact (G.mem_neighborFinset w v).mpr hadj.symm

theorem bipartite_left_degree_sum (G : SimpleGraph V) (A : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (Aᶜ:Set V)) :
    (∑ i : A, (G.degree i.val:ℝ))=(Fintype.card G.edgeSet:ℝ) := by
  have hG' : G.IsBipartiteWith (A:Set V) ((Aᶜ:Finset V):Set V) := by
    simpa only [Finset.coe_compl] using hG
  have hh := G.isBipartiteWith_sum_degrees_eq_card_edges hG'
  have hs : (∑ i : A, G.degree i.val)=∑ v ∈ A, G.degree v := by
    simpa using sum_attach A (fun v => G.degree v)
  rw [← hs] at hh
  have he : G.edgeFinset.card=Fintype.card G.edgeSet := by
    simp only [SimpleGraph.edgeFinset,Set.toFinset_card]
  rw [he] at hh
  exact_mod_cast hh

/-- The rectangular dependency bound for a genuine simple bipartite graph.
The opposite side can have arbitrarily many vertices. -/
theorem bipartite_rectangle_degree_square_bound (G : SimpleGraph V) (A : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (Aᶜ:Set V)) (C : ℝ)
    (hC : 0<C) (hu : (A.card:ℝ)≤C) (hrow : ∀ v∈A, (G.degree v:ℝ)≤C) :
    (∑ v, (G.degree v:ℝ)^2) ≤
      C*(Fintype.card G.edgeSet:ℝ)+(Fintype.card G.edgeSet:ℝ)^2/C := by
  have hh := rectangular_incidence_square_bound (fun i : A => G.neighborFinset i.val) C hC
    (by simpa only [Fintype.card_coe] using hu)
    (fun i => by rw [G.card_neighborFinset_eq_degree]; exact hrow i.val i.property)
  simp only [G.card_neighborFinset_eq_degree,bipartite_left_degree_sum G A hG] at hh
  have hid : (∑ i : A, (G.degree i.val:ℝ)^2)+
      (∑ v, (incidenceColumnCount (fun i : A => G.neighborFinset i.val) v:ℝ)^2)=
        ∑ v, (G.degree v:ℝ)^2 := by
    rw [show (∑ i : A, (G.degree i.val:ℝ)^2)=∑ v∈A, (G.degree v:ℝ)^2 by
      simpa using sum_attach A (fun v => (G.degree v:ℝ)^2)]
    have hc : (∑ v, (incidenceColumnCount (fun i : A => G.neighborFinset i.val) v:ℝ)^2)=
        ∑ v ∈ Aᶜ, (G.degree v:ℝ)^2 := by
      rw [← Finset.sum_ite_mem_eq (Aᶜ) (fun v => (G.degree v:ℝ)^2)]
      apply sum_congr rfl
      intro v _
      rw [bipartite_column_count G A hG]
      by_cases hv : v∈A <;> simp [hv]
    rw [hc]
    exact sum_add_sum_compl A (fun v => (G.degree v:ℝ)^2)
  rwa [hid] at hh

theorem bipartite_rectangle_janson (G : SimpleGraph V) (A : Finset V)
    (hG : G.IsBipartiteWith (A:Set V) (Aᶜ:Set V)) (C : ℝ)
    (hC : 0<C) (hu : (A.card:ℝ)≤C) (hrow : ∀ v∈A, (G.degree v:ℝ)≤C)
    (p : unitInterval) (hm : 0<(Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)
    (tau : ℝ) (ht0 : 0≤tau) (ht1 : tau≤1) :
    (subsetBernoulli (univ:Finset V) p).prob
        (fun S => (sampledFinsetEdgeCount G S:ℝ)≤tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)) ≤
      Real.exp (-fullJansonPhi tau*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2)^2/
        ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
          (C*(Fintype.card G.edgeSet:ℝ)+(Fintype.card G.edgeSet:ℝ)^2/C)*(p:ℝ)^3)) :=
  graph_janson_square_lower_tail G p hm _
    (bipartite_rectangle_degree_square_bound G A hG C hC hu hrow) tau ht0 ht1

end
end Cycle12
