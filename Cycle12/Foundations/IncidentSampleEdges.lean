import Cycle12.Foundations.GraphJanson
import Cycle12.Foundations.BernoulliMiss
import Cycle12.Foundations.FiniteSupport

namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def incidentSampleEdges (G : SimpleGraph V) (U : Finset V) : Finset G.edgeSet :=
  univ.filter (fun e => ∃ v∈U, v∈e.val)

def incidentEdgeCount (G : SimpleGraph V) (U : Finset V) : ℕ := (incidentSampleEdges G U).card

theorem incidentSampleEdges_insert (G : SimpleGraph V) (U : Finset V) (v : V) :
    incidentSampleEdges G (insert v U)=incidentSampleEdges G U∪
      univ.filter (fun e : G.edgeSet => v∈e.val) := by
  ext e
  simp only [incidentSampleEdges,mem_filter,mem_univ,true_and,mem_union,mem_insert]
  constructor
  · rintro ⟨w,rfl | hw,he⟩
    · exact Or.inr he
    · exact Or.inl ⟨w,hw,he⟩
  · rintro (⟨w,hw,he⟩ | he)
    · exact ⟨w,Or.inr hw,he⟩
    · exact ⟨v,Or.inl rfl,he⟩

theorem incidentEdgeCount_increment (G : SimpleGraph V) (U : Finset V) (v : V) :
    0 ≤ (incidentEdgeCount G (insert v U):ℝ)-incidentEdgeCount G U ∧
      (incidentEdgeCount G (insert v U):ℝ)-incidentEdgeCount G U ≤ (G.degree v:ℝ) := by
  have hl := card_le_card (subset_union_left (s₁:=incidentSampleEdges G U)
    (s₂:=univ.filter (fun e : G.edgeSet => v∈e.val)))
  have hu := card_union_le (incidentSampleEdges G U) (univ.filter (fun e : G.edgeSet => v∈e.val))
  rw [← incidentSampleEdges_insert] at hl hu
  rw [incident_edges_card G v] at hu
  have hlR : (incidentEdgeCount G U:ℝ) ≤ incidentEdgeCount G (insert v U) := by exact_mod_cast hl
  have huR : (incidentEdgeCount G (insert v U):ℝ) ≤ incidentEdgeCount G U+G.degree v := by
    exact_mod_cast hu
  constructor <;> linarith

theorem incidentEdgeCount_eq_sum (G : SimpleGraph V) (U : Finset V) :
    (incidentEdgeCount G U:ℝ)=∑ e : G.edgeSet,
      if ¬(edgeVertexSet G e∩U=∅) then (1:ℝ) else 0 := by
  have he : ∀ e : G.edgeSet, (∃ v∈U, v∈e.val) ↔ ¬(edgeVertexSet G e∩U=∅) := by
    intro e
    constructor
    · rintro ⟨v,hvU,hve⟩ hzero
      have hv : v∈edgeVertexSet G e∩U := mem_inter.mpr ⟨by simpa [edgeVertexSet] using hve,hvU⟩
      simpa only [hzero,notMem_empty] using hv
    · intro hn
      obtain ⟨v,hv⟩ := nonempty_iff_ne_empty.mpr hn
      exact ⟨v,(mem_inter.mp hv).2,by simpa [edgeVertexSet] using (mem_inter.mp hv).1⟩
  simp only [incidentEdgeCount,incidentSampleEdges,he,sum_boole]

theorem subsetBernoulli_univ (p : unitInterval) :
    subsetBernoulli (univ:Finset V) p=bernoulliSubset p := by
  unfold subsetBernoulli bernoulliSubset
  congr 1
  funext S
  simp

theorem incidentEdgeCount_expect (G : SimpleGraph V) (p : unitInterval) :
    (bernoulliSubset p).expect (fun S => (incidentEdgeCount G S:ℝ))=
      (2*(p:ℝ)-(p:ℝ)^2)*(Fintype.card G.edgeSet:ℝ) := by
  simp_rw [incidentEdgeCount_eq_sum,FiniteLaw.expect_sum]
  have he : ∀ e : G.edgeSet, (bernoulliSubset p).expect
      (fun S => if ¬(edgeVertexSet G e∩S=∅) then (1:ℝ) else 0)=1-(1-(p:ℝ))^2 := by
    intro e
    have hh := (bernoulliSubset (V:=V) p).prob_compl (fun S => edgeVertexSet G e∩S=∅)
    rw [← subsetBernoulli_univ p,subsetBernoulli_miss _ _ _ (subset_univ _),edgeVertexSet_card] at hh
    rw [subsetBernoulli_univ] at hh
    convert hh using 1
    unfold FiniteLaw.prob
    congr 1
    funext S
    by_cases h : edgeVertexSet G e∩S=∅ <;> simp [h]
  simp_rw [he]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  ring

theorem degree_square_sum_le (G : SimpleGraph V) {r : ℝ}
    (hdeg : ∀ v, (G.degree v:ℝ) ≤ r) :
    (∑ v : V, (G.degree v:ℝ)^2) ≤ 2*(Fintype.card G.edgeSet:ℝ)*r := by
  have hs : (∑ v : V, (G.degree v:ℝ))=2*(Fintype.card G.edgeSet:ℝ) := by
    have hh := G.sum_degrees_eq_twice_card_edges
    have hr := congrArg (fun n : ℕ => (n:ℝ)) hh
    simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat] at hr
    simpa only [SimpleGraph.edgeFinset,Set.toFinset_card] using hr
  calc
    _ ≤ ∑ v : V, r*(G.degree v:ℝ) := by
      apply sum_le_sum
      intro v _
      have hh := mul_le_mul_of_nonneg_right (hdeg v) (Nat.cast_nonneg (α:=ℝ) (G.degree v))
      nlinarith
    _ = r*∑ v : V, (G.degree v:ℝ) := (mul_sum _ _ _).symm
    _ = _ := by rw [hs]; ring

end
end Cycle13
