import Cycle12.Foundations.FiniteProductLaw
import Cycle12.Foundations.BernoulliSymmetry
import Cycle12.Foundations.SamplingGeometry

namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def optionChoices (N : Finset V) : Finset (Option V) :=
  if N.Nonempty then N.map ⟨Option.some,Option.some_injective V⟩ else {none}

theorem optionChoices_nonempty (N : Finset V) : (optionChoices N).Nonempty := by
  unfold optionChoices
  split_ifs with h
  · exact h.map
  · exact singleton_nonempty _

def uniformNeighborChoice (N : Finset V) : FiniteLaw (Option V) :=
  FiniteLaw.uniformOn (optionChoices N) (optionChoices_nonempty N)

theorem uniformNeighborChoice_expect (N : Finset V) (f : Option V→ℝ) :
    (uniformNeighborChoice N).expect f=
      if N.Nonempty then (∑ v∈N, f (some v))/(N.card:ℝ) else f none := by
  rw [uniformNeighborChoice,FiniteLaw.uniformOn_expect]
  by_cases h : N.Nonempty
  · simp only [optionChoices,h,ite_true,sum_map,card_map,Function.Embedding.coeFn_mk]
  · simp [optionChoices,h]

theorem uniformNeighborChoice_bad (N B : Finset V) :
    (uniformNeighborChoice N).prob (fun o => ∃ v∈B, o=some v)=
      ∑ v∈B, markedChoiceWeight N N v := by
  rw [FiniteLaw.prob,uniformNeighborChoice_expect]
  have he : ∀ v : V, (∃ w∈B, some v=some w) ↔ v∈B := by intro v; simp
  simp_rw [he]
  by_cases h : N.Nonempty
  · rw [if_pos h]
    simp only [sum_boole,filter_mem_eq_inter,markedChoiceWeight,inter_self]
    rw [← sum_filter]
    simp only [filter_mem_eq_inter,sum_const,nsmul_eq_mul]
    rw [inter_comm N B]
    ring
  · have hz : N=∅ := not_nonempty_iff_eq_empty.mp h
    subst N
    simp [markedChoiceWeight]

theorem uniformNeighborChoice_none (N : Finset V) :
    (uniformNeighborChoice N).prob (fun o => o=none)=if N=∅ then 1 else 0 := by
  rw [FiniteLaw.prob,uniformNeighborChoice_expect]
  by_cases h : N.Nonempty
  · have hn := h.ne_empty
    simp [h,hn]
  · simp [h,not_nonempty_iff_eq_empty.mp h]

def neighborCopyLaw (G : SimpleGraph V) (T : Finset V) : FiniteLaw (V→Option V) :=
  FiniteLaw.independent (fun v => uniformNeighborChoice (neighborsIn G v T))

def copiedSide (T : Finset V) (ξ : V→Option V) (A : Finset V) : Finset V :=
  univ.filter (fun v => if v∈T then v∈A else ∃ w, ξ v=some w ∧ w∈A)

theorem copiedSide_marked (T : Finset V) (ξ : V→Option V) (A : Finset V) (hA : A⊆T) :
    copiedSide T ξ A∩T=A := by
  ext v
  by_cases hv : v∈T
  · simp [copiedSide,hv]
  · have ha : v∉A := fun h => hv (hA h)
    simp [hv,ha]

theorem neighborCopyLaw_marginal (G : SimpleGraph V) (T : Finset V) (v : V) (f : Option V→ℝ) :
    (neighborCopyLaw G T).expect (fun ξ => f (ξ v))=
      (uniformNeighborChoice (neighborsIn G v T)).expect f :=
  FiniteLaw.independent_expect_eval _ _ _

end
end Cycle13
