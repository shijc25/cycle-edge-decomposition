import Cycle12.Foundations.UniformNeighborChoice
import Cycle12.Foundations.BernoulliMiss
import Cycle12.Foundations.FiniteSupport

namespace Cycle13
open Finset SimpleGraph
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem markedNeighbor_bad_mean (W N B : Finset V) (p : unitInterval)
    (hNW : N⊆W) (hBN : B⊆N) :
    (subsetBernoulli W p).expect (fun T => (uniformNeighborChoice (N∩T)).prob
      (fun o => ∃ v∈B, o=some v)) ≤ (B.card:ℝ)/(N.card:ℝ) := by
  simp_rw [uniformNeighborChoice_bad]
  have he : ∀ T v, markedChoiceWeight (N∩T) (N∩T) v=markedChoiceWeight N T v := by
    intro T v; simp only [markedChoiceWeight,inter_self]
  simp_rw [he]
  exact markedChoiceWeight_bad_mean W N B p hNW hBN

theorem markedNeighbor_none_mean (W N : Finset V) (p : unitInterval) (hNW : N⊆W) :
    (subsetBernoulli W p).expect (fun T => (uniformNeighborChoice (N∩T)).prob
      (fun o => o=none)) ≤ Real.exp (-(p:ℝ)*N.card) := by
  simp_rw [uniformNeighborChoice_none]
  have he : (subsetBernoulli W p).expect (fun T => if N∩T=∅ then 1 else 0)=
      (subsetBernoulli W p).prob (fun T => N∩T=∅) := by
    unfold FiniteLaw.prob; congr 1; funext T
    by_cases h : N∩T=∅ <;> simp [h]
  rw [he]
  exact subsetBernoulli_miss_le W N p hNW

theorem uniformNeighborChoice_some_support (N : Finset V) (v : V)
    (h : 0<(uniformNeighborChoice N).mass (some v)) : v∈N := by
  by_contra hv
  by_cases hN : N.Nonempty
  · simp [uniformNeighborChoice,FiniteLaw.uniformOn,optionChoices,hN,hv] at h
  · simp [uniformNeighborChoice,FiniteLaw.uniformOn,optionChoices,hN] at h

def copiedVertexError (T A : Finset V) (v : V) (o : Option V) : Prop :=
  v∉T ∧ ¬(v∈A ↔ ∃ w, o=some w ∧ w∈A∩T)

theorem neighborCopy_error_marginal (G : SimpleGraph V) (T A : Finset V) (v : V) :
    (neighborCopyLaw G T).prob (fun ξ => ¬(v∈A ↔ v∈copiedSide T ξ (A∩T)))=
      (uniformNeighborChoice (neighborsIn G v T)).prob (copiedVertexError T A v) := by
  have he : ∀ ξ : V→Option V, ¬(v∈A ↔ v∈copiedSide T ξ (A∩T)) ↔
      copiedVertexError T A v (ξ v) := by
    intro ξ
    by_cases hv : v∈T <;> simp [copiedVertexError,copiedSide,hv]
  unfold FiniteLaw.prob
  simp_rw [he]
  convert neighborCopyLaw_marginal G T v
    (fun o => if copiedVertexError T A v o then (1:ℝ) else 0) using 1
    <;> congr 1 <;> funext ξ <;> split_ifs <;> rfl

theorem uniformNeighborChoice_error_bound (N T A : Finset V) (v : V) :
    (uniformNeighborChoice (N∩T)).prob (copiedVertexError T A v) ≤
      (uniformNeighborChoice (N∩T)).prob
        (fun o => ∃ w∈(if v∈A then N\A else N∩A), o=some w)+
      if v∈A then (uniformNeighborChoice (N∩T)).prob (fun o => o=none) else 0 := by
  let B := if v∈A then N\A else N∩A
  have hevent : ∀ o, 0<(uniformNeighborChoice (N∩T)).mass o →
      copiedVertexError T A v o → (∃ w∈B, o=some w) ∨ (v∈A ∧ o=none) := by
    intro o ho herr
    rcases herr with ⟨hvT,herr⟩
    cases o with
    | none =>
      right
      have hvA : v∈A := by simpa using herr
      exact ⟨hvA,rfl⟩
    | some w =>
      have hw := uniformNeighborChoice_some_support (N∩T) w ho
      obtain ⟨hwN,hwT⟩ := mem_inter.mp hw
      left
      refine ⟨w,?_,rfl⟩
      by_cases hvA : v∈A
      · have hwA : w∉A := by simpa [hvA,hwT] using herr
        simpa [B,hvA] using (mem_sdiff.mpr ⟨hwN,hwA⟩)
      · have hwA : w∈A := by simpa [hvA,hwT] using herr
        simpa [B,hvA] using (mem_inter.mpr ⟨hwN,hwA⟩)
  apply (FiniteLaw.prob_mono_support _ hevent).trans
  have hh := (uniformNeighborChoice (N∩T)).prob_union_le
    (fun o => ∃ w∈B, o=some w) (fun o => v∈A ∧ o=none)
  by_cases hv : v∈A
  · simpa only [hv,true_and,ite_true,B] using hh
  · simpa only [hv,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const,add_zero,B] using hh

theorem copiedVertexError_mean (W N A : Finset V) (p : unitInterval)
    (hNW : N⊆W) (v : V) :
    (subsetBernoulli W p).expect (fun T =>
      (uniformNeighborChoice (N∩T)).prob (copiedVertexError T A v)) ≤
    (((if v∈A then N\A else N∩A).card:ℕ):ℝ)/(N.card:ℝ)+
      if v∈A then Real.exp (-(p:ℝ)*N.card) else 0 := by
  apply ((subsetBernoulli W p).expect_mono
    (fun T => uniformNeighborChoice_error_bound N T A v)).trans
  rw [FiniteLaw.expect_add]
  have hB : (if v∈A then N\A else N∩A)⊆N := by split_ifs <;> aesop
  have hb := markedNeighbor_bad_mean W N (if v∈A then N\A else N∩A) p hNW hB
  by_cases hv : v∈A
  · simp only [hv,ite_true]
    have hn := markedNeighbor_none_mean W N p hNW
    simp only [hv,ite_true] at hb
    linarith
  · simp only [hv,ite_false,FiniteLaw.expect_const,add_zero]
    simpa only [hv,ite_false] using hb

end
end Cycle13
