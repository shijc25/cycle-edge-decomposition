import Cycle12.Foundations.GraphCopyWitness

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem outside_copy_error_mean (G : SimpleGraph V) (U C : Finset V) (q : unitInterval)
    (v : V) (hv : v∉U) :
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).prob
      (fun ξ => v∉copiedSide T ξ (C∩T))) ≤
      ((neighborsIn G v (U\C)).card:ℝ)/((neighborsIn G v U).card:ℝ)+
        exp (-(q:ℝ)*(neighborsIn G v U).card) := by
  have hn : neighborsIn G v U\insert v C=neighborsIn G v (U\C) := by
    ext w
    simp only [neighborsIn,mem_sdiff,mem_filter,mem_insert]
    constructor
    · intro h
      exact ⟨⟨h.1.1,fun hc => h.2 (Or.inr hc)⟩,h.1.2⟩
    · intro h
      refine ⟨⟨h.1.1,h.2⟩,?_⟩
      rintro (rfl | hc)
      · exact hv h.1.1
      · exact h.1.2 hc
  have hh := neighborCopy_marked_error_mean G U (insert v C) q v
  simp only [mem_insert_self,ite_true,hn] at hh
  apply le_trans _ hh
  apply FiniteLaw.expect_mono_support
  intro T hmass
  have hT : T⊆U := by
    by_contra hn
    rw [subsetBernoulli_mass_not_subset U T q hn] at hmass
    exact lt_irrefl _ hmass
  have hvT : v∉T := fun h => hv (hT h)
  have he : insert v C∩T=C∩T := by ext w; simp [hvT]
  rw [he]
  apply le_of_eq
  congr 1
  funext ξ
  simp only [mem_insert_self,true_iff]

def outsideCopyMisses (X C T : Finset V) (ξ : V→Option V) : ℝ :=
  ((X\copiedSide T ξ (C∩T)).card:ℝ)

theorem outsideCopyMisses_expect (G : SimpleGraph V) (U X C : Finset V)
    (hdisj : Disjoint X U) (q : unitInterval) {δ : ℝ} (hδ : 0 < δ)
    (hdeg : ∀ v∈X, δ ≤ ((neighborsIn G v U).card:ℝ)) :
    (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).expect
      (outsideCopyMisses X C T)) ≤
      ((G.interedges X (U\C)).card:ℝ)/δ+exp (-(q:ℝ)*δ)*X.card := by
  have he : ∀ T ξ, outsideCopyMisses X C T ξ=∑ v∈X,
      if v∉copiedSide T ξ (C∩T) then (1:ℝ) else 0 := by
    intro T ξ
    have hf : X.filter (fun v => v∉copiedSide T ξ (C∩T))=X\copiedSide T ξ (C∩T) := by
      ext v; simp
    simp only [outsideCopyMisses,sum_boole,hf]
  change (subsetBernoulli U q).expect (fun T => (neighborCopyLaw G T).expect
    (fun ξ => outsideCopyMisses X C T ξ)) ≤ _
  simp_rw [he,FiniteLaw.expect_finset_sum]
  have hp : ∀ v∈X, (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).expect (fun ξ => if v∉copiedSide T ξ (C∩T) then (1:ℝ) else 0)) ≤
      ((neighborsIn G v (U\C)).card:ℝ)/δ+exp (-(q:ℝ)*δ) := by
    intro v hv
    have hbad := outside_copy_error_mean G U C q v (fun hu => Finset.disjoint_left.mp hdisj hv hu)
    have hpoint : ∀ T, (neighborCopyLaw G T).expect
        (fun ξ => if v∉copiedSide T ξ (C∩T) then (1:ℝ) else 0)=
        (neighborCopyLaw G T).prob (fun ξ => v∉copiedSide T ξ (C∩T)) := by
      intro T
      unfold FiniteLaw.prob
      congr 1
      funext ξ
      by_cases h : v∉copiedSide T ξ (C∩T) <;> simp [h]
    simp_rw [hpoint]
    apply hbad.trans
    have hd := hdeg v hv
    have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) (neighborsIn G v (U\C)).card) hδ hd
    have hexp : exp (-(q:ℝ)*(neighborsIn G v U).card) ≤ exp (-(q:ℝ)*δ) := by
      apply exp_le_exp.mpr
      nlinarith [q.2.1]
    linarith
  apply (sum_le_sum hp).trans_eq
  rw [sum_add_distrib,← sum_div,← Nat.cast_sum,← card_interedges_eq_sum_neighborsIn,
    sum_const,nsmul_eq_mul]
  ring

end
end Cycle13
