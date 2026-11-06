import Cycle12.MajorityFullError
import Cycle12.Foundations.OutsideCopyError

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_outside_majority_error (G : SimpleGraph V) (U C : Finset V)
    (hU : U.Nonempty) {v : V} (hv : v∉U) {k : ℕ} (hk : k ≤ U.card)
    {delta lambda Kfull : ℝ} (hdelta : 2 < delta)
    (hdeg : delta ≤ ((neighborsIn G v U).card:ℝ))
    (hmean : lambda ≤ ((k:ℝ)/U.card)*delta)
    (hK : 1 ≤ Kfull) (hcor : majorityCorrection delta*(9/8) ≤ Kfull) :
    (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).prob
      (fun xi => v∉fixedMajoritySide univ T (C∩T) xi)) ≤
      Kfull*((neighborsIn G v (U\C)).card:ℝ)/delta+exp (-lambda) := by
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
  have hh := fixed_majority_full_vertex_error G univ U (insert v C) hU (mem_univ v)
    hk hdelta hdeg hmean hK hcor
  simp only [mem_insert_self,ite_true,hn] at hh
  apply (le_trans _ hh)
  apply FiniteLaw.expect_mono_support
  intro T hmass
  have hT := (fixed_size_support U T hk hmass).1
  have hvT : v∉T := fun h => hv (hT h)
  have he : insert v C∩T=C∩T := by ext w; simp [hvT]
  rw [he]
  exact le_of_eq (by congr 1; funext xi; simp only [true_iff])

def fixedOutsideMajorityMisses (X C : Finset V) (x : Finset V×(V → Finset V)) : ℝ :=
  ((X\fixedMajoritySide univ x.1 (C∩x.1) x.2).card:ℝ)

theorem fixed_outside_majority_misses_expect (G : SimpleGraph V) (U X C : Finset V)
    (hU : U.Nonempty) (hdisj : Disjoint X U) {k : ℕ} (hk : k ≤ U.card)
    {delta lambda Kfull : ℝ} (hdelta : 2 < delta)
    (hdeg : ∀ v∈X, delta ≤ ((neighborsIn G v U).card:ℝ))
    (hmean : lambda ≤ ((k:ℝ)/U.card)*delta)
    (hK : 1 ≤ Kfull) (hcor : majorityCorrection delta*(9/8) ≤ Kfull) :
    (fixedMajorityExperiment G U k).expect (fixedOutsideMajorityMisses X C) ≤
      Kfull*((G.interedges X (U\C)).card:ℝ)/delta+exp (-lambda)*X.card := by
  have he : ∀ x : Finset V×(V → Finset V), fixedOutsideMajorityMisses X C x=
      ∑ v∈X, if v∉fixedMajoritySide univ x.1 (C∩x.1) x.2 then (1:ℝ) else 0 := by
    intro x
    have hf : X.filter (fun v => v∉fixedMajoritySide univ x.1 (C∩x.1) x.2)=
        X\fixedMajoritySide univ x.1 (C∩x.1) x.2 := by ext v; simp
    simp only [fixedOutsideMajorityMisses,sum_boole,hf]
  rw [fixedMajorityExperiment,FiniteLaw.expect_joint]
  simp_rw [he,FiniteLaw.expect_finset_sum]
  have hp : ∀ v∈X, (fixedSizeLaw U k).expect (fun T => (fixedMajorityLaw G T).expect
      (fun xi => if v∉fixedMajoritySide univ T (C∩T) xi then (1:ℝ) else 0)) ≤
      Kfull*((neighborsIn G v (U\C)).card:ℝ)/delta+exp (-lambda) := by
    intro v hv
    have hpoint : ∀ T, (fixedMajorityLaw G T).expect
        (fun xi => if v∉fixedMajoritySide univ T (C∩T) xi then (1:ℝ) else 0)=
        (fixedMajorityLaw G T).prob (fun xi => v∉fixedMajoritySide univ T (C∩T) xi) := by
      intro T
      unfold FiniteLaw.prob
      congr 1
      funext xi
      by_cases h : v∉fixedMajoritySide univ T (C∩T) xi <;> simp [h]
    simp_rw [hpoint]
    exact fixed_outside_majority_error G U C hU
      (fun hu => Finset.disjoint_left.mp hdisj hv hu) hk hdelta (hdeg v hv) hmean hK hcor
  apply (sum_le_sum hp).trans_eq
  rw [sum_add_distrib,← sum_div,← mul_sum,← Nat.cast_sum,
    ← card_interedges_eq_sum_neighborsIn,sum_const,nsmul_eq_mul]
  ring

end
end Cycle12
