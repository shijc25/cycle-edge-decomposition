import Cycle12.Foundations.IncidentSampleEdges
import Cycle12.Foundations.SubsetBernoulliMGF
import Cycle12.Foundations.SamplingGeometry

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def poissonRate (μ a : ℝ) : ℝ := μ-a+a*log (a/μ)

theorem subsetBernoulli_lower_threshold (W D : Finset V) (p : unitInterval) (hD : D⊆W)
    {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (haμ : a ≤ μ)
    (hmean : μ ≤ (p:ℝ)*D.card) :
    (subsetBernoulli W p).prob (fun S => ((S∩D).card:ℝ) ≤ a) ≤ exp (-poissonRate μ a) := by
  let θ := -log (a/μ)
  have hratio : 0 < a/μ := div_pos ha hμ
  have hratio1 : a/μ ≤ 1 := (div_le_one hμ).mpr haμ
  have hθ : 0 ≤ θ := neg_nonneg.mpr (log_nonpos hratio.le hratio1)
  have hmark := (subsetBernoulli W p).exp_markov_le (fun S => -((S∩D).card:ℝ)) θ (-a) hθ
  have hevent : (fun S : Finset V => ((S∩D).card:ℝ) ≤ a)=
      (fun S => -a ≤ -((S∩D).card:ℝ)) := by funext S; apply propext; exact neg_le_neg_iff.symm
  rw [hevent]
  apply hmark.trans
  have he : (fun S : Finset V => exp (θ*-((S∩D).card:ℝ)))=
      (fun S => exp (-θ*((S∩D).card:ℝ))) := by funext S; congr 1; ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left (subsetBernoulli_count_mgf_le W p D (-θ) hD)
    (exp_pos (-θ*(-a))).le).trans
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hexp : exp (-θ)=a/μ := by dsimp [θ]; rw [neg_neg,exp_log hratio]
  rw [hexp]
  have hm := mul_le_mul_of_nonpos_right hmean (show a/μ-1 ≤ 0 by linarith)
  have hcancel : μ*(a/μ)=a := by field_simp
  dsimp [θ,poissonRate]
  nlinarith

theorem subsetBernoulli_upper_threshold (W D : Finset V) (p : unitInterval) (hD : D⊆W)
    {μ a : ℝ} (hμ : 0 < μ) (hμa : μ ≤ a) (hmean : (p:ℝ)*D.card ≤ μ) :
    (subsetBernoulli W p).prob (fun S => a ≤ ((S∩D).card:ℝ)) ≤ exp (-poissonRate μ a) := by
  let θ := log (a/μ)
  have ha : 0 < a := hμ.trans_le hμa
  have hratio : 0 < a/μ := div_pos ha hμ
  have hratio1 : 1 ≤ a/μ := (le_div_iff₀ hμ).mpr (by simpa using hμa)
  have hθ : 0 ≤ θ := log_nonneg hratio1
  have hmark := (subsetBernoulli W p).exp_markov_le (fun S => ((S∩D).card:ℝ)) θ a hθ
  apply hmark.trans
  apply (mul_le_mul_of_nonneg_left (subsetBernoulli_count_mgf_le W p D θ hD)
    (exp_pos (-θ*a)).le).trans
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hexp : exp θ=a/μ := by dsimp [θ]; rw [exp_log hratio]
  rw [hexp]
  have hm := mul_le_mul_of_nonneg_right hmean (show 0 ≤ a/μ-1 by linarith)
  have hcancel : μ*(a/μ)=a := by field_simp
  dsimp [θ,poissonRate]
  nlinarith

theorem bernoulliSubset_card_lower_log (p : unitInterval) {a : ℝ}
    (hμ : 0 < (p:ℝ)*Fintype.card V) (ha : 0 < a) (haμ : a ≤ (p:ℝ)*Fintype.card V) :
    (bernoulliSubset (V:=V) p).prob (fun S => (S.card:ℝ) < a) ≤
      exp (-poissonRate ((p:ℝ)*Fintype.card V) a) := by
  have hh := subsetBernoulli_lower_threshold (univ:Finset V) univ p (Subset.refl _)
    hμ ha haμ (by simp)
  simp only [subsetBernoulli_univ,inter_univ] at hh
  exact (FiniteLaw.prob_mono _ (fun S h => h.le)).trans hh

theorem bernoulliSubset_card_upper_log (p : unitInterval) {a : ℝ}
    (hμ : 0 < (p:ℝ)*Fintype.card V) (hμa : (p:ℝ)*Fintype.card V ≤ a) :
    (bernoulliSubset (V:=V) p).prob (fun S => a < (S.card:ℝ)) ≤
      exp (-poissonRate ((p:ℝ)*Fintype.card V) a) := by
  have hh := subsetBernoulli_upper_threshold (univ:Finset V) univ p (Subset.refl _)
    hμ hμa (by simp)
  simp only [subsetBernoulli_univ,inter_univ] at hh
  exact (FiniteLaw.prob_mono _ (fun S h => h.le)).trans hh

theorem neighborsIn_univ_card (G : SimpleGraph V) (v : V) :
    (neighborsIn G v univ).card=G.degree v := by
  have he : neighborsIn G v univ=G.neighborFinset v := by ext w; simp [neighborsIn]
  rw [he,card_neighborFinset_eq_degree]

theorem bernoulliSubset_all_degrees_log (G : SimpleGraph V) (p : unitInterval)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (hδμ : δ ≤ μ)
    (hmean : ∀ v, μ ≤ (p:ℝ)*G.degree v) :
    (bernoulliSubset p).prob (fun U => ∃ v, ((neighborsIn G v U).card:ℝ) < δ) ≤
      (Fintype.card V:ℝ)*exp (-poissonRate μ δ) := by
  apply (FiniteLaw.prob_exists_le_sum _ (fun v U => ((neighborsIn G v U).card:ℝ) < δ)).trans
  have hp : ∀ v, (bernoulliSubset p).prob (fun U => ((neighborsIn G v U).card:ℝ) < δ) ≤
      exp (-poissonRate μ δ) := by
    intro v
    have hm : μ ≤ (p:ℝ)*(neighborsIn G v univ).card := by rw [neighborsIn_univ_card]; exact hmean v
    have hh := subsetBernoulli_lower_threshold (univ:Finset V) (neighborsIn G v univ) p
      (subset_univ _) hμ hδ hδμ hm
    have he : ∀ U : Finset V, U∩neighborsIn G v univ=neighborsIn G v U := by
      intro U; ext w; simp [neighborsIn]
    simp_rw [subsetBernoulli_univ,he] at hh
    exact (FiniteLaw.prob_mono _ (fun U h => h.le)).trans hh
  have hs := sum_le_sum (s:=univ) (fun v _ => hp v)
  simpa only [sum_const,card_univ,nsmul_eq_mul] using hs

end
end Cycle13
