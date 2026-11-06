import Cycle12.Foundations.NeighborCopyError

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem neighborsIn_subset_inter (G : SimpleGraph V) (U T : Finset V) (hT : T⊆U) (v : V) :
    neighborsIn G v T=neighborsIn G v U∩T := by
  ext w
  simp only [neighborsIn,mem_filter,mem_inter]
  constructor
  · intro h; exact ⟨⟨hT h.1,h.2⟩,h.1⟩
  · intro h; exact ⟨h.2,h.1.2⟩

theorem neighborCopy_marked_error_mean (G : SimpleGraph V) (U A : Finset V)
    (p : unitInterval) (v : V) :
    (subsetBernoulli U p).expect (fun T => (neighborCopyLaw G T).prob
      (fun ξ => ¬(v∈A ↔ v∈copiedSide T ξ (A∩T)))) ≤
    (((if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card:ℕ):ℝ)/
      ((neighborsIn G v U).card:ℝ)+
      if v∈A then exp (-(p:ℝ)*(neighborsIn G v U).card) else 0 := by
  simp_rw [neighborCopy_error_marginal]
  apply le_trans ((subsetBernoulli U p).expect_mono_support (Y:=fun T =>
    (uniformNeighborChoice (neighborsIn G v U∩T)).prob (copiedVertexError T A v)) ?_)
    (copiedVertexError_mean U (neighborsIn G v U) A p (filter_subset _ _) v)
  intro T hmass
  have hT : T⊆U := by
    by_contra hn
    rw [subsetBernoulli_mass_not_subset U T p hn] at hmass
    exact lt_irrefl _ hmass
  rw [neighborsIn_subset_inter G U T hT v]

theorem sampledErrorWeight_eq_sum (G : SimpleGraph V) (U A S : Finset V) (hAU : A⊆U) :
    sampledErrorWeight G U A (U∩S)=
      ∑ v∈U, ((neighborsIn G v U).card:ℝ)*(if ¬(v∈A ↔ v∈S) then 1 else 0) := by
  have he : A ∆ (U∩S)=U.filter (fun v => ¬(v∈A ↔ v∈S)) := by
    ext v
    by_cases hu : v∈U
    · by_cases ha : v∈A <;> by_cases hs : v∈S <;> simp [Finset.mem_symmDiff,hu,ha,hs]
    · have ha : v∉A := fun h => hu (hAU h)
      simp [Finset.mem_symmDiff,hu,ha]
  rw [sampledErrorWeight,he,sum_filter]
  apply sum_congr rfl
  intro v _
  by_cases h : ¬(v∈A ↔ v∈S) <;> simp [h]

theorem neighborCopy_error_weight_expectation (G : SimpleGraph V) (U A T : Finset V)
    (hAU : A⊆U) :
    (neighborCopyLaw G T).expect (fun ξ =>
      sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T)))=
    ∑ v∈U, ((neighborsIn G v U).card:ℝ)*(neighborCopyLaw G T).prob
      (fun ξ => ¬(v∈A ↔ v∈copiedSide T ξ (A∩T))) := by
  simp_rw [sampledErrorWeight_eq_sum G U A _ hAU,FiniteLaw.expect_finset_sum,
    FiniteLaw.expect_const_mul]
  apply sum_congr rfl
  intro v _
  congr 1
  unfold FiniteLaw.prob
  congr 1
  funext ξ
  by_cases h : ¬(v∈A ↔ v∈copiedSide T ξ (A∩T)) <;> simp [h]

theorem degree_exp_antitone {p δ d : ℝ} (hp : 0≤p) (hδ : 1≤p*δ) (hd : δ≤d) :
    d*exp (-p*d) ≤ δ*exp (-p*δ) := by
  have hder (x : ℝ) : HasDerivAt (fun t : ℝ => t*exp (-p*t))
      (exp (-p*x)*(1-p*x)) x := by
    convert (hasDerivAt_id x).mul (((hasDerivAt_id x).const_mul (-p)).exp) using 1
      <;> (try funext t) <;> dsimp <;> ring
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici δ)
    (f:=fun t : ℝ => t*exp (-p*t)) (f':=fun x => exp (-p*x)*(1-p*x))
    (by fun_prop) (fun x _ => (hder x).hasDerivWithinAt) (fun x hx => by
      have hxδ : δ≤x := interior_subset hx
      apply mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
      have hh := mul_le_mul_of_nonneg_left hxδ hp
      linarith)
  exact hm (by simp) hd hd

end
end Cycle13
