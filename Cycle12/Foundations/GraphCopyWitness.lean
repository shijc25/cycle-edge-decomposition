import Cycle12.Foundations.GraphCopyExpectation

/-! The quantitative neighbor-copy error bound for an actual sampled
cut, with all auxiliary choices made from the marked set alone. -/
namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sum_sample_cross_neighbors (G : SimpleGraph V) (U A : Finset V) (hAU : A⊆U) :
    (∑ v∈U, (((if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card:ℕ):ℝ))=
      2*((G.interedges A (U\A)).card:ℝ) := by
  have h₁ (v : V) : neighborsIn G v U\A=neighborsIn G v (U\A) := by
    ext w; simp [neighborsIn,and_assoc,and_left_comm,and_comm]
  have h₂ (v : V) : neighborsIn G v U∩A=neighborsIn G v A := by
    ext w
    simp only [neighborsIn,mem_inter,mem_filter]
    constructor
    · intro h; exact ⟨h.2,h.1.2⟩
    · intro h; exact ⟨⟨hAU h.1,h.2⟩,h.1⟩
  simp_rw [h₁,h₂]
  have hpoint : ∀ v : V,
      (((if v∈A then neighborsIn G v (U\A) else neighborsIn G v A).card:ℕ):ℝ)=
      if v∈A then ((neighborsIn G v (U\A)).card:ℝ) else ((neighborsIn G v A).card:ℝ) := by
    intro v; split_ifs <;> rfl
  simp_rw [hpoint]
  rw [sum_ite]
  have hf₁ : U.filter (fun v => v∈A)=A := by rw [filter_mem_eq_inter,inter_eq_right.mpr hAU]
  have hf₂ : U.filter (fun v => v∉A)=U\A := by ext v; simp
  rw [hf₁,hf₂,← Nat.cast_sum,← Nat.cast_sum,
    ← card_interedges_eq_sum_neighborsIn,← card_interedges_eq_sum_neighborsIn]
  have hc : (G.interedges (U\A) A).card=(G.interedges A (U\A)).card := by
    letI : Std.Symm G.Adj := ⟨fun _ _ h => G.adj_symm h⟩
    exact Rel.card_interedges_comm (r:=G.Adj) (U\A) A
  rw [hc]
  ring

theorem neighborCopy_total_error (G : SimpleGraph V) (U A : Finset V) (hAU : A⊆U)
    (p : unitInterval) {δ : ℝ} (hδ : 0<δ) (hmark : 1≤(p:ℝ)*δ)
    (hdeg : ∀ v∈U, δ≤((neighborsIn G v U).card:ℝ)) :
    (subsetBernoulli U p).expect (fun T => (neighborCopyLaw G T).expect (fun ξ =>
      sampledErrorWeight G U A (U∩copiedSide T ξ (A∩T)))) ≤
      2*((G.interedges A (U\A)).card:ℝ)+δ*exp (-(p:ℝ)*δ)*A.card := by
  simp_rw [neighborCopy_error_weight_expectation G U A _ hAU,
    FiniteLaw.expect_finset_sum,FiniteLaw.expect_const_mul]
  have hpoint : ∀ v∈U, ((neighborsIn G v U).card:ℝ)*
      (subsetBernoulli U p).expect (fun T => (neighborCopyLaw G T).prob
        (fun ξ => ¬(v∈A ↔ v∈copiedSide T ξ (A∩T)))) ≤
      (((if v∈A then neighborsIn G v U\A else neighborsIn G v U∩A).card:ℕ):ℝ)+
        (if v∈A then δ*exp (-(p:ℝ)*δ) else 0) := by
    intro v hv
    have hd := hdeg v hv
    have hpos : 0<((neighborsIn G v U).card:ℝ) := hδ.trans_le hd
    have hb := mul_le_mul_of_nonneg_left (neighborCopy_marked_error_mean G U A p v) hpos.le
    have htail := degree_exp_antitone p.2.1 hmark hd
    apply hb.trans
    by_cases ha : v∈A
    · simp only [ha,ite_true]
      rw [mul_add,mul_div_cancel₀ _ hpos.ne']
      linarith
    · simp only [ha,ite_false,add_zero]
      rw [mul_div_cancel₀ _ hpos.ne']
  apply (sum_le_sum hpoint).trans_eq
  rw [sum_add_distrib,sum_sample_cross_neighbors G U A hAU,← sum_filter]
  have hf : U.filter (fun v => v∈A)=A := by rw [filter_mem_eq_inter,inter_eq_right.mpr hAU]
  rw [hf,sum_const,nsmul_eq_mul]
  ring

end
end Cycle13
