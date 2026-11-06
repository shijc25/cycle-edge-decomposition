import Cycle12.Foundations.ExpansionPruning
import Cycle12.Foundations.QuadraticBallGrowth
import Cycle12.Foundations.SmallBoundaryCore

namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem connected_of_cutExpansion [Nonempty V] (G : SimpleGraph V) {h : ℝ}
    (hh : 0 < h) (hexp : OAI.ErdosGallai.CutExpansion G h) : G.Connected := by
  apply connected_of_positive_cuts G
  intro S hS hproper
  have hc : Sᶜ.Nonempty := (Finset.compl_ne_univ_iff_nonempty Sᶜ).mp (by simpa using hproper)
  have hs : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hsc : (0:ℝ) < Sᶜ.card := by exact_mod_cast hc.card_pos
  have hx := hexp S
  rw [← cutSize_eq_interedges] at hx
  have hp : (0:ℝ) < cutSize G S := (mul_pos hh (lt_min hs hsc)).trans_le hx
  exact_mod_cast hp

/-- Closed finite balls; connectedness is supplied wherever the natural
graph distance must distinguish different vertices. -/
def finiteMetricBall (G : SimpleGraph V) (x : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.dist x v ≤ r

theorem mem_finiteMetricBall (G : SimpleGraph V) (x v : V) (r : ℕ) :
    v ∈ finiteMetricBall G x r ↔ G.dist x v ≤ r := by simp [finiteMetricBall]

theorem finiteMetricBall_mono (G : SimpleGraph V) (x : V) {i j : ℕ} (hij : i ≤ j) :
    finiteMetricBall G x i ⊆ finiteMetricBall G x j := by
  intro v hv
  exact (mem_finiteMetricBall _ _ _ _).mpr (((mem_finiteMetricBall _ _ _ _).mp hv).trans hij)

theorem finiteMetricBall_nonempty (G : SimpleGraph V) (x : V) (r : ℕ) :
    (finiteMetricBall G x r).Nonempty := ⟨x,by simp [finiteMetricBall]⟩

theorem finiteMetricBall_zero (G : SimpleGraph V) (hc : G.Connected) (x : V) :
    finiteMetricBall G x 0={x} := by
  ext v
  simp only [mem_finiteMetricBall,Nat.le_zero,Finset.mem_singleton,hc.dist_eq_zero_iff]
  exact eq_comm

/-- Every edge leaving the (i+1)-ball joins its outer layer to the next
layer. This is where simplicity gives the product bound on the cut. -/
theorem metricBall_cut_le_layer_product (G : SimpleGraph V) (x : V) (i : ℕ) :
    cutSize G (finiteMetricBall G x (i+1)) ≤
      (finiteMetricBall G x (i+1)\finiteMetricBall G x i).card*
      (finiteMetricBall G x (i+2)\finiteMetricBall G x (i+1)).card := by
  have hsub : G.interedges (finiteMetricBall G x (i+1)) (finiteMetricBall G x (i+1))ᶜ ⊆
      (finiteMetricBall G x (i+1)\finiteMetricBall G x i) ×ˢ
      (finiteMetricBall G x (i+2)\finiteMetricBall G x (i+1)) := by
    intro e he
    obtain ⟨hu,hv,hadj⟩ := G.mem_interedges_iff.mp he
    have hdu := (mem_finiteMetricBall _ _ _ _).mp hu
    have hdv : ¬G.dist x e.2 ≤ i+1 := by simpa only [mem_compl,mem_finiteMetricBall] using hv
    have hd := hadj.diff_dist_adj (u:=x)
    have he₁ : G.dist x e.1=i+1 := by omega
    have he₂ : G.dist x e.2=i+2 := by omega
    simp only [Finset.mem_product,Finset.mem_sdiff,mem_finiteMetricBall,he₁,he₂]
    omega
  rw [cutSize_eq_interedges]
  simpa only [Finset.card_product] using Finset.card_le_card hsub

theorem metricBall_sqrt_step (G : SimpleGraph V) (x : V) {h : ℝ}
    (hh : 0 ≤ h) (hexp : OAI.ErdosGallai.CutExpansion G h) (i : ℕ)
    (hsmall : 2*(finiteMetricBall G x (i+1)).card ≤ Fintype.card V) :
    sqrt (finiteMetricBall G x i).card+sqrt h ≤ sqrt (finiteMetricBall G x (i+2)).card := by
  have hm₁ := Finset.card_le_card (finiteMetricBall_mono G x (by omega : i ≤ i+1))
  have hm₂ := Finset.card_le_card (finiteMetricBall_mono G x (by omega : i+1 ≤ i+2))
  have hp := cutExpansion_small G hexp hsmall
  have hc := metricBall_cut_le_layer_product G x i
  rw [Finset.card_sdiff_of_subset (finiteMetricBall_mono G x (by omega : i ≤ i+1)),
    Finset.card_sdiff_of_subset (finiteMetricBall_mono G x (by omega : i+1 ≤ i+2))] at hc
  have hcR : (cutSize G (finiteMetricBall G x (i+1)):ℝ) ≤
      ((finiteMetricBall G x (i+1)).card-(finiteMetricBall G x i).card:ℕ)*
      ((finiteMetricBall G x (i+2)).card-(finiteMetricBall G x (i+1)).card:ℕ) := by
    exact_mod_cast hc
  push_cast [Nat.cast_sub hm₁,Nat.cast_sub hm₂] at hcR
  apply sqrt_growth_of_layer_product (y:=((finiteMetricBall G x (i+1)).card:ℝ)) (Nat.cast_nonneg _)
    (by exact_mod_cast (finiteMetricBall_nonempty G x (i+1)).card_pos)
    (Nat.cast_nonneg _) hh (by exact_mod_cast hm₁.trans hm₂)
  exact hp.trans hcR

theorem metricBall_first (G : SimpleGraph V) (x : V) {h : ℝ}
    (hexp : OAI.ErdosGallai.CutExpansion G h) (hn : 2 ≤ Fintype.card V) :
    h ≤ ((finiteMetricBall G x 1).card:ℝ) := by
  have hh := cutExpansion_small G hexp (S:={x}) (by simpa using hn)
  simp only [Finset.card_singleton,Nat.cast_one,mul_one,cutSize_singleton] at hh
  have hsub : G.neighborFinset x ⊆ finiteMetricBall G x 1 := by
    intro v hv
    rw [mem_finiteMetricBall]
    exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset x v).mp hv))
  have hc : (G.degree x:ℝ) ≤ (finiteMetricBall G x 1).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hh.trans hc

theorem metricBall_sqrt_lower (G : SimpleGraph V) (x : V) {h : ℝ}
    (hh : 0 ≤ h) (hexp : OAI.ErdosGallai.CutExpansion G h) (hn : 2 ≤ Fintype.card V)
    (k : ℕ) (hsmall : 2*(finiteMetricBall G x k).card ≤ Fintype.card V) :
    (k:ℝ)/2*sqrt h ≤ sqrt (finiteMetricBall G x k).card := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | (_ | k)
    · simpa using sqrt_nonneg ((finiteMetricBall G x 0).card:ℝ)
    · have hh := sqrt_le_sqrt (metricBall_first G x hexp hn)
      have hz := sqrt_nonneg h
      norm_num only [Nat.cast_one]
      linarith
    · simp only [Nat.add_assoc,show (1:ℕ)+1=2 by rfl] at hsmall ⊢
      have hsmall₁ : 2*(finiteMetricBall G x (k+1)).card ≤ Fintype.card V := by
        have hh := Finset.card_le_card (finiteMetricBall_mono G x (by omega : k+1 ≤ k+2))
        omega
      have hsmall₀ : 2*(finiteMetricBall G x k).card ≤ Fintype.card V := by
        have hh := Finset.card_le_card (finiteMetricBall_mono G x (by omega : k ≤ k+2))
        omega
      have hprev := ih k (by omega) hsmall₀
      have hnext := metricBall_sqrt_step G x hh hexp k hsmall₁
      push_cast
      nlinarith only [hprev,hnext]

theorem finiteMetricBalls_disjoint (G : SimpleGraph V) (hc : G.Connected)
    (x y : V) {k : ℕ} (hk : 2*k < G.dist x y) :
    Disjoint (finiteMetricBall G x k) (finiteMetricBall G y k) := by
  rw [Finset.disjoint_left]
  intro v hx hy
  rw [mem_finiteMetricBall] at hx hy
  have hh := hc.dist_triangle (u:=x) (v:=v) (w:=y)
  rw [SimpleGraph.dist_comm (u:=v) (v:=y)] at hh
  omega

/-- The explicit square-root diameter bound, including its additive
constant. There is no logarithmic or unspecified asymptotic loss. -/
theorem expander_dist_bound (G : SimpleGraph V) {h : ℝ} (hh : 0 < h)
    (hexp : OAI.ErdosGallai.CutExpansion G h) (x y : V) :
    (G.dist x y:ℝ) ≤ 2*sqrt (2*Fintype.card V/h)+2 := by
  letI : Nonempty V := ⟨x⟩
  have hc := connected_of_cutExpansion G hh hexp
  by_cases hxy : x=y
  · subst hxy
    simp only [SimpleGraph.dist_self,Nat.cast_zero]
    positivity
  have hn : 2 ≤ Fintype.card V := Finset.one_lt_card.mpr ⟨x,Finset.mem_univ _,y,Finset.mem_univ _,hxy⟩
  have hd : 0 < G.dist x y := hc.pos_dist_of_ne hxy
  let k := (G.dist x y-1)/2
  have hk : 2*k < G.dist x y := by dsimp [k]; omega
  have hdist : G.dist x y ≤ 2*k+2 := by dsimp [k]; omega
  have hdis := finiteMetricBalls_disjoint G hc x y hk
  have hsum : (finiteMetricBall G x k).card+(finiteMetricBall G y k).card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_univ _
  have hchoose : ∃ z : V, 2*(finiteMetricBall G z k).card ≤ Fintype.card V := by
    by_cases hs : 2*(finiteMetricBall G x k).card ≤ Fintype.card V
    · exact ⟨x,hs⟩
    · exact ⟨y,by omega⟩
  obtain ⟨z,hz⟩ := hchoose
  have hb := metricBall_sqrt_lower G z hh.le hexp hn k hz
  have hbsq : ((k:ℝ)/2)^2*h ≤ (finiteMetricBall G z k).card := by
    calc
      _ = ((k:ℝ)/2*sqrt h)^2 := by rw [mul_pow,sq_sqrt hh.le]
      _ ≤ (sqrt ((finiteMetricBall G z k).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mpr hb
      _ = _ := sq_sqrt (Nat.cast_nonneg _)
  have hzR : 2*((finiteMetricBall G z k).card:ℝ) ≤ Fintype.card V := by exact_mod_cast hz
  have hksq : (k:ℝ)^2 ≤ 2*Fintype.card V/h := (le_div_iff₀ hh).mpr (by nlinarith only [hbsq,hzR])
  have hroot : (k:ℝ) ≤ sqrt (2*Fintype.card V/h) := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by positivity : (0:ℝ) ≤ 2*Fintype.card V/h)]
    exact hksq
  have hdR : (G.dist x y:ℝ) ≤ 2*(k:ℝ)+2 := by exact_mod_cast hdist
  linarith

theorem expander_short_path (G : SimpleGraph V) {h : ℝ} (hh : 0 < h)
    (hexp : OAI.ErdosGallai.CutExpansion G h) (x y : V) :
    ∃ p : G.Walk x y, p.IsPath ∧ (p.length:ℝ) ≤ 2*sqrt (2*Fintype.card V/h)+2 := by
  letI : Nonempty V := ⟨x⟩
  obtain ⟨p,hp,hlen⟩ := (connected_of_cutExpansion G hh hexp).exists_path_of_dist x y
  exact ⟨p,hp,by rw [hlen]; exact expander_dist_bound G hh hexp x y⟩

end
end Cycle13
