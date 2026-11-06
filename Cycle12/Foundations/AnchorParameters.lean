import Cycle12.Foundations.GlobalCutParameters
import Cycle12.Foundations.AnchorClassification
import Cycle12.Foundations.AnchorWitnessTransfer

namespace Cycle13
open Finset SimpleGraph Real
open GlobalCutParameters (side smallSide residualGraph dependencyDegree)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure AnchorParameters where
  δ : ℝ
  β : ℝ
  L : ℝ
  lower : ℝ
  upper : ℝ
  err : ℝ
  miss : ℝ
  cap : ℝ
  ω : ℝ
  slope : ℝ
  b : ℝ
  θ : ℝ
  c : ℝ
  popB : ℝ
  h : ℝ
  t₀ : ℝ
  κ : ℝ
  τ : ℝ

namespace AnchorParameters

structure Valid (C : AnchorParameters) (p q ρ : unitInterval) (n : ℝ) : Prop where
  p_pos : 0 < (p:ℝ)
  residual_pos : 0 < (ρ:ℝ)
  degree_pos : 0 < C.δ
  expansion_pos : 0 < C.β
  anchor_pos : 0 < C.L
  anchor_lt_degree : C.L < C.δ
  error_pos : 0 < C.err
  miss_pos : 0 < C.miss
  mark_degree : 1 ≤ (q:ℝ)*C.δ
  mark_cap : (q:ℝ)*C.upper ≤ C.cap
  witness_pos : 0 < C.ω
  witness_bound : C.ω ≤ 1-(2+(C.δ/C.β)*exp (-(q:ℝ)*C.δ))/C.err-
    (C.L/C.δ+exp (-(q:ℝ)*C.δ))/C.miss-exp (-(C.cap-(q:ℝ)*C.upper)^2/(2*C.cap))
  slope_pos : 0 < C.slope
  theta_pos : 0 < C.θ
  mgf_slope : exp C.θ-1 ≤ C.θ*C.slope
  population_pos : 0 < C.c
  population_first : C.c ≤ 1-C.miss
  population_second : C.c*((n:ℝ)-C.lower) ≤ C.popB
  population_bound : C.slope*(p:ℝ)*C.popB+C.b ≤ C.lower/2-C.err*C.L*n/C.δ
  scale_pos : 0 < C.h
  order_scale : 9*C.h ≤ (n:ℝ)
  side_scale_lower : (107/100:ℝ) ≤ C.t₀
  side_scale_bound : C.t₀*C.h ≤ C.c*(C.β*(C.δ-C.L)/C.L)
  retained_nonneg : 0 ≤ C.κ
  marked_retention : C.κ ≤ 1-C.h/n-C.cap/C.h
  fraction_nonneg : 0 ≤ C.τ
  fraction_le_one : C.τ ≤ 1
  cut_threshold : (1+C.err)*C.L ≤ C.τ*C.κ*C.h*C.c*(ρ:ℝ)^2

def eligible (C : AnchorParameters) (T : Finset V) (ξ : V→Option V)
    (A : {A : Finset V // A⊆T}) : Prop := C.t₀*C.h ≤ ((smallSide T ξ A).card:ℝ)

def jansonRate (C : AnchorParameters) (ρ : unitInterval) : ℝ :=
  (1-C.τ)^2*C.κ*C.h*(ρ:ℝ)/(2*(2+1/((ρ:ℝ)*(C.t₀*C.h))))

def upperEvent (C : AnchorParameters) (p : unitInterval) (U T : Finset V)
    (ξ : V→Option V) : Prop :=
  ∃ A, C.slope*(p:ℝ)*(side T ξ A).card+C.b < ((U∩side T ξ A).card:ℝ) ∨
    C.slope*(p:ℝ)*(side T ξ A)ᶜ.card+C.b < ((U\side T ξ A).card:ℝ)

def jansonEvent (C : AnchorParameters) (G : SimpleGraph V) (ρ : unitInterval)
    (U T : Finset V) (ξ : V→Option V) : Prop :=
  (T.card:ℝ) ≤ C.cap ∧ ∃ A, C.eligible T ξ A ∧
    (sampledEdgeCount (residualGraph G T ξ A) {v | v.val∈U}:ℝ) ≤
      C.τ*(Fintype.card (residualGraph G T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2

theorem side_scale_pos (C : AnchorParameters) {p q ρ : unitInterval} {n : ℕ}
    (hC : C.Valid p q ρ n) : 0 < C.t₀ := lt_of_lt_of_le (by norm_num) hC.side_scale_lower

theorem retained_edges (C : AnchorParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V)) (G : SimpleGraph V)
    (hG : GlobalCutProfile G C.h) (T : Finset V) (ξ : V→Option V)
    (A : {A : Finset V // A⊆T}) (hT : (T.card:ℝ) ≤ C.cap) (hA : C.eligible T ξ A) :
    C.κ*C.h*(smallSide T ξ A).card ≤ (Fintype.card (residualGraph G T ξ A).edgeSet:ℝ) := by
  apply global_truncated_after_marks G (smallSide T ξ A) T hC.scale_pos hC.order_scale hG
    ((mul_le_mul_of_nonneg_right hC.side_scale_lower hC.scale_pos.le).trans hA)
    (by exact_mod_cast smallerCutSide_small (side T ξ A)) hT hC.marked_retention

theorem residual_degree (C : AnchorParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V)) (G : SimpleGraph V) (T : Finset V)
    (ξ : V→Option V) (A : {A : Finset V // A⊆T}) (hA : C.eligible T ξ A)
    (v w : (↑(univ\T):Set V)) (hvw : (residualGraph G T ξ A).Adj v w) :
    (residualGraph G T ξ A).degree v+(residualGraph G T ξ A).degree w ≤
      dependencyDegree T ξ A+2 := by
  have hS : 0 < (smallSide T ξ A).card := by
    exact_mod_cast (mul_pos (C.side_scale_pos hC) hC.scale_pos).trans_le hA
  exact truncatedCut_unmarked_endpoint_sum G (smallSide T ξ A) T _ (by omega) hvw

theorem residual_rate (C : AnchorParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V)) (G : SimpleGraph V) (hG : GlobalCutProfile G C.h)
    (T : Finset V) (ξ : V→Option V) (A : {A : Finset V // A⊆T})
    (hT : (T.card:ℝ) ≤ C.cap) (hA : C.eligible T ξ A) :
    C.jansonRate ρ ≤ (1-C.τ)^2*(Fintype.card (residualGraph G T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2/
      (2*(1+(dependencyDegree T ξ A:ℝ)*(ρ:ℝ))) := by
  have hd : (dependencyDegree T ξ A:ℝ) ≤ (1+1)*((smallSide T ξ A).card:ℝ) := by
    have hr := Nat.cast_le (α:=ℝ).mpr
      (Nat.sub_le ((smallSide T ξ A).card+(smallSide T ξ A).card) 2)
    simp only [Nat.cast_add] at hr
    change (((smallSide T ξ A).card+(smallSide T ξ A).card-2:ℕ):ℝ) ≤ _
    linarith
  have hh := janson_rate_from_linear_edge_bound (τ:=C.τ) hC.retained_nonneg hC.scale_pos.le
    hC.residual_pos (L:=1) (by norm_num) (mul_pos (C.side_scale_pos hC) hC.scale_pos)
    hA (Nat.cast_nonneg (dependencyDegree T ξ A)) hd (C.retained_edges hC G hG T ξ A hT hA)
  simpa only [jansonRate,one_add_one_eq_two] using hh

end AnchorParameters
end
end Cycle13
