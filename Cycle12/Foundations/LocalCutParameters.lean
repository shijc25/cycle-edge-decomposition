import Cycle12.Foundations.TruncatedJansonRate
import Cycle12.Foundations.UniformNeighborChoice
import Cycle12.Foundations.MarkedWitnessUnion

/-! Scalar premises for the local-cut sampling argument. The graph
expansion profile remains a separate hypothesis, and every random event
below is an event of the actual sample/mark/neighbor-copy experiment. -/
namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure LocalCutParameters where
  δ : ℝ
  β : ℝ
  err : ℝ
  upper : ℝ
  cap : ℝ
  ω : ℝ
  slope : ℝ
  b : ℝ
  θ : ℝ
  c : ℝ
  η : ℝ
  size : ℝ
  ν : ℝ
  ell : ℝ
  α : ℝ
  h : ℝ
  t₀ : ℝ
  L : ℝ
  k₀ : ℝ
  κ : ℝ
  τ : ℝ

namespace LocalCutParameters

structure Valid (C : LocalCutParameters) (p q ρ : unitInterval) : Prop where
  p_pos : 0 < (p:ℝ)
  residual_pos : 0 < (ρ:ℝ)
  degree_pos : 0 < C.δ
  cut_lt_degree : C.β < C.δ
  error_pos : 0 < C.err
  mark_degree : 1 ≤ (q:ℝ)*C.δ
  mark_cap : (q:ℝ)*C.upper ≤ C.cap
  witness_pos : 0 < C.ω
  witness_bound : C.ω ≤ 1-(2*C.β+C.δ*exp (-(q:ℝ)*C.δ))/C.err-
    exp (-(C.cap-(q:ℝ)*C.upper)^2/(2*C.cap))
  slope_pos : 0 < C.slope
  intercept_nonneg : 0 ≤ C.b
  theta_pos : 0 < C.θ
  mgf_slope : exp C.θ-1 ≤ C.θ*C.slope
  population_pos : 0 < C.c
  population_bound : C.slope*(p:ℝ)*C.c+C.err/C.δ+C.b/(C.δ-C.β) ≤ 1
  scale_pos : 0 < C.h
  side_scale_pos : 0 < C.t₀
  side_scale_bound : C.t₀*C.h ≤ C.c*(C.δ-C.β)
  cap_scale : 1 ≤ C.L
  profile_retention : C.k₀ ≤ truncationProfile C.α (C.L-1) C.t₀
  retained_nonneg : 0 ≤ C.κ
  marked_retention : C.κ ≤ C.k₀-(C.cap/C.h)*(C.L+1/(C.t₀*C.h))
  fraction_nonneg : 0 ≤ C.τ
  fraction_le_one : C.τ ≤ 1
  cut_threshold : C.β+C.err ≤ C.τ*C.κ*C.h*C.c*(ρ:ℝ)^2
  small_fraction_nonneg : 0 ≤ C.η
  reverse_nonneg : 0 ≤ C.ν
  reverse_le_one : C.ν ≤ 1
  reverse_mean : C.ell ≤ (ρ:ℝ)*(C.size-C.cap)
  localization : (1+C.err/C.δ)*C.η*C.upper < C.ν*C.ell

def side (T : Finset V) (ξ : V→Option V) (A : {A : Finset V // A⊆T}) : Finset V :=
  copiedSide T ξ A.val

theorem side_marked (T : Finset V) (ξ : V→Option V) (A : {A : Finset V // A⊆T}) :
    side T ξ A∩T=A.val := copiedSide_marked T ξ A.val A.property

def eligible (C : LocalCutParameters) (T : Finset V) (ξ : V→Option V)
    (A : {A : Finset V // A⊆T}) : Prop :=
  C.t₀*C.h ≤ ((side T ξ A).card:ℝ) ∧ ((side T ξ A).card:ℝ) < C.size

def residualGraph (C : LocalCutParameters) (G : SimpleGraph V)
    (T : Finset V) (ξ : V→Option V) (A : {A : Finset V // A⊆T}) :
    SimpleGraph (↑(univ\T):Set V) :=
  (truncatedCut G (side T ξ A) (roundedCutCap C.L (side T ξ A))).induce (↑(univ\T):Set V)

def dependencyDegree (C : LocalCutParameters) (T : Finset V) (ξ : V→Option V)
    (A : {A : Finset V // A⊆T}) : ℕ :=
  roundedCutCap C.L (side T ξ A)+(side T ξ A).card-2

def jansonRate (C : LocalCutParameters) (ρ : unitInterval) : ℝ :=
  (1-C.τ)^2*C.κ*C.h*(ρ:ℝ)/(2*(C.L+1+1/((ρ:ℝ)*(C.t₀*C.h))))

def upperEvent (C : LocalCutParameters) (p : unitInterval) (U T : Finset V)
    (ξ : V→Option V) : Prop :=
  ∃ A, C.slope*(p:ℝ)*(side T ξ A).card+C.b < ((U∩side T ξ A).card:ℝ)

def reverseEvent (C : LocalCutParameters) (U T : Finset V) (ξ : V→Option V) : Prop :=
  (T.card:ℝ) ≤ C.cap ∧ ∃ A, C.size ≤ ((side T ξ A).card:ℝ) ∧
    ((U∩side T ξ A).card:ℝ) < C.ν*C.ell

def jansonEvent (C : LocalCutParameters) (G : SimpleGraph V) (ρ : unitInterval)
    (U T : Finset V) (ξ : V→Option V) : Prop :=
  (T.card:ℝ) ≤ C.cap ∧ ∃ A, C.eligible T ξ A ∧
    (sampledEdgeCount (C.residualGraph G T ξ A) {v | v.val∈U}:ℝ) ≤
      C.τ*(Fintype.card (C.residualGraph G T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2

def CutProfile (C : LocalCutParameters) (G : SimpleGraph V) : Prop :=
  ∀ X : Finset V, (X.card:ℝ) < C.size → C.α*C.h*X.card ≤ (cutSize G X:ℝ)

theorem retained_edges (C : LocalCutParameters) {p q ρ : unitInterval} (hC : C.Valid p q ρ)
    (G : SimpleGraph V) (hG : C.CutProfile G) (T : Finset V)
    (ξ : V→Option V) (A : {A : Finset V // A⊆T})
    (hT : (T.card:ℝ) ≤ C.cap) (hA : C.eligible T ξ A) :
    C.κ*C.h*(side T ξ A).card ≤ (Fintype.card (C.residualGraph G T ξ A).edgeSet:ℝ) := by
  apply rounded_truncation_retained G (side T ξ A) T hC.scale_pos hC.side_scale_pos
    hC.cap_scale hA.1 (α₀:=C.α) (α₁:=C.α) (le_refl _) (le_refl _)
    (by simpa only [min_self] using hC.profile_retention) ?_ hT hC.marked_retention
  intro X hX
  apply hG X
  exact (show (X.card:ℝ) ≤ (side T ξ A).card by exact_mod_cast card_le_card hX).trans_lt hA.2

theorem residual_degree (C : LocalCutParameters) {p q ρ : unitInterval} (hC : C.Valid p q ρ)
    (G : SimpleGraph V) (T : Finset V) (ξ : V→Option V) (A : {A : Finset V // A⊆T})
    (hA : C.eligible T ξ A) (v w : (↑(univ\T):Set V))
    (hvw : (C.residualGraph G T ξ A).Adj v w) :
    (C.residualGraph G T ξ A).degree v+(C.residualGraph G T ξ A).degree w ≤
      C.dependencyDegree T ξ A+2 := by
  have hS : 0 < (side T ξ A).card := by
    exact_mod_cast (mul_pos hC.side_scale_pos hC.scale_pos).trans_le hA.1
  exact truncatedCut_unmarked_endpoint_sum G (side T ξ A) T _
    (roundedCutCap_endpoint_budget hC.cap_scale _ hS).1 hvw

theorem residual_rate (C : LocalCutParameters) {p q ρ : unitInterval} (hC : C.Valid p q ρ)
    (G : SimpleGraph V) (hG : C.CutProfile G) (T : Finset V)
    (ξ : V→Option V) (A : {A : Finset V // A⊆T})
    (hT : (T.card:ℝ) ≤ C.cap) (hA : C.eligible T ξ A) :
    C.jansonRate ρ ≤ (1-C.τ)^2*(Fintype.card (C.residualGraph G T ξ A).edgeSet:ℝ)*(ρ:ℝ)^2/
      (2*(1+(C.dependencyDegree T ξ A:ℝ)*(ρ:ℝ))) := by
  exact rounded_truncated_janson_rate G (side T ξ A) T hC.retained_nonneg hC.scale_pos.le
    hC.residual_pos hC.cap_scale (mul_pos hC.side_scale_pos hC.scale_pos) hA.1
    (C.retained_edges hC G hG T ξ A hT hA)

end LocalCutParameters
end
end Cycle13
