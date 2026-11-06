import Cycle12.Foundations.GlobalCutProbability
import Cycle12.Foundations.LocalCutProbability
import Cycle12.Foundations.AnchorProbability
import Cycle12.Foundations.IncidentFreedman
import Cycle12.Foundations.GraphSampleVariance

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def SampleAnchoring (G : SimpleGraph V) (U : Finset V) (L : ℝ) : Prop :=
  ∀ X C : Finset V, Disjoint X U → C⊆U → 2*C.card ≤ U.card →
    L*X.card ≤ ((G.interedges X (U\C)).card:ℝ)+((G.interedges C (U\C)).card:ℝ)

structure GoodVertexSample (G : SimpleGraph V) (U : Finset V)
    (δ β L lower upper edgeLower incidentUpper : ℝ) : Prop where
  order_lower : lower ≤ (U.card:ℝ)
  order_upper : (U.card:ℝ) ≤ upper
  neighbors : ∀ v, δ ≤ ((neighborsIn G v U).card:ℝ)
  cuts : SampleCutExpansion G U β
  anchoring : SampleAnchoring G U L
  edges : edgeLower ≤ (sampledEdgeCount G (U:Set V):ℝ)
  incident : (incidentEdgeCount G U:ℝ) ≤ incidentUpper

theorem sample_expansion_of_not_bad_cut (G : SimpleGraph V) (U : Finset V)
    {δ β upper : ℝ} (hupper : (U.card:ℝ) ≤ upper)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ¬BadCutSample G δ β upper U) : SampleCutExpansion G U β := by
  intro A hAU hsmall
  by_contra! hcut
  have ha : 0 < (A.card:ℝ) := by
    by_contra! hn
    have hz : (A.card:ℝ)=0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz,mul_zero] at hcut
    exact (not_lt_of_ge (Nat.cast_nonneg _)) hcut
  exact hbad ⟨hupper,hdeg,A,hAU,ha,hsmall,hcut.le⟩

theorem sample_anchoring_of_not_bad_anchor (G : SimpleGraph V) (U : Finset V)
    {δ β L lower upper : ℝ} (hcond : AnchorSampleConditions G δ β lower upper U)
    (hbad : ¬BadAnchorSample G δ β L lower upper U) : SampleAnchoring G U L := by
  intro X C hXU hCU hsmall
  by_contra! hcost
  have hx : 0 < (X.card:ℝ) := by
    by_contra! hn
    have hz : (X.card:ℝ)=0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz,mul_zero] at hcost
    have h₁ : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
    have h₂ : (0:ℝ) ≤ (G.interedges C (U\C)).card := Nat.cast_nonneg _
    linarith
  exact hbad ⟨hcond,X,C,hXU,hCU,hsmall,hx,hcost.le⟩

def LocalSampleCutExpansion (G : SimpleGraph V) (U : Finset V) (β η : ℝ) : Prop :=
  ∀ C⊆U, 2*C.card ≤ U.card → (C.card:ℝ) ≤ η*U.card →
    β*C.card ≤ ((G.interedges C (U\C)).card:ℝ)

theorem sample_local_expansion_of_not_bad (G : SimpleGraph V) (U : Finset V)
    {δ β upper η : ℝ} (hupper : (U.card:ℝ) ≤ upper)
    (hdeg : ∀ v∈U, δ ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ¬BadCutWithin G δ β upper (fun U A => (A.card:ℝ) ≤ η*U.card) U) :
    LocalSampleCutExpansion G U β η := by
  intro A hAU hsmall hlocal
  by_contra! hcut
  have ha : 0 < (A.card:ℝ) := by
    by_contra! hn
    have hz : (A.card:ℝ)=0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz,mul_zero] at hcut
    exact (not_lt_of_ge (Nat.cast_nonneg _)) hcut
  exact hbad ⟨hupper,hdeg,A,⟨hAU,ha,hsmall,hcut.le⟩,hlocal⟩

theorem exists_sample_of_failure_bounds (G : SimpleGraph V) (p : unitInterval)
    (extraBad : Finset V→Prop) {δ β L lower upper edgeLower incidentUpper : ℝ}
    {bLower bUpper bDegree bCut bAnchor bEdge bIncident bExtra : ℝ}
    (hLower : (bernoulliSubset (V:=V) p).prob (fun U => (U.card:ℝ) < lower) ≤ bLower)
    (hUpper : (bernoulliSubset (V:=V) p).prob (fun U => upper < (U.card:ℝ)) ≤ bUpper)
    (hDegree : (bernoulliSubset p).prob (fun U => ∃ v, ((neighborsIn G v U).card:ℝ) < δ) ≤ bDegree)
    (hCut : (bernoulliSubset p).prob (BadCutSample G δ β upper) ≤ bCut)
    (hAnchor : (bernoulliSubset p).prob (BadAnchorSample G δ β L lower upper) ≤ bAnchor)
    (hEdge : (bernoulliSubset (V:=V) p).prob
      (fun U : Finset V => (sampledEdgeCount G (U:Set V):ℝ) < edgeLower) ≤ bEdge)
    (hIncident : (bernoulliSubset p).prob (fun U => incidentUpper < (incidentEdgeCount G U:ℝ)) ≤ bIncident)
    (hExtra : (bernoulliSubset p).prob extraBad ≤ bExtra)
    (hsum : bLower+bUpper+bDegree+bCut+bAnchor+bEdge+bIncident+bExtra < 1) :
    ∃ U : Finset V, GoodVertexSample G U δ β L lower upper edgeLower incidentUpper ∧ ¬extraBad U := by
  let bad : Fin 8→Finset V→Prop := ![
    (fun U => (U.card:ℝ) < lower),(fun U => upper < (U.card:ℝ)),
    (fun U => ∃ v, ((neighborsIn G v U).card:ℝ) < δ),BadCutSample G δ β upper,
    BadAnchorSample G δ β L lower upper,(fun U => (sampledEdgeCount G (U:Set V):ℝ) < edgeLower),
    (fun U => incidentUpper < (incidentEdgeCount G U:ℝ)),extraBad]
  let bound : Fin 8→ℝ := ![bLower,bUpper,bDegree,bCut,bAnchor,bEdge,bIncident,bExtra]
  have hb : ∀ i, (bernoulliSubset p).prob (bad i) ≤ bound i := by
    intro i
    fin_cases i
    · exact hLower
    · exact hUpper
    · exact hDegree
    · exact hCut
    · exact hAnchor
    · exact hEdge
    · exact hIncident
    · exact hExtra
  have htotal : ∑ i, bound i < 1 := by
    simpa [bound,Fin.sum_univ_succ,add_assoc] using hsum
  obtain ⟨U,hU⟩ := FiniteLaw.exists_all_good (bernoulliSubset p) bad bound hb htotal
  have hlo : lower ≤ (U.card:ℝ) := le_of_not_gt (hU 0)
  have hup : (U.card:ℝ) ≤ upper := le_of_not_gt (hU 1)
  have hd : ∀ v, δ ≤ ((neighborsIn G v U).card:ℝ) := by
    intro v
    by_contra! h
    exact hU 2 ⟨v,h⟩
  have hc := sample_expansion_of_not_bad_cut G U hup (fun v _ => hd v) (hU 3)
  have ha := sample_anchoring_of_not_bad_anchor G U ⟨hlo,hup,hd,hc⟩ (hU 4)
  exact ⟨U,⟨hlo,hup,hd,hc,ha,le_of_not_gt (hU 5),le_of_not_gt (hU 6)⟩,hU 7⟩

end
end Cycle13
