import Cycle12.FixedAnchorFailure
import Cycle12.FixedRestrictedFailure
import Cycle12.FixedUpperCantelli
import Cycle12.RetainedVertexGraph
import Cycle12.Foundations.SampleSuccess

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Retaining positive mass matters: an arbitrary point outside the
support of a fixed-size law need not have the specified cardinality. -/
theorem finite_law_exists_good_support {Ω I : Type*} [Fintype Ω] [Fintype I]
    (mu : FiniteLaw Ω) (bad : I → Ω → Prop) (bound : I → ℝ)
    (hbound : ∀ i, mu.prob (bad i) ≤ bound i) (hsum : ∑ i, bound i < 1) :
    ∃ x, 0 < mu.mass x ∧ ∀ i, ¬bad i x := by
  by_contra! h
  have he : mu.prob (fun x => ∃ i, bad i x)=1 := by
    calc
      _ = mu.expect (fun _ => 1) := by
        unfold FiniteLaw.prob
        apply le_antisymm <;> apply mu.expect_mono_support <;> intro x hx <;> simp [h x hx]
      _ = 1 := mu.expect_const _
  have hu := mu.prob_exists_le_sum bad
  rw [he] at hu
  have hb := sum_le_sum (s:=univ) (fun i _ => hbound i)
  linarith only [hu,hb,hsum]

variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_expansion_of_not_failure (G : SimpleGraph V) (U : Finset V)
    {N : ℕ} {z dm beta : ℝ} (hcard : U.card=N)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ¬FixedExpansionFailure G univ N z dm beta U) : SampleCutExpansion G U (beta*z) := by
  intro A hAU hsmall
  by_contra! hcut
  have hside : A.card ≤ (U\A).card := by
    rw [card_sdiff_of_subset hAU]
    omega
  apply hbad
  refine ⟨subset_univ U,hcard,hdeg,A,hAU,?_⟩
  rwa [min_eq_left (show (A.card:ℝ) ≤ (U\A).card by exact_mod_cast hside)]

theorem fixed_local_expansion_of_not_failure (G : SimpleGraph V) (U : Finset V)
    {N : ℕ} {z dm beta eta : ℝ} (hcard : U.card=N)
    (hdeg : ∀ v∈U, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hbad : ¬FixedRestrictedCutFailure G univ N z dm beta eta U) :
    LocalSampleCutExpansion G U (beta*z) eta := by
  intro A hAU hsmall hlocal
  by_contra! hcut
  have hAn : A.Nonempty := by
    apply card_pos.mp
    by_contra! hz
    have hzero : A.card=0 := Nat.eq_zero_of_le_zero hz
    rw [hzero,Nat.cast_zero,mul_zero] at hcut
    exact (not_lt_of_ge (Nat.cast_nonneg _)) hcut
  exact hbad ⟨subset_univ U,hcard,hdeg,A,hAU,hAn,hsmall,hlocal,hcut⟩

theorem fixed_anchoring_of_not_failure (G : SimpleGraph V) (U : Finset V)
    {N : ℕ} {z dm beta L : ℝ} (hcard : U.card=N)
    (hdeg : ∀ v, dm*z ≤ ((neighborsIn G v U).card:ℝ))
    (hexp : SampleCutExpansion G U (beta*z))
    (hbad : ¬FixedAnchorFailure G N z dm beta L U) : SampleAnchoring G U L := by
  intro X C hXU hCU hsmall
  by_contra! hcost
  have hx : 0 < (X.card:ℝ) := by
    by_contra! hn
    have hz : (X.card:ℝ)=0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz,mul_zero] at hcost
    have h₁ : (0:ℝ) ≤ (G.interedges X (U\C)).card := Nat.cast_nonneg _
    have h₂ : (0:ℝ) ≤ (G.interedges C (U\C)).card := Nat.cast_nonneg _
    linarith only [hcost,h₁,h₂]
  exact hbad ⟨hcard,hdeg,hexp,X,C,hXU,hCU,hsmall,hx,hcost.le⟩

/-- Jointly choose one actual fixed-size sample. The global-cut and
anchor failure events use their conditional degree/expansion hypotheses,
which are supplied by the earlier good events in this same sample. -/
theorem exists_fixed_sample_of_failure_bounds (G : SimpleGraph V) {N : ℕ}
    (hN : N ≤ Fintype.card V) (extraBad : Finset V → Prop)
    {z dm beta L edgeLower incidentUpper bDegree bCut bAnchor bEdge bIncident bExtra : ℝ}
    (hDegree : (fixedSizeLaw (univ:Finset V) N).prob
      (fun U => ∃ v, ((neighborsIn G v U).card:ℝ) < dm*z) ≤ bDegree)
    (hCut : (fixedSizeLaw (univ:Finset V) N).prob (FixedExpansionFailure G univ N z dm beta) ≤ bCut)
    (hAnchor : (fixedSizeLaw (univ:Finset V) N).prob (FixedAnchorFailure G N z dm beta L) ≤ bAnchor)
    (hEdge : (fixedSizeLaw (univ:Finset V) N).prob
      (fun U => (sampledFinsetEdgeCount G U:ℝ) < edgeLower) ≤ bEdge)
    (hIncident : (fixedSizeLaw (univ:Finset V) N).prob
      (fun U => incidentUpper < (incidentEdgeCount G U:ℝ)) ≤ bIncident)
    (hExtra : (fixedSizeLaw (univ:Finset V) N).prob extraBad ≤ bExtra)
    (hsum : bDegree+bCut+bAnchor+bEdge+bIncident+bExtra < 1) :
    ∃ U : Finset V, U.card=N ∧
      GoodVertexSample G U (dm*z) (beta*z) L N N edgeLower incidentUpper ∧ ¬extraBad U := by
  let mu := fixedSizeLaw (univ:Finset V) N
  let bad : Fin 6 → Finset V → Prop := ![
    (fun U => ∃ v, ((neighborsIn G v U).card:ℝ) < dm*z),FixedExpansionFailure G univ N z dm beta,
    FixedAnchorFailure G N z dm beta L,(fun U => (sampledFinsetEdgeCount G U:ℝ) < edgeLower),
    (fun U => incidentUpper < (incidentEdgeCount G U:ℝ)),extraBad]
  let bound : Fin 6 → ℝ := ![bDegree,bCut,bAnchor,bEdge,bIncident,bExtra]
  have hb : ∀ i, mu.prob (bad i) ≤ bound i := by
    intro i
    fin_cases i
    · exact hDegree
    · exact hCut
    · exact hAnchor
    · exact hEdge
    · exact hIncident
    · exact hExtra
  have htotal : ∑ i, bound i < 1 := by
    simpa [bound,Fin.sum_univ_succ,add_assoc] using hsum
  obtain ⟨U,hUpos,hU⟩ := finite_law_exists_good_support mu bad bound hb htotal
  have hcard := (fixed_size_support univ U (by simpa only [card_univ] using hN) hUpos).2
  have hd : ∀ v, dm*z ≤ ((neighborsIn G v U).card:ℝ) := by
    intro v
    exact le_of_not_gt (fun h => hU 0 ⟨v,h⟩)
  have hc := fixed_expansion_of_not_failure G U hcard (fun v _ => hd v) (hU 1)
  have ha := fixed_anchoring_of_not_failure G U hcard hd hc (hU 2)
  have he : edgeLower ≤ (sampledEdgeCount G (U:Set V):ℝ) := by
    have hh := le_of_not_gt (hU 3)
    change edgeLower ≤ (sampledFinsetEdgeCount G U:ℝ) at hh
    rwa [sampled_finset_edge_count_eq_sampled] at hh
  exact ⟨U,hcard,⟨by simp [hcard],by simp [hcard],hd,hc,ha,he,le_of_not_gt (hU 4)⟩,hU 5⟩

end
end Cycle12
