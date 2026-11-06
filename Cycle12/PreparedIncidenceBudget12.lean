import Cycle12.PreparedBatchPaths12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Distinct original edges touching a vertex set cost at most its total
original degree; an edge touching twice only strengthens the estimate. -/
theorem original_incident_edge_budget (G : SimpleGraph V) (U : Finset V) (S : Set (Sym2 V))
    (hS : ∀ e,e∈S → ∃ v∈U,e∈G.incidenceSet v) :
    S.ncard ≤ ∑ v∈U,G.degree v := by
  have hs : S.toFinset⊆U.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    obtain ⟨v,hv,hve⟩ := hS e (Set.mem_toFinset.mp he)
    exact mem_biUnion.mpr ⟨v,hv,G.mem_incidenceFinset.mpr hve⟩
  have hc := (card_le_card hs).trans card_biUnion_le
  simpa only [←Set.ncard_eq_toFinset_card',card_incidenceFinset_eq_degree] using hc

theorem PreparedClassLedger12.matching_touches {G : SimpleGraph V} {A : I → Finset V}
    {Q : ℕ} {e : Sym2 (Option I)} {H : SimpleGraph V}
    (D : PreparedClassLedger12 G A Q e H) (hd : Pairwise (fun r t => Disjoint (A r) (A t)))
    {x y : V} (hxy : s(x,y)∈D.matchingEdges) : x∈blockUnion A ∧ y∈blockUnion A := by
  cases D with
  | crossing r t hrt he P hh =>
    have h : (edgeLabelGraph G (blockLabel A) e).Adj x y :=
      PreparedClassLedger12.matching_subset (.crossing r t hrt he P hh) hxy
    rw [he] at h
    rcases ((block_cross_graph G A hd r t x y).mp h).2 with h|h
    · exact ⟨(mem_blockUnion A x).mpr ⟨r,h.1⟩,(mem_blockUnion A y).mpr ⟨t,h.2⟩⟩
    · exact ⟨(mem_blockUnion A x).mpr ⟨t,h.1⟩,(mem_blockUnion A y).mpr ⟨r,h.2⟩⟩
  | _ => exact False.elim hxy

namespace PreparedBlockBatch12
variable {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}

theorem pairs_incident (P : PreparedBlockBatch12 G A Q) {e : Sym2 V} (he : e∈P.pairs.used) :
    ∃ v∈blockUnion A,e∈G.incidenceSet v := by
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  rcases hj with rfl|rfl
  · exact ⟨P.pairs.left j,(mem_blockUnion A _).mpr ⟨P.pairs.owner j,P.pairs.left_mem j⟩,
      G.mk'_mem_incidenceSet_right_iff.mpr (P.pairs.adj_left j)⟩
  · exact ⟨P.pairs.right j,(mem_blockUnion A _).mpr ⟨P.pairs.owner j,P.pairs.right_mem j⟩,
      G.mk'_mem_incidenceSet_right_iff.mpr (P.pairs.adj_right j)⟩

theorem matching_incident (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t)))
    {e : Sym2 V} (he : e∈P.matchingEdges) : ∃ v∈blockUnion A,e∈G.incidenceSet v := by
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hv := (P.classes k).ledger.matching_touches hd hk
    have hg : G.Adj x y := ((P.classes k).ledger.matching_subset hk).1
    exact ⟨x,hv.1,G.mk'_mem_incidenceSet_left_iff.mpr hg⟩

/-- All two-edge paths, even those later sent to completion, plus every
matching edge fit in one active-incidence budget for the actual batch. -/
theorem original_pair_matching_budget (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) :
    2*Fintype.card P.pairs.Index+P.matchingEdges.ncard ≤ ∑ v∈blockUnion A,G.degree v := by
  have hc := original_incident_edge_budget G (blockUnion A) (P.pairs.used∪P.matchingEdges)
    (fun e he => he.elim (fun h => P.pairs_incident h) (fun h => P.matching_incident hd h))
  rw [Set.ncard_union_eq P.pairs_matching,P.pairs.used_card] at hc
  exact hc

/-- The same charge in terms of actual disjoint active-block orders. -/
theorem original_pair_matching_budget_real (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) {a : ℝ}
    (hdegree : ∀ r v,v∈A r → (G.degree v:ℝ) ≤ a) :
    2*(Fintype.card P.pairs.Index:ℝ)+P.matchingEdges.ncard ≤ a*∑ r,((A r).card:ℝ) := by
  have hh : (2*(Fintype.card P.pairs.Index:ℝ)+P.matchingEdges.ncard) ≤
      ∑ v∈blockUnion A,(G.degree v:ℝ) := by exact_mod_cast P.original_pair_matching_budget hd
  have hs : (∑ v∈blockUnion A,(G.degree v:ℝ)) ≤ ∑ _v∈blockUnion A,a := by
    apply sum_le_sum
    intro v hv
    obtain ⟨r,hr⟩ := (mem_blockUnion A v).mp hv
    exact hdegree r v hr
  have he : (blockUnion A).card=∑ r,(A r).card := by
    exact card_biUnion (fun r _ t _ hrt => hd hrt)
  have heR : ((blockUnion A).card:ℝ)=∑ r,((A r).card:ℝ) := by exact_mod_cast he
  simp only [sum_const,nsmul_eq_mul,heR] at hs
  exact hh.trans (by simpa only [mul_comm] using hs)

end PreparedBlockBatch12
end
end Cycle12
