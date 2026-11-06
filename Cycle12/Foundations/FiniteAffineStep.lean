import Cycle12.Foundations.DFSBlockPacking
import Cycle12.Foundations.PackingExtension

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def WeightedAffineBound (C t : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ P : CyclePacking G, P.weight ≤ C*Fintype.card V+(G.edgeSet.ncard:ℝ)/t

def FiniteBlockPayment (k T : ℕ) (t K : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B : DFSBlock G k T),
    ∃ P : CyclePacking B.localGraph,
      (P.count:ℝ)+(P.singles:ℝ)/t-(B.localGraph.edgeSet.ncard:ℝ)/T ≤ K*B.core.card

theorem weightedAffine_trivial : WeightedAffineBound 0 (42/23) := by
  intro V _ _ G
  refine ⟨CyclePacking.empty G,?_⟩
  rw [CyclePacking.weight_empty]
  norm_num
  ring_nf
  exact le_rfl

/-- Turn a bounded-circumference affine theorem into a theorem for every
graph, by removing actual long cycles first. -/
theorem weightedAffine_of_short_cycles {C : ℝ} {T : ℕ} (hT : 1 ≤ T)
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      NoCycleAtLeast G T → ∃ P : CyclePacking G,
        P.weight ≤ C*Fintype.card V+(G.edgeSet.ncard:ℝ)/T) :
    WeightedAffineBound C T := by
  intro V _ _ G
  obtain ⟨P,hP,hpay⟩ := exists_long_cycle_removal G T
  obtain ⟨Q,hQ⟩ := hbase V P.residue hP
  refine ⟨P.extend Q,?_⟩
  rw [CyclePacking.extend_weight]
  have ht : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hb : (P.count:ℝ)+(P.singles:ℝ)/T ≤ (G.edgeSet.ncard:ℝ)/T := by
    apply (le_div_iff₀ ht).mpr
    have hh : (P.count:ℝ)*T+P.singles ≤ G.edgeSet.ncard := by exact_mod_cast hpay
    convert hh using 1 <;> field_simp <;> ring
  change Q.weight ≤ C*Fintype.card V+(P.singles:ℝ)/T at hQ
  linarith

/-- A complete finite DFS step. The suffix is applied once, to the union
of all leftover original edges, so its order term is C*n, not the sum of
overlapping block orders. The local numerical payment remains explicit. -/
theorem weightedAffine_dfs_step {C K t : ℝ} {k T : ℕ}
    (hk : 0<k) (hT : 1≤T) (ht : 0<t)
    (hsuffix : WeightedAffineBound C t) (hblock : FiniteBlockPayment k T t K) :
    WeightedAffineBound (C+K) T := by
  intro V _ _ G
  obtain ⟨L,hL,hlong⟩ := exists_long_cycle_removal G T
  obtain ⟨D⟩ := exists_dfsPartition L.residue hk hT hL
  choose P hP using fun i => hblock V L.residue (D.block i)
  obtain ⟨R,hRc,hRs⟩ := D.exists_packing P
  have hcost : (R.count:ℝ)+(R.singles:ℝ)/t-(L.singles:ℝ)/T ≤ K*Fintype.card V := by
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin D.count))) => hP i)
    have hsumCore : (∑ i, ((D.block i).core.card:ℝ))=Fintype.card V := by
      exact_mod_cast (by simpa only [Finset.card_univ] using D.sum_core_card)
    have hsumEdges : (∑ i, ((D.block i).localGraph.edgeSet.ncard:ℝ))=L.singles := by
      exact_mod_cast D.sum_local_edges
    have hsumCount : (∑ i, ((P i).count:ℝ))=R.count := by exact_mod_cast hRc.symm
    have hsumSingles : (∑ i, ((P i).singles:ℝ))=R.singles := by exact_mod_cast hRs.symm
    simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,
      ← Finset.mul_sum,hsumCore,hsumEdges,hsumCount,hsumSingles] using hh
  obtain ⟨Q,hQ⟩ := hsuffix V R.residue
  refine ⟨L.extend (R.extend Q),?_⟩
  rw [CyclePacking.extend_weight,CyclePacking.extend_weight]
  have hTpos : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hb : (L.count:ℝ)+(L.singles:ℝ)/T ≤ (G.edgeSet.ncard:ℝ)/T := by
    apply (le_div_iff₀ hTpos).mpr
    have hh : (L.count:ℝ)*T+L.singles ≤ G.edgeSet.ncard := by exact_mod_cast hlong
    convert hh using 1 <;> field_simp <;> ring
  change Q.weight ≤ C*Fintype.card V+(R.singles:ℝ)/t at hQ
  nlinarith only [hcost,hQ,hb]

end
end Cycle13
