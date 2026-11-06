import Cycle12.Foundations.LongCycle
import Cycle12.Foundations.MixedCoverDelete

namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def greedyRatio (n : ℕ) : ℝ := 1-2/((n-1:ℕ):ℝ)

theorem greedyRatio_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ greedyRatio n := by
  have hN : (2:ℝ) ≤ ((n-1:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ n-1 by omega)
  unfold greedyRatio
  have hh : (2:ℝ)/((n-1:ℕ):ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hN
  linarith

/-- One actual greedy step removes a long cycle and contracts the number
of remaining edges by the sharp n-1 factor. -/
theorem CyclePacking.exists_greedy_step {G : SimpleGraph V} (P : CyclePacking G)
    (hn : 3 ≤ Fintype.card V) (hm : Fintype.card V-1 < P.singles) :
    ∃ Q : CyclePacking G, Q.count=P.count+1 ∧
      (Q.singles:ℝ) ≤ greedyRatio (Fintype.card V)*P.singles := by
  obtain ⟨v,p,hp,hlarge⟩ := exists_cycle_with_edge_bound P.residue hm
  let q := p.mapLe P.residue_le
  have hq : q.IsCycle := hp.mapLe _
  have hsub : q.edgeSet ⊆ P.residue.edgeSet := by
    rw [show q.edgeSet=p.edgeSet from Walk.edgeSet_mapLe_eq_edgeSet _ _]
    exact p.edges_subset_edgeSet
  let Q := P.addCycle q.edgeSet ⟨v,q,hq,rfl⟩ hsub
  have hcount : Q.count=P.count+1 := rfl
  have hs : Q.singles+p.length=P.singles := by
    have hh := P.singles_addCycle q.edgeSet ⟨v,q,hq,rfl⟩ hsub
    simpa only [Q,q,Walk.edgeSet_mapLe_eq_edgeSet,cycle_edgeSet_ncard hp] using hh
  have hsr : (Q.singles:ℝ)+p.length=P.singles := by exact_mod_cast hs
  have hl : 2*(P.singles:ℝ) ≤ p.length*((Fintype.card V-1:ℕ):ℝ) := by exact_mod_cast hlarge
  have hN : (0:ℝ) < ((Fintype.card V-1:ℕ):ℝ) := by exact_mod_cast (show 0 < Fintype.card V-1 by omega)
  have hdiv : 2*(P.singles:ℝ)/((Fintype.card V-1:ℕ):ℝ) ≤ p.length := (div_le_iff₀ hN).mpr hl
  refine ⟨Q,hcount,?_⟩
  unfold greedyRatio
  rw [show (1-2/((Fintype.card V-1:ℕ):ℝ))*(P.singles:ℝ)=
    (P.singles:ℝ)-2*(P.singles:ℝ)/((Fintype.card V-1:ℕ):ℝ) by ring]
  linarith only [hsr,hdiv]

/-- The longest-cycle greedy procedure, with all cycles on the original
graph and an explicit bound after any prescribed number of steps. -/
theorem exists_greedy_packing (G : SimpleGraph V) (hn : 3 ≤ Fintype.card V) (k : ℕ) :
    ∃ P : CyclePacking G, P.count ≤ k ∧
      (P.singles:ℝ) ≤ max ((G.edgeSet.ncard:ℝ)*(greedyRatio (Fintype.card V))^k)
        ((Fintype.card V-1:ℕ):ℝ) := by
  induction k with
  | zero =>
    refine ⟨CyclePacking.empty G,by simp [CyclePacking.empty],?_⟩
    rw [CyclePacking.singles_empty,pow_zero,mul_one]
    exact le_max_left _ _
  | succ k ih =>
    obtain ⟨P,hPk,hPe⟩ := ih
    by_cases hsmall : P.singles ≤ Fintype.card V-1
    · refine ⟨P,by omega,?_⟩
      exact (show (P.singles:ℝ) ≤ ((Fintype.card V-1:ℕ):ℝ) by exact_mod_cast hsmall).trans (le_max_right _ _)
    obtain ⟨Q,hQc,hQe⟩ := P.exists_greedy_step hn (lt_of_not_ge hsmall)
    refine ⟨Q,by omega,?_⟩
    have hPL : (P.singles:ℝ) ≤ (G.edgeSet.ncard:ℝ)*(greedyRatio (Fintype.card V))^k := by
      rcases le_max_iff.mp hPe with h | h
      · exact h
      · exact False.elim (hsmall (by exact_mod_cast h))
    apply le_trans hQe
    apply le_trans (mul_le_mul_of_nonneg_left hPL (greedyRatio_nonneg hn))
    rw [pow_succ]
    have he : greedyRatio (Fintype.card V)*((G.edgeSet.ncard:ℝ)*greedyRatio (Fintype.card V)^k)=
        (G.edgeSet.ncard:ℝ)*(greedyRatio (Fintype.card V)^k*greedyRatio (Fintype.card V)) := by ring
    rw [he]
    exact le_max_left _ _

end
end Cycle13
