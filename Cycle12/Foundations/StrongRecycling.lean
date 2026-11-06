import Cycle12.Foundations.DenseStrong
import Cycle12.Foundations.StrongBranchBudget

/-! Deterministic recycling of every edge not used by a strong clique model.
The probabilistic construction of the two initial edge banks is separate. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

namespace StrongCliqueImmersion
variable {V : Type} {G H : SimpleGraph V} {t : ℕ}

def mapLe (M : StrongCliqueImmersion t G) (h : G ≤ H) : StrongCliqueImmersion t H where
  branch := M.branch
  route p := ⟨(M.route p).val.mapLe h, (M.route p).property.map Function.injective_id⟩
  disjoint := by
    intro p q hpq
    simpa only [Walk.edgeSet_mapLe_eq_edgeSet] using M.disjoint hpq
  avoids := by
    intro p i hi
    exact M.avoids p i (by simpa only [Walk.support_mapLe_eq_support] using hi)

@[simp] theorem mapLe_branch (M : StrongCliqueImmersion t G) (h : G ≤ H) :
    (M.mapLe h).branch = M.branch := rfl

@[simp] theorem used_mapLe [Fintype V] (M : StrongCliqueImmersion t G) (h : G ≤ H) :
    (M.mapLe h).used = M.used := by
  simp only [used, mapLe, Walk.edgeSet_mapLe_eq_edgeSet]

theorem bank_le_residue [Fintype V] (M : StrongCliqueImmersion t G)
    (h : G ≤ H) {F : SimpleGraph V} (hF : F ≤ H) (hd : Disjoint F G) :
    F ≤ (M.mapLe h).residue := by
  intro x y hxy
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hF hxy, ?_⟩
  intro he
  have heG := M.used_subset (by simpa only [used_mapLe] using he)
  exact SimpleGraph.disjoint_left.mp hd x y hxy heG

end StrongCliqueImmersion

theorem degree_edge_partition {V : Type} [Fintype V] (F K H : SimpleGraph V)
    (hd : Disjoint F K) (hu : F ⊔ K = H) (v : V) :
    F.degree v + K.degree v = H.degree v := by
  classical
  have hdis : Disjoint (F.neighborSet v) (K.neighborSet v) := by
    apply Set.disjoint_left.mpr
    intro w hF hK
    exact SimpleGraph.disjoint_left.mp hd v w hF hK
  have heq : H.neighborSet v = F.neighborSet v ∪ K.neighborSet v := by
    rw [← hu, SimpleGraph.neighborSet_sup]
  have hc := Set.ncard_union_eq hdis
  rw [← heq] at hc
  simpa only [SimpleGraph.ncard_neighborSet] using hc.symm

/-- The exact deterministic hypotheses used after a successful random split. -/
theorem recycled_strong_branch_bound {V : Type} [Fintype V]
    (H F K : SimpleGraph V) (hd : Disjoint F K) (hu : F ⊔ K = H)
    {t : ℕ} (M : StrongCliqueImmersion t K) {D d g T : ℝ}
    (hg : g < 1) (hcore : ∀ i : Fin t, D ≤ (K.degree (M.branch i) : ℝ))
    (hmark : ∀ v : V, D ≤ (K.degree v : ℝ) →
      g * H.degree v ≤ (F.degree v : ℝ))
    (hbase : ∀ i : Fin t, d ≤ (H.degree (M.branch i) : ℝ))
    (ht : (t : ℝ) ≤ T) :
    ∃ J : StrongCliqueImmersion t H, J.branch = M.branch ∧ F ≤ J.residue ∧
      ∀ i : Fin t, max (D / (1 - g)) d - T ≤ (J.residue.degree (J.branch i) : ℝ) := by
  have hK : K ≤ H := hu ▸ le_sup_right
  have hF : F ≤ H := hu ▸ le_sup_left
  refine ⟨M.mapLe hK, rfl, M.bank_le_residue hK hF hd, ?_⟩
  apply StrongCliqueImmersion.branch_residual_degree _ _ ht
  intro i
  change max (D / (1 - g)) d ≤ (H.degree (M.branch i) : ℝ)
  apply max_le _ (hbase i)
  apply (div_le_iff₀ (show 0 < 1 - g by linarith)).mpr
  have hparts := degree_edge_partition F K H hd hu (M.branch i)
  have hpartsR : (F.degree (M.branch i) : ℝ) + K.degree (M.branch i) = H.degree (M.branch i) := by
    exact_mod_cast hparts
  have hm := hmark (M.branch i) (hcore i)
  have hc := hcore i
  nlinarith

/-- Dense strong-core existence, edge recycling and the branch reserve in
one statement. The successful-split inequalities are explicit hypotheses. -/
theorem exists_dense_recycled_strong_model {V : Type} [Fintype V] [DecidableEq V]
    (H F K : SimpleGraph V) (hd : Disjoint F K) (hu : F ⊔ K = H)
    {E N D T d g : ℝ} (hT : 4 ≤ T) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V : ℝ) ≤ N) (hedges : E ≤ (K.edgeFinset.card : ℝ))
    (hdense : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + Real.log (N / T)) ≤ 2 * E / N)
    (hg : g < 1)
    (hmark : ∀ v : V, D ≤ (K.degree v : ℝ) → g * H.degree v ≤ (F.degree v : ℝ))
    (hbase : ∀ v : V, d ≤ (H.degree v : ℝ)) :
    ∃ J : StrongCliqueImmersion (evenFloor T) H, F ≤ J.residue ∧
      ∀ i : Fin (evenFloor T),
        max (D / (1 - g)) d - T ≤ (J.residue.degree (J.branch i) : ℝ) := by
  obtain ⟨M, hM⟩ := exists_dense_even_strong_model K hT hTD hDN horder hedges hdense hstop
  obtain ⟨J, _, hF, hbound⟩ := recycled_strong_branch_bound H F K hd hu M hg hM hmark
    (fun i => hbase (M.branch i)) (evenFloor_bounds hT).2.1
  exact ⟨J, hF, hbound⟩

end
end Cycle13
