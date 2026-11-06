import Cycle12.Foundations.WeakImmersionComposition
import Cycle12.Foundations.GraphBranchCut

/-! Recycling the complement of an actual weak clique model. The budget
counts all internal branch passages; no strong-model assumption is used. -/
namespace Cycle13
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

namespace WeakCliqueImmersion
variable {V : Type} {G H : SimpleGraph V} {t : ℕ}

def mapLe (M : WeakCliqueImmersion t G) (h : G ≤ H) : WeakCliqueImmersion t H where
  branch := M.branch
  route p := ⟨(M.route p).val.mapLe h, (M.route p).property.map Function.injective_id⟩
  disjoint := by
    intro p q hpq
    simpa only [Walk.edgeSet_mapLe_eq_edgeSet] using M.disjoint hpq

@[simp] theorem used_mapLe (M : WeakCliqueImmersion t G) (h : G ≤ H) :
    (M.mapLe h).used = M.used := by
  simp only [used, mapLe, Walk.edgeSet_mapLe_eq_edgeSet]

theorem residue_used_cover (M : WeakCliqueImmersion t G) :
    M.residue.edgeSet ∪ M.used = G.edgeSet := by
  rw [residue, SimpleGraph.edgeSet_deleteEdges]
  exact Set.sdiff_union_of_subset M.used_subset

theorem bank_le_residue (M : WeakCliqueImmersion t G)
    (h : G ≤ H) {F : SimpleGraph V} (hF : F ≤ H) (hd : Disjoint F G) :
    F ≤ (M.mapLe h).residue := by
  intro x y hxy
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hF hxy, ?_⟩
  intro he
  have heG := M.used_subset (by simpa only [used_mapLe] using he)
  exact SimpleGraph.disjoint_left.mp hd x y hxy heG

theorem branch_residual_degree [Fintype V] (M : WeakCliqueImmersion t G)
    {D T : ℝ} (hdeg : ∀ i, D ≤ (G.degree (M.branch i) : ℝ))
    (hbudget : ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*t)
    (ht : (t : ℝ) ≤ T) (i : Fin t) :
    D - 11/10*T ≤ (M.residue.degree (M.branch i) : ℝ) := by
  classical
  have hb := M.branch_degree_balance i
  rw [Nat.add_assoc, ← M.branch_used_edges] at hb
  have hbR : (M.residue.degree (M.branch i) : ℝ)+
      ({e ∈ M.used | M.branch i ∈ e}.ncard : ℝ) = G.degree (M.branch i) := by
    exact_mod_cast hb
  have hu : 10*({e ∈ M.used | M.branch i ∈ e}.ncard : ℝ) ≤ 11*(t : ℝ) := by
    exact_mod_cast hbudget i
  have hd := hdeg i
  linarith

end WeakCliqueImmersion

/-- A successful initial bank/core split gives the full recycled degree
reserve once the core contains a budgeted weak model. -/
theorem recycled_weak_branch_bound {V : Type} [Fintype V]
    (H F K : SimpleGraph V) (hd : Disjoint F K) (hu : F ⊔ K = H)
    {t : ℕ} (M : WeakCliqueImmersion t K) {D d g T : ℝ}
    (hg : g < 1) (hcore : ∀ i : Fin t, D ≤ (K.degree (M.branch i) : ℝ))
    (hmark : ∀ v : V, D ≤ (K.degree v : ℝ) →
      g * H.degree v ≤ (F.degree v : ℝ))
    (hbase : ∀ i : Fin t, d ≤ (H.degree (M.branch i) : ℝ))
    (hbudget : ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*t)
    (ht : (t : ℝ) ≤ T) :
    ∃ J : WeakCliqueImmersion t H, J.branch = M.branch ∧ F ≤ J.residue ∧
      ∀ i : Fin t, max (D/(1-g)) d - 11/10*T ≤
        (J.residue.degree (J.branch i) : ℝ) := by
  have hK : K ≤ H := hu ▸ le_sup_right
  have hF : F ≤ H := hu ▸ le_sup_left
  refine ⟨M.mapLe hK, rfl, M.bank_le_residue hK hF hd, ?_⟩
  apply WeakCliqueImmersion.branch_residual_degree _ ?_ ?_ ht
  · intro i
    change max (D/(1-g)) d ≤ (H.degree (M.branch i) : ℝ)
    apply max_le _ (hbase i)
    apply (div_le_iff₀ (show 0 < 1-g by linarith)).mpr
    have hparts := degree_edge_partition F K H hd hu (M.branch i)
    have hpartsR : (F.degree (M.branch i) : ℝ)+K.degree (M.branch i) =
        H.degree (M.branch i) := by exact_mod_cast hparts
    have hm := hmark (M.branch i) (hcore i)
    have hc := hcore i
    nlinarith
  · intro i
    change 10*{e ∈ (M.mapLe hK).used | M.branch i ∈ e}.ncard ≤ 11*t
    rw [WeakCliqueImmersion.used_mapLe]
    exact hbudget i

end
end Cycle13
