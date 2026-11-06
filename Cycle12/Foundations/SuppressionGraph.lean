import Cycle12.Foundations.NormalizedSuppression
import Cycle12.Foundations.NewEdgeLoss
import Cycle12.Foundations.Deficiency
import Cycle12.Foundations.WeakImmersionComposition

/-! Graph-level consequences of the actual suppression operation: retained
edges persist, strong lifting is available, and simple reductions preserve
Eulerian parity and cannot increase total degree deficiency. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
variable {I J V W : Type} {G : SimpleGraph W} {φ : V ↪ W}

theorem graph_le_append (R : RoutedEdges G φ I) (S : RoutedEdges G φ J)
    (hd : ∀ i j, Disjoint (R.route i).edgeSet (S.route j).edgeSet) :
    R.graph ≤ (R.append S hd).graph := by
  rintro x y ⟨hne,i,hi⟩
  exact ⟨hne,Sum.inl i,hi⟩

variable [Fintype I] [DecidableEq I] [DecidableEq V] (R : RoutedEdges G φ I)

theorem kept_graph_contains (z : V) {x y : {v : V // v≠z}}
    (h : R.graph.Adj x.val y.val) : (R.keptRoutes z).graph.Adj x y := by
  obtain ⟨hne,i,hi⟩ := h
  have ha : R.left i≠z := by
    rcases Sym2.eq_iff.mp hi with hd | hr
    · exact hd.1 ▸ x.property
    · exact hr.1 ▸ y.property
  have hb : R.right i≠z := by
    rcases Sym2.eq_iff.mp hi with hd | hr
    · exact hd.2 ▸ y.property
    · exact hr.2 ▸ x.property
  refine ⟨fun he => hne (congrArg Subtype.val he),⟨i,ha,hb⟩,?_⟩
  apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp hi with hd | hr
  · exact Or.inl ⟨Subtype.ext hd.1,Subtype.ext hd.2⟩
  · exact Or.inr ⟨Subtype.ext hr.1,Subtype.ext hr.2⟩

theorem suppress_graph_contains (z : V) {H : SimpleGraph (R.Ports z)}
    (M : H.Subgraph) (hM : M.IsMatching) :
    R.graph.comap (Subtype.val : {v : V // v≠z} → V) ≤ (R.suppress z M hM).graph := by
  intro x y hxy
  exact graph_le_append _ _ _ (R.kept_graph_contains z hxy)

variable [Fintype V] [Fintype W]

theorem graph_deficiency_le (hs : R.IsSimple)
    (hdeg : ∀ v, R.degree v=G.degree (φ v)) (d : ℕ) :
    degreeDeficiency R.graph d ≤ degreeDeficiency G d := by
  have heq : ∀ v, R.graph.degree v=G.degree (φ v) := fun v =>
    (R.degree_eq_graph hs v).symm.trans (hdeg v)
  unfold degreeDeficiency
  simp_rw [heq]
  calc
    _ = ∑ w ∈ univ.image φ, (d-G.degree w) :=
      (sum_image (fun i _ j _ h => φ.injective h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

theorem graph_even_degrees (hs : R.IsSimple)
    (hdeg : ∀ v, R.degree v=G.degree (φ v)) (heven : ∀ w, Even (G.degree w)) :
    ∀ v, Even (R.graph.degree v) := by
  intro v
  rw [← R.degree_eq_graph hs,hdeg]
  exact heven _

end RoutedEdges

def HasBudgetedClique {V : Type} (t : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ M : WeakCliqueImmersion t G,
    ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*t

theorem HasBudgetedClique.lift {V W : Type} [Fintype V] [Fintype W]
    {H : SimpleGraph V} {G : SimpleGraph W} {t : ℕ}
    (h : HasBudgetedClique t H) (R : EdgeRouting H G) : HasBudgetedClique t G := by
  obtain ⟨M,hM⟩ := h
  exact ⟨M.lift R,M.lift_preserves_branch_budget R hM⟩

theorem hasBudgetedClique_of_strong {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (M : StrongCliqueImmersion t G) : HasBudgetedClique t G := by
  refine ⟨M.toWeak,fun i => ?_⟩
  change 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*t
  rw [M.branch_used_edges]
  omega

theorem no_simple_reduction_of_minimality {I V W : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype W] {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I)
    {d t : ℕ} (hbad : ¬HasBudgetedClique t G)
    (heven : ∀ w, Even (G.degree w)) (hdef : degreeDeficiency G d<d)
    (hdeg : ∀ v, R.degree v=G.degree (φ v))
    (hsmaller : Fintype.card V<Fintype.card W)
    (hminimal : ∀ H : SimpleGraph V, Fintype.card V<Fintype.card W →
      (∀ v, Even (H.degree v)) → degreeDeficiency H d<d → HasBudgetedClique t H) :
    ¬R.IsSimple := by
  intro hs
  have hmodel := hminimal R.graph hsmaller (R.graph_even_degrees hs hdeg heven)
    ((R.graph_deficiency_le hs hdeg d).trans_lt hdef)
  exact hbad (hmodel.lift R.graphRouting)

end
end Cycle13
