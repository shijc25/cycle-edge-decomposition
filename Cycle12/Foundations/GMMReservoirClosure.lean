import Cycle12.Foundations.GMMTerminalPairability
import Cycle12.Foundations.ReservoirClosure
import Cycle12.Foundations.WeakImmersionRouting

/-! Actual GMM connectors in a reserved weak clique immersion, followed
by simple-cycle closure. No demand-routing existence premise remains. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

theorem gmm_immersion_connectors (M : WeakCliqueImmersion t G) (U : Set V)
    (hb : ∀ r, M.branch r∈U)
    (hM : ∀ q : CliquePair t, ∀ v∈(M.route q).val.support, v∈U)
    {I : Type} [Fintype I] [DecidableEq I] (a b : I → Fin t)
    (hd : ∀ r, Suppression.incidenceDegree a b r ≤ 2*(t/6-2)) :
    ∃ Q : ∀ i, G.Walk (M.branch (a i)) (M.branch (b i)),
      (∀ i, (Q i).IsPath) ∧ (∀ i, ∀ v∈(Q i).support, v∈U) ∧
      (Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet)) ∧
      ∀ i, (Q i).edgeSet⊆M.used := by
  obtain ⟨R⟩ := gmm_terminal_pairability a b (by simpa only [Fintype.card_fin] using hd)
  refine ⟨fun i => (M.liftWalk (R.route i)).bypass,fun i => Walk.bypass_isPath _,?_,?_,?_⟩
  · intro i v hv
    exact M.liftWalk_inside U hb hM (R.route i) v (Walk.support_bypass_subset_support _ hv)
  · intro i j hij
    exact (M.liftWalk_disjoint _ _ (R.disjoint hij)).mono
      (Walk.edges_bypass_subset_edges _) (Walk.edges_bypass_subset_edges _)
  · intro i e he
    exact M.liftWalk_edges_subset_used _ (Walk.edges_bypass_subset_edges _ he)

theorem paired_endpoint_degree {I T : Type} [Fintype I] [DecidableEq T]
    (f : I × Bool → T) (r : T) :
    Suppression.incidenceDegree (fun i => f (i,false)) (fun i => f (i,true)) r=
      (univ.filter (fun k => f k=r)).card := by
  rw [← Nat.cast_id ((univ.filter (fun k => f k=r)).card),← sum_boole]
  rw [Fintype.sum_prod_type]
  unfold Suppression.incidenceDegree
  apply sum_congr rfl
  intro i hi
  simp only [Fintype.sum_bool]
  omega

theorem close_paths_via_gmm (P : EndpointPathPacking G) (U : Set V)
    (hPU : ∀ i, ∀ v∈(P.paths i).walk.support, v∉U)
    (M : WeakCliqueImmersion t G) (hb : ∀ r, M.branch r∈U)
    (hM : ∀ q : CliquePair t, ∀ v∈(M.route q).val.support, v∈U)
    (label : Fin P.count × Bool → Fin t)
    (F : ∀ k, G.Walk (P.endpoint k) (M.branch (label k)))
    (hFU : ∀ k, ∀ v∈(F k).support.tail, v∈U)
    (hFF : Pairwise (fun k l => Disjoint (F k).edgeSet (F l).edgeSet))
    (hFM : ∀ k, Disjoint (F k).edgeSet M.used)
    (hload : ∀ r, (univ.filter (fun k => label k=r)).card ≤ 2*(t/6-2)) :
    ∃ C : CyclePacking G, C.count=P.count ∧ P.used⊆C.used ∧
      C.singles ≤ P.singles ∧ C.cost ≤ 42*P.count+23*P.singles := by
  obtain ⟨Q,_,hQU,hQQ,hQM⟩ := gmm_immersion_connectors M U hb hM
    (fun i => label (i,false)) (fun i => label (i,true))
    (by intro r; rw [paired_endpoint_degree]; exact hload r)
  exact close_paths_via_reservoir P U hPU (fun k => M.branch (label k)) F hFU hFF Q hQU hQQ
    (fun k i => (hFM k).mono_right (hQM i))

end
end Cycle13
