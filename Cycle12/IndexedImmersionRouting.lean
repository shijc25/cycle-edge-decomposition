import Cycle12.ExpandingCapacityRouting
import Cycle12.Foundations.BankCycleClosure
import Cycle12.Foundations.WeakRecycling

namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Indexed fans may have repeated roots and may be empty. Composing them
with terminal-pairability in a weak immersion preserves edge disjointness. -/
theorem route_indexed_fans (G F : SimpleGraph V) (hFG : F ≤ G)
    {t c : ℕ} (M : WeakCliqueImmersion t G)
    (hFM : Disjoint F.edgeSet M.used) (source : I × Bool → V)
    (R : IndexedCapacity.Routing F source M.branchFinset c)
    (hc : c ≤ 2*(t/6-2)) :
    Nonempty (DemandRouting G (fun i => source (i,false)) (fun i => source (i,true))) := by
  let label := fun k => M.branchLabel (R.branch k)
  have hlabel : ∀ k, M.branch (label k) = (R.branch k).val :=
    fun k => M.branchLabel_spec _
  let fan : ∀ k, G.Walk (source k) (M.branch (label k)) :=
    fun k => ((R.path k).mapLe hFG).copy rfl (hlabel k).symm
  have hfan : ∀ k, (fan k).edgeSet = (R.path k).edgeSet := by
    intro k
    simp only [fan, Walk.edgeSet_copy, Walk.edgeSet_mapLe_eq_edgeSet]
  have hslots : Function.Injective (fun k => (label k,R.slot k)) := by
    intro k l h
    apply R.slot_injective
    refine Prod.ext ?_ (congrArg (fun z : Fin t × Fin c => z.2) h)
    apply Subtype.ext
    have hfirst : label k = label l := congrArg (fun z : Fin t × Fin c => z.1) h
    rw [← hlabel k, ← hlabel l, hfirst]
  have hload : ∀ v, (univ.filter (fun k => label k = v)).card ≤ 2*(t/6-2) :=
    fun v => (slot_injective_load label R.slot hslots v).trans hc
  obtain ⟨Q,_,_,hQQ,hQM⟩ := gmm_immersion_connectors M Set.univ
    (fun _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _)
    (fun i => label (i,false)) (fun i => label (i,true))
    (fun v => by rw [paired_endpoint_degree]; exact hload v)
  have hFF : Pairwise (fun k l => Disjoint (fan k).edgeSet (fan l).edgeSet) := by
    simpa only [hfan] using R.disjoint
  have hFQ : ∀ k i, Disjoint (fan k).edgeSet (Q i).edgeSet := by
    intro k i
    rw [hfan]
    exact hFM.mono (R.path k).edges_subset_edgeSet (hQM i)
  refine ⟨{
    route := fun i => ((fan (i,false)).append (Q i)).append (fan (i,true)).reverse
    disjoint := ?_ }⟩
  intro i j hij
  simp only [Walk.edgeSet_append, Walk.edgeSet_reverse]
  have hcross : ∀ x y : Bool, Disjoint (fan (i,x)).edgeSet (fan (j,y)).edgeSet := by
    intro x y
    exact hFF (fun h => hij (congrArg Prod.fst h))
  exact (((hcross false false).union_right (hFQ (i,false) j)).union_right (hcross false true)).union_left
    (((hFQ (j,false) i).symm.union_right (hQQ hij)).union_right (hFQ (j,true) i).symm) |>.union_left
      (((hcross true false).union_right (hFQ (i,true) j)).union_right (hcross true true))

theorem route_via_expansion_and_immersion (G F : SimpleGraph V) (hFG : F ≤ G)
    {t c : ℕ} {h : ℝ} (M : WeakCliqueImmersion t G)
    (hFM : Disjoint F.edgeSet M.used) (source : I × Bool → V)
    (hexp : OAI.ErdosGallai.CutExpansion F h)
    (hload : ∀ v, ((univ.filter (fun k => source k = v)).card:ℝ) ≤ h)
    (hc : (c:ℝ) ≤ h) (hcap : 2*Fintype.card I ≤ c*t)
    (hterminal : c ≤ 2*(t/6-2)) :
    ∃ p : ∀ i, G.Walk (source (i,false)) (source (i,true)),
      (∀ i, (p i).IsPath) ∧ Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet) := by
  obtain ⟨R⟩ := IndexedCapacity.exists_routing_of_expansion F source M.branchFinset c
    hexp hload hc (by simpa only [Fintype.card_prod, Fintype.card_bool,
      M.branchFinset_card, Nat.mul_comm] using hcap)
  obtain ⟨Q⟩ := route_indexed_fans G F hFG M hFM source R hterminal
  exact Q.simple_paths

end
end Cycle12
