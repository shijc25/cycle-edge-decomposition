import Cycle12.ReservedSpokeChoice12
import Cycle12.Foundations.RoutingLoadCounts

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J]

/-- Endpoint occurrences are assigned injectively to the previously
reserved spokes. Their representative load can only decrease, and every
added edge lies in the protected reserve R. -/
theorem close_paths_with_reserved_spokes [Nonempty V]
    (G H R : SimpleGraph V) (hHG : H ≤ G) (U : Finset V) {z upper : ℝ}
    (hU : ReservoirSample H U z upper)
    (root f : J → V) (hf : ∀ j, f j ∈ U ∧ H.Adj (root j) (f j))
    (hR : ∀ j, R.Adj (root j) (f j))
    (hinj : Function.Injective (fun j => s(root j,f j)))
    (hinside : ∀ x ∈ U, ∀ y ∈ U, H.Adj x y → R.Adj x y)
    (hload : ∀ v, ((univ.filter (fun j => f j = v)).card:ℝ) ≤ z/64)
    (source : I × Bool → V) (Q : ∀ i, G.Walk (source (i,false)) (source (i,true)))
    (hne : ∀ i, source (i,false) ≠ source (i,true))
    (hQ : ∀ i, (Q i).IsPath)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet))
    (hout : ∀ i, ∀ v ∈ (Q i).support, v ∉ U)
    (hslots : ∀ v, Fintype.card {k // source k = v} ≤ Fintype.card {j // root j = v})
    (hz : 8192 ≤ z) (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card I:ℝ) ≤ z^2) :
    ∃ C : ∀ i, G.Walk (source (i,false)) (source (i,false)),
      (∀ i, (C i).IsCycle) ∧
      Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
      (∀ i, (Q i).edgeSet ⊆ (C i).edgeSet) ∧
      ∀ i, (C i).edgeSet ⊆ (Q i).edgeSet ∪ R.edgeSet := by
  obtain ⟨pick,hpick,hroot⟩ := embedding_over_fibers source root hslots
  let fi : I × Bool → V := f ∘ pick
  have hfi : ∀ k, fi k ∈ U ∧ H.Adj (source k) (fi k) := by
    intro k
    have hh := hf (pick k)
    rw [hroot k] at hh
    exact hh
  have hRi : ∀ k, R.Adj (source k) (fi k) := by
    intro k
    have hh := hR (pick k)
    rw [hroot k] at hh
    exact hh
  have hii : Function.Injective (fun k => s(source k,fi k)) := by
    intro k l hkl
    apply hpick
    apply hinj
    simpa only [hroot,fi,Function.comp_apply] using hkl
  have hli : ∀ v, ((univ.filter (fun k => fi k = v)).card:ℝ) ≤ z/64 := by
    intro v
    have hc : (univ.filter (fun k => fi k = v)).card ≤ (univ.filter (fun j => f j = v)).card := by
      apply card_le_card_of_injOn pick
      · intro k hk
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hk).2⟩
      · exact fun _ _ _ _ he => hpick he
    exact (show ((univ.filter (fun k => fi k = v)).card:ℝ) ≤
      ((univ.filter (fun j => f j = v)).card:ℝ) by exact_mod_cast hc).trans (hload v)
  exact close_reserved_external_paths G H R hHG U hU source fi Q hQ hQQ hout hfi hRi hinside hii
    (fun i he => (hne i he).elim) hz hlog hsquare hli

/-- Endpoint occurrences indexed by Bool have precisely the endpointLoad
used by the Lovász partition and parity lemmas. -/
theorem endpoint_bool_fiber_card (a b : I → V) (v : V) :
    Fintype.card {k : I × Bool // (if k.2 then b k.1 else a k.1) = v} = Cycle13.endpointLoad a b v := by
  rw [Fintype.card_subtype,card_eq_sum_ones,sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false]
  rw [sum_add_distrib]
  simp only [Cycle13.endpointLoad,card_eq_sum_ones,sum_filter]
  omega

end
end Cycle12
