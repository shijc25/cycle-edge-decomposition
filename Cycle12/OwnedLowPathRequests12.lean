import Cycle12.OwnedPairGraph12
import Cycle12.LowDemandIncidence12
import Cycle12.GroupedDemandData12

namespace Cycle12.OwnedTwoEdgeFamily12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : I → Finset V}

theorem load_bound_of_good_vertices (P : OwnedTwoEdgeFamily12 G A) (good : Finset V)
    {a : ℝ} (ha : 0 ≤ a) (hl : ∀ j,P.left j∈good) (hr : ∀ j,P.right j∈good)
    (hd : ∀ v,v∈good → (G.degree v:ℝ) ≤ a) (v : V) :
    (endpointLoad P.left P.right v:ℝ) ≤ a := by
  by_cases hv : v∈good
  · have hh : (endpointLoad P.left P.right v:ℝ) ≤ G.degree v := by
      exact_mod_cast P.certificate.load_le v
    exact hh.trans (hd v hv)
  · have hL : univ.filter (fun j : P.Index => P.left j=v)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro j _ he
      exact hv (he ▸ hl j)
    have hR : univ.filter (fun j : P.Index => P.right j=v)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro j _ he
      exact hv (he ▸ hr j)
    simpa only [endpointLoad,hL,hR,card_empty,zero_add,Nat.cast_zero] using ha

/-- Keep pairs only at centers below the actual original pair-graph degree
threshold. No original pair is split between the two sides. -/
def low (P : OwnedTwoEdgeFamily12 G A) (d : ℝ) : OwnedTwoEdgeFamily12 G A :=
  P.restrict (fun j => (P.graph.degree (P.center j):ℝ) < d)

theorem low_center_load (P : OwnedTwoEdgeFamily12 G A) {d : ℝ} (hd : 0 ≤ d) (v : V) :
    (univ.filter (fun j : (P.low d).Index => (P.low d).center j=v)).card ≤ ⌊d/2⌋₊ := by
  let Q := P.low d
  have hl (j : Q.Index) : P.graph.Adj (Q.center j) (Q.left j) := by
    apply (P.graph_adj _ _).mpr
    exact Set.mem_iUnion.mpr ⟨j.val,Or.inl rfl⟩
  have hr (j : Q.Index) : P.graph.Adj (Q.center j) (Q.right j) := by
    apply (P.graph_adj _ _).mpr
    exact Set.mem_iUnion.mpr ⟨j.val,Or.inr rfl⟩
  by_cases hv : (P.graph.degree v:ℝ) < d
  · have hh := twoEdge_center_load Q.left Q.right Q.center hl hr Q.distinct (by
      simpa only [twoEdgeWalk_edges] using Q.disjoint) v
    apply (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ d/2)).mpr
    have hhR : 2*((univ.filter (fun j : Q.Index => Q.center j=v)).card:ℝ) ≤ P.graph.degree v := by
      exact_mod_cast hh
    linarith only [hhR,hv]
  · have he : univ.filter (fun j : Q.Index => Q.center j=v)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro j _ hj
      have hp : (P.graph.degree (Q.center j):ℝ) < d := j.property
      rw [hj] at hp
      exact hv hp
    change (univ.filter (fun j : Q.Index => Q.center j=v)).card ≤ _
    rw [he,card_empty]
    exact Nat.zero_le _

/-- Real allowances are rounded down for the coloring palette, so no
unbudgeted ceiling term is introduced into the high-center estimate. -/
theorem low_coloring (P : OwnedTwoEdgeFamily12 G A) (good : Finset V) {a d : ℝ}
    (ha : 1 ≤ a) (hd : 0 ≤ d) (hl : ∀ j,P.left j∈good) (hr : ∀ j,P.right j∈good)
    (hdegree : ∀ v,v∈good → (G.degree v:ℝ) ≤ a) :
    Nonempty ((lowPathConflict (P.low d).left (P.low d).right (P.low d).center).Coloring
      (Fin (2*⌊a⌋₊+⌊d/2⌋₊))) := by
  have ha0 : 0 ≤ a := (by norm_num : (0:ℝ) ≤ 1).trans ha
  have hA : 1 ≤ ⌊a⌋₊ := (Nat.le_floor_iff ha0).mpr (by exact_mod_cast ha)
  apply low_path_coloring _ _ _ (by omega)
  · intro v
    rw [←endpointLoad_eq_incident_card _ _ (P.low d).distinct v]
    apply (Nat.le_floor_iff ha0).mpr
    exact (P.low d).load_bound_of_good_vertices good ha0
      (fun j => hl j.val) (fun j => hr j.val) hdegree v
  · exact P.low_center_load hd

theorem low_palette_cost {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    ((2*⌊a⌋₊+⌊d/2⌋₊:ℕ):ℝ) ≤ 2*a+d/2 := by
  have hA := Nat.floor_le ha
  have hD := Nat.floor_le (show 0 ≤ d/2 by positivity)
  push_cast
  linarith only [hA,hD]

/-- Reconnecting the original pairs only permutes their charged ports.
This certificate can be combined with matching and quotient certificates. -/
theorem reconnection_certificate_exists (P : OwnedTwoEdgeFamily12 G A) (next : Equiv.Perm P.Index) :
    Nonempty (OriginalEndpointCertificate G P.right (fun j => P.left (next j)) P.used) := by
  obtain ⟨neighbor,hn,hinj⟩ := low_demands_original_incidences G P.left P.right P.center
    P.adj_left P.adj_right P.distinct (by simpa only [twoEdgeWalk_edges] using P.disjoint) next
  refine ⟨⟨neighbor,fun k => (hn k).1,?_,hinj⟩⟩
  intro k
  simpa only [twoEdgeWalk_edges,used,edges] using (hn k).2

theorem low_group_count (P : OwnedTwoEdgeFamily12 G A) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (color : (lowPathConflict (P.low d).left (P.low d).right (P.low d).center).Coloring
      (Fin (2*⌊a⌋₊+⌊d/2⌋₊))) {Q : ℕ} (hQ : 0<Q) :
    (Fintype.card (ColoredDemandGroups color Q):ℝ) ≤
      (Fintype.card (P.low d).Index:ℝ)/Q+2*a+d/2 := by
  have hh := coloredDemandGroups_count_bound color hQ
  rw [Fintype.card_fin] at hh
  exact hh.trans (by have hp := low_palette_cost ha hd; linarith only [hp])

end
end Cycle12.OwnedTwoEdgeFamily12
