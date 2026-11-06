/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BergeLib.Berge
public import GallaiEdmondsLib.GEConstruct

/-!
# The Gallai–Edmonds structure theorem

For a finite simple graph `G`, let `D(G)` be the set of vertices missed by at least one maximum
matching, `A(G)` the set of vertices outside `D(G)` with a neighbour in `D(G)`, and `C(G)` the
remaining vertices. Matchings are Mathlib's `SimpleGraph.Subgraph.IsMatching`; a set `S` has a
perfect matching if some matching of `G` has vertex set exactly `S`.

* `GallaiEdmonds.factorCritical`: every connected component of `G[D(G)]` is *factor-critical*:
  deleting any one of its vertices leaves a set with a perfect matching.
* `GallaiEdmonds.perfectMatching_C`: `G[C(G)]` has a perfect matching.
* `GallaiEdmonds.maximumMatching_structure`: every maximum matching matches `C(G)` within itself,
  matches every vertex of `A(G)` to a vertex of `D(G)`, sends distinct vertices of `A(G)` into
  distinct components of `G[D(G)]`, and leaves at most one vertex of each component of `G[D(G)]`
  unmatched within that component.
* `GallaiEdmonds.two_mul_card_add`: **the Gallai–Edmonds formula.** For every maximum matching `M`,
  `2|M| + c(D(G)) = |V| + |A(G)|`, where `c(D(G))` is the number of components of `G[D(G)]`.
-/

@[expose] public section

open SimpleGraph

namespace GallaiEdmonds

variable {V : Type*} (G : SimpleGraph V)

/-- `M` is a maximum matching of `G`. -/
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

/-- `D(G)`: the vertices missed by at least one maximum matching. -/
def setD : Set V := {v | ∃ M : G.Subgraph, IsMaximumMatching G M ∧ v ∉ M.verts}

/-- `A(G)`: the vertices outside `D(G)` adjacent to a vertex of `D(G)`. -/
def setA : Set V := {v | v ∉ setD G ∧ ∃ u ∈ setD G, G.Adj u v}

/-- `C(G)`: the vertices in neither `D(G)` nor `A(G)`. -/
def setC : Set V := {v | v ∉ setD G ∧ v ∉ setA G}

/-- `S` has a perfect matching: some matching of `G` has vertex set exactly `S`. -/
def HasPerfectMatchingOn (S : Set V) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = S

/-- The vertex set of a connected component of `G[D(G)]`. -/
def compSet (c : (G.induce (setD G)).ConnectedComponent) : Set V :=
  {v | ∃ h : v ∈ setD G, (G.induce (setD G)).connectedComponentMk ⟨v, h⟩ = c}


/-! ### Auxiliary lemmas: identification of `D`, `A`, `C` via a minimal barrier -/

lemma oddPart_closed (U : Set V) : Closed G Uᶜ (oddPart G U) := by
  rintro y ⟨hyU, hodd⟩ z hz hadj
  have hzy : z ∈ cc G Uᶜ y := mem_cc_of_adj (mem_cc_self hyU) hz hadj
  exact ⟨hz, by rw [cc_eq_of_mem hzy]; exact hodd⟩

lemma oddPart_subset (U : Set V) : oddPart G U ⊆ Uᶜ := fun _ hy => hy.1

lemma exists_maximum [Finite V] : ∃ M : G.Subgraph, IsMaximumMatching G M := by
  obtain ⟨M, -, hM, hmax, -⟩ := tb_eq G
  exact ⟨M, hM, hmax⟩

lemma setD_eq [Finite V] {U : Set V} (hU : IsMinBarrier G U) : setD G = oddPart G U := by
  ext v
  constructor
  · rintro ⟨M, ⟨hM, hmax⟩, hv⟩
    obtain ⟨h1a, -, -, h1d⟩ := step1 hM (hU.1.eq hM hmax)
    have hvU : v ∉ U := fun hvU => by
      obtain ⟨x, hx, -⟩ := h1a v hvU
      exact hv (M.edge_vert hx)
    refine ⟨hvU, ?_⟩
    by_contra hodd
    obtain ⟨w, -, hw⟩ := h1d v hvU (Nat.not_odd_iff_even.mp hodd)
    exact hv (M.edge_vert hw)
  · intro hv
    obtain ⟨M, hM, hmax⟩ := exists_maximum G
    obtain ⟨M', hM', hmax', hvM'⟩ := exists_max_missing hU hM hmax hv
    exact ⟨M', ⟨hM', hmax'⟩, hvM'⟩

lemma setA_eq [Finite V] {U : Set V} (hU : IsMinBarrier G U) : setA G = U := by
  ext a
  constructor
  · rintro ⟨haD, d, hdD, hadj⟩
    rw [setD_eq G hU] at haD hdD
    by_contra haU
    have had : a ∈ cc G Uᶜ d := mem_cc_of_adj (mem_cc_self hdD.1) haU hadj
    exact haD ⟨haU, by rw [cc_eq_of_mem had]; exact hdD.2⟩
  · intro hu
    obtain ⟨M, hM, hmax⟩ := exists_maximum G
    obtain ⟨h1a, -, -, -⟩ := step1 hM (hU.1.eq hM hmax)
    obtain ⟨x, hx, hxU, hodd⟩ := h1a a hu
    refine ⟨?_, x, ?_, (M.adj_sub hx).symm⟩
    · rw [setD_eq G hU]; exact fun h => h.1 hu
    · rw [setD_eq G hU]; exact ⟨hxU, hodd⟩

lemma mem_setC_iff [Finite V] {U : Set V} (hU : IsMinBarrier G U) (w : V) :
    w ∈ setC G ↔ w ∉ U ∧ Even (cc G Uᶜ w).ncard := by
  simp only [setC, setD_eq G hU, setA_eq G hU, Set.mem_ofPred_eq, oddPart,
    ← Nat.not_odd_iff_even]
  tauto

lemma compSet_mk [Finite V] {U : Set V} (hU : IsMinBarrier G U) (x : V) (hx : x ∈ setD G) :
    compSet G ((G.induce (setD G)).connectedComponentMk ⟨x, hx⟩) = cc G Uᶜ x := by
  have h1 : compSet G ((G.induce (setD G)).connectedComponentMk ⟨x, hx⟩) = cc G (setD G) x := by
    ext y
    simp only [compSet, Set.mem_ofPred_eq, ConnectedComponent.eq, cc]
    constructor
    · rintro ⟨hy, r⟩; exact ⟨hx, hy, r.symm⟩
    · rintro ⟨_, hy, r⟩; exact ⟨hy, r.symm⟩
  have hxO : x ∈ oddPart G U := setD_eq G hU ▸ hx
  rw [h1, setD_eq G hU, cc_eq_of_closed (oddPart_subset G U) (oddPart_closed G U) hxO]

lemma compSet_mem_oddComps [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    (c : (G.induce (setD G)).ConnectedComponent) : compSet G c ∈ oddComps G Uᶜ := by
  induction c using ConnectedComponent.ind with
  | h a =>
    obtain ⟨x, hx⟩ := a
    have hxO : x ∈ oddPart G U := setD_eq G hU ▸ hx
    rw [compSet_mk G hU]
    exact ⟨cc_mem_comps hxO.1, hxO.2⟩

lemma comps_setD [Finite V] {U : Set V} (hU : IsMinBarrier G U) :
    comps G (setD G) = oddComps G Uᶜ := by
  rw [setD_eq G hU, comps_of_closed (oddPart_subset G U) (oddPart_closed G U)]
  ext K
  constructor
  · rintro ⟨hK, hsub⟩
    obtain ⟨y, hy⟩ := comps_nonempty hK
    refine ⟨hK, ?_⟩
    rw [comps_eq_cc hK hy]
    exact (hsub hy).2
  · rintro ⟨hK, hodd⟩
    exact ⟨hK, fun y hy => ⟨comps_subset hK hy, by rw [← comps_eq_cc hK hy]; exact hodd⟩⟩

/-- Every connected component of `G[D(G)]` is factor-critical. -/
theorem factorCritical [Finite V] (c : (G.induce (setD G)).ConnectedComponent) :
    ∀ v ∈ compSet G c, HasPerfectMatchingOn G (compSet G c \ {v}) := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  intro v hv
  have hK := compSet_mem_oddComps G hU c
  obtain ⟨hvD, -⟩ := id hv
  obtain ⟨M, ⟨hM, hmax⟩, hvM⟩ := hvD
  obtain ⟨-, -, h1c, -⟩ := step1 hM (hU.1.eq hM hmax)
  refine ⟨M.induce (compSet G c \ {v}), ?_, rfl⟩
  intro w hw
  rcases h1c _ hK v hv w hw.1 (fun h => hw.2 h.symm) with ⟨z, -, hz⟩ | ⟨z, hzK, hz⟩
  · exact (hvM (M.edge_vert hz)).elim
  · have hzv : z ≠ v := fun h => hvM (h ▸ M.edge_vert hz.symm)
    exact ⟨z, ⟨hw, ⟨hzK, hzv⟩, hz⟩, fun z' h => hM.eq_of_adj_left h.2.2 hz⟩

/-- `G[C(G)]` has a perfect matching. -/
theorem perfectMatching_C [Finite V] : HasPerfectMatchingOn G (setC G) := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  obtain ⟨M, hM, hmax⟩ := exists_maximum G
  obtain ⟨-, -, -, h1d⟩ := step1 hM (hU.1.eq hM hmax)
  refine ⟨M.induce (setC G), ?_, rfl⟩
  intro w hw
  have hw' := (mem_setC_iff G hU w).1 hw
  obtain ⟨z, hz, hadj⟩ := h1d w hw'.1 hw'.2
  have hzC : z ∈ setC G :=
    (mem_setC_iff G hU z).2 ⟨cc_subset hz, by rw [cc_eq_of_mem hz]; exact hw'.2⟩
  exact ⟨z, ⟨hw, hzC, hadj⟩, fun z' h => hM.eq_of_adj_left h.2.2 hadj⟩

/-- The structure of every maximum matching. -/
theorem maximumMatching_structure [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    (∀ v ∈ setC G, ∃ w ∈ setC G, M.Adj v w) ∧
    (∀ a ∈ setA G, ∃ u ∈ setD G, M.Adj a u) ∧
    (∀ a ∈ setA G, ∀ a' ∈ setA G, ∀ u u' : ↥(setD G), a ≠ a' → M.Adj a u → M.Adj a' u' →
      (G.induce (setD G)).connectedComponentMk u ≠
        (G.induce (setD G)).connectedComponentMk u') ∧
    (∀ c : (G.induce (setD G)).ConnectedComponent, ∀ v ∈ compSet G c, ∀ w ∈ compSet G c,
      v ≠ w → (∃ x ∈ compSet G c, M.Adj v x) ∨ (∃ x ∈ compSet G c, M.Adj w x)) := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  obtain ⟨h1a, h1b, h1c, h1d⟩ := step1 hM.1 (hU.1.eq hM.1 hM.2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    have hv' := (mem_setC_iff G hU v).1 hv
    obtain ⟨z, hz, hadj⟩ := h1d v hv'.1 hv'.2
    exact ⟨z, (mem_setC_iff G hU z).2 ⟨cc_subset hz, by rw [cc_eq_of_mem hz]; exact hv'.2⟩,
      hadj⟩
  · intro a ha
    rw [setA_eq G hU] at ha
    obtain ⟨x, hx, hxU, hodd⟩ := h1a a ha
    exact ⟨x, by rw [setD_eq G hU]; exact ⟨hxU, hodd⟩, hx⟩
  · intro a ha a' ha' u u' hne hu hu' heq
    rw [setA_eq G hU] at ha ha'
    have h1 := compSet_mk G hU u.1 u.2
    have h2 := compSet_mk G hU u'.1 u'.2
    simp only [Subtype.coe_eta] at h1 h2
    rw [heq, h2] at h1
    exact h1b a ha a' ha' u u' hne hu hu' h1.symm
  · intro c v hv w hw hne
    exact h1c _ (compSet_mem_oddComps G hU c) v hv w hw hne

/-- **The Gallai–Edmonds formula.** For every maximum matching `M`,
`2|M| + c(D(G)) = |V| + |A(G)|`. -/
theorem two_mul_card_add [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    2 * M.edgeSet.ncard + Nat.card (G.induce (setD G)).ConnectedComponent =
      Nat.card V + (setA G).ncard := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  have heq := hU.1.eq hM.1 hM.2
  rw [ncard_verts_eq_two_mul hM.1] at heq
  rw [setA_eq G hU, natCard_components_eq, comps_setD G hU]
  exact heq

end GallaiEdmonds
