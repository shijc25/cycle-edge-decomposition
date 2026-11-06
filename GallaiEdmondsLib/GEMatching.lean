/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BergeLib.Berge
public import GallaiEdmondsLib.GEComponents

/-!
# Matchings and the Tutte–Berge formula in the language of component sets

Auxiliary material for the Gallai–Edmonds structure theorem: the Tutte–Berge inequality and
formula (from `BergeLib.Berge`) restated with `oddC`, a version restricted to a vertex set, and
the analysis of the equality case.
-/

@[expose] public section

open SimpleGraph

namespace GallaiEdmonds

variable {V : Type*} {G : SimpleGraph V}

open Finset in
lemma ncard_verts_eq_two_mul [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.1 hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  simp only [hdeg, Finset.sum_boole, Nat.cast_id] at h
  have e1 : M.verts.ncard = #{x | x ∈ M.verts} := by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have e2 : M.edgeSet.ncard = #M.spanningCoe.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset, Subgraph.edgeSet_spanningCoe]
  rw [e1, e2, h]

lemma even_ncard_verts [Finite V] {M : G.Subgraph} (hM : M.IsMatching) :
    Even M.verts.ncard := by
  rw [ncard_verts_eq_two_mul hM]; exact even_two_mul _

open Classical in
/-- The partner of a vertex in a matching. -/
noncomputable def partner {M : G.Subgraph} (hM : M.IsMatching) (y : V) : V :=
  if h : y ∈ M.verts then (hM h).choose else y

lemma partner_adj {M : G.Subgraph} (hM : M.IsMatching) {y : V} (hy : y ∈ M.verts) :
    M.Adj y (partner hM y) := by
  simp only [partner, hy, ↓reduceDIte]; exact (hM hy).choose_spec.1

lemma partner_eq {M : G.Subgraph} (hM : M.IsMatching) {y w : V} (h : M.Adj y w) :
    partner hM y = w :=
  hM.eq_of_adj_left (partner_adj hM (M.edge_vert h)) h

lemma oddC_le_ncard [Finite V] (H : SimpleGraph V) (W : Set V) : oddC H W ≤ W.ncard := by
  have hsub : oddComps H W ⊆ cc H W '' W := by
    rintro K ⟨⟨x, hx, rfl⟩, -⟩; exact ⟨x, hx, rfl⟩
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_image_le)

lemma oddC_congr_graph {H : SimpleGraph V} {W : Set V}
    (h : ∀ a ∈ W, ∀ b ∈ W, H.Adj a b ↔ G.Adj a b) : oddC H W = oddC G W := by
  have : oddComps H W = oddComps G W := by
    ext K
    simp only [oddComps, comps, cc_congr_graph h]
  rw [oddC, oddC, this]

/-- Tutte–Berge inequality. -/
lemma tb_le [Finite V] {M : G.Subgraph} (hM : M.IsMatching) (U : Set V) :
    M.verts.ncard + oddC G Uᶜ ≤ Nat.card V + U.ncard := by
  rw [ncard_verts_eq_two_mul hM, ← oddCount_eq]
  exact BergeMatching.two_mul_card_add_le hM U

/-- Tutte–Berge formula: a maximum matching and a set attaining equality. -/
lemma tb_eq [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by
  obtain ⟨M, U, hM, heq⟩ := BergeMatching.exists_tutte_berge G
  refine ⟨M, U, hM, fun M' hM' => ?_, ?_⟩
  · have := BergeMatching.two_mul_card_add_le hM' U
    omega
  · rw [ncard_verts_eq_two_mul hM, ← oddCount_eq]; exact heq

/-- Tutte–Berge restricted to a vertex set `S` (the `≥` half of the formula). -/
lemma tb_restricted [Finite V] (G : SimpleGraph V) (S : Set V) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.verts ⊆ S ∧ ∃ T ⊆ S,
      S.ncard + T.ncard ≤ N.verts.ncard + oddC G (S \ T) := by
  obtain ⟨M', T0, hM', heq⟩ := BergeMatching.exists_tutte_berge (restrictG G S)
  let N : G.Subgraph :=
    { verts := M'.verts, Adj := M'.Adj, adj_sub := fun h => (M'.adj_sub h).1,
      edge_vert := M'.edge_vert, symm := M'.symm }
  have hN : N.IsMatching := fun v hv => hM' hv
  have hNS : N.verts ⊆ S := fun v hv => by
    obtain ⟨w, hw, -⟩ := hM' hv; exact (M'.adj_sub hw).2.1
  refine ⟨N, hN, hNS, T0 ∩ S, Set.inter_subset_right, ?_⟩
  rw [oddCount_eq, ← ncard_verts_eq_two_mul hM'] at heq
  have hsub : S \ T0 ⊆ T0ᶜ := fun x hx => hx.2
  have hcl : Closed (restrictG G S) T0ᶜ (S \ T0) := fun y hy z hz hadj => ⟨hadj.2.2, hz⟩
  have hsplit := oddC_split hsub hcl
  have hcongr : oddC (restrictG G S) (S \ T0) = oddC G (S \ T0) :=
    oddC_congr_graph fun a ha b hb => ⟨fun h => h.1, fun h => ⟨h, ha.1, hb.1⟩⟩
  have hle := oddC_le_ncard (restrictG G S) (T0ᶜ \ (S \ T0))
  have hST : S \ (T0 ∩ S) = S \ T0 := by
    ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [hST]
  have h1 := Set.ncard_add_ncard_compl T0
  have h2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard T0ᶜ (S \ T0)
  have h3 : T0ᶜ ∩ (S \ T0) = S \ T0 := Set.inter_eq_right.mpr hsub
  have h4 := Set.ncard_inter_add_ncard_sdiff_eq_ncard S T0
  have h5 : (T0 ∩ S).ncard ≤ T0.ncard := Set.ncard_le_ncard Set.inter_subset_left
  have h6 : S ∩ T0 = T0 ∩ S := Set.inter_comm _ _
  rw [h3] at h2
  rw [h6] at h4
  change M'.verts.ncard + oddC G (S \ T0) ≥ _
  omega

/-- Equality analysis of the Tutte–Berge inequality. -/
theorem step1 [Finite V] {M : G.Subgraph} (hM : M.IsMatching) {U : Set V}
    (hEq : M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard) :
    (∀ u ∈ U, ∃ x, M.Adj u x ∧ x ∉ U ∧ Odd (cc G Uᶜ x).ncard) ∧
    (∀ u ∈ U, ∀ u' ∈ U, ∀ x x', u ≠ u' → M.Adj u x → M.Adj u' x' →
      cc G Uᶜ x ≠ cc G Uᶜ x') ∧
    (∀ K ∈ oddComps G Uᶜ, ∀ y ∈ K, ∀ z ∈ K, y ≠ z →
      (∃ w ∈ K, M.Adj y w) ∨ (∃ w ∈ K, M.Adj z w)) ∧
    (∀ y, y ∉ U → Even (cc G Uᶜ y).ncard → ∃ w ∈ cc G Uᶜ y, M.Adj y w) := by
  classical
  set B : Set V := {y | y ∉ U ∧ ¬∃ w ∈ cc G Uᶜ y, M.Adj y w} with hB
  have hP : ∀ K ∈ oddComps G Uᶜ, ∃ y ∈ K, y ∈ B := by
    intro K hK
    by_contra hcon
    push Not at hcon
    have hall : ∀ y ∈ K, ∃ w ∈ K, M.Adj y w := by
      intro y hy
      have h := hcon y hy
      simp only [hB, Set.mem_ofPred_eq, not_and, not_not] at h
      obtain ⟨w, hw, hadj⟩ := h (comps_subset hK.1 hy)
      exact ⟨w, by rwa [← comps_eq_cc hK.1 hy] at hw, hadj⟩
    have hMK : (M.induce K).IsMatching := by
      intro y hy
      obtain ⟨w, hw, hadj⟩ := hall y hy
      exact ⟨w, ⟨hy, hw, hadj⟩, fun w' h => hM.eq_of_adj_left h.2.2 hadj⟩
    have := even_ncard_verts hMK
    rw [Subgraph.induce_verts] at this
    exact (Nat.not_even_iff_odd.mpr hK.2) this
  -- lower bound
  have hsubimg : oddComps G Uᶜ ⊆ cc G Uᶜ '' B := by
    intro K hK
    obtain ⟨y, hyK, hyB⟩ := hP K hK
    exact ⟨y, hyB, (comps_eq_cc hK.1 hyK).symm⟩
  have hlow1 := Set.ncard_le_ncard hsubimg
  have hlow2 : (cc G Uᶜ '' B).ncard ≤ B.ncard := Set.ncard_image_le
  -- upper bound
  have hB1 : B \ M.verts ⊆ M.vertsᶜ ∩ Uᶜ := fun y hy => ⟨hy.2, hy.1.1⟩
  have hpmaps : ∀ y ∈ B ∩ M.verts, partner hM y ∈ U ∩ M.verts := by
    intro y hy
    have hadj := partner_adj hM hy.2
    refine ⟨?_, M.edge_vert hadj.symm⟩
    by_contra hU
    exact hy.1.2 ⟨_, mem_cc_of_adj (mem_cc_self hy.1.1) hU (M.adj_sub hadj), hadj⟩
  have hpinj : Set.InjOn (partner hM) (B ∩ M.verts) := by
    intro y hy z hz hyz
    have hy' := partner_adj hM hy.2
    have hz' := partner_adj hM hz.2
    rw [hyz] at hy'
    exact hM.eq_of_adj_right hy' hz'
  have hpimg : partner hM '' (B ∩ M.verts) ⊆ U ∩ M.verts := by
    rintro _ ⟨y, hy, rfl⟩; exact hpmaps y hy
  have hB2 : (B ∩ M.verts).ncard ≤ (U ∩ M.verts).ncard := by
    rw [← hpinj.ncard_image]; exact Set.ncard_le_ncard hpimg
  have hBsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard B M.verts
  have hB1le := Set.ncard_le_ncard hB1
  -- global counting
  have c1 := Set.ncard_add_ncard_compl M.verts
  have c2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard M.vertsᶜ U
  have c3 := Set.ncard_inter_add_ncard_sdiff_eq_ncard U M.verts
  have e1 : M.vertsᶜ \ U = M.vertsᶜ ∩ Uᶜ := rfl
  have e2 : U \ M.verts = M.vertsᶜ ∩ U :=
    Set.ext fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [e1] at c2
  rw [e2] at c3
  unfold oddC at hEq
  have hzero : (M.vertsᶜ ∩ U).ncard = 0 := by omega
  have hUM : U ⊆ M.verts := by
    intro u hu
    by_contra h
    rw [Set.ncard_eq_zero] at hzero
    exact (Set.eq_empty_iff_forall_notMem.mp hzero) u ⟨h, hu⟩
  -- consequences
  have himgeq : cc G Uᶜ '' B = oddComps G Uᶜ :=
    (Set.eq_of_subset_of_ncard_le hsubimg (by omega)).symm
  have hBodd : ∀ y ∈ B, Odd (cc G Uᶜ y).ncard := by
    intro y hy
    have : cc G Uᶜ y ∈ oddComps G Uᶜ := himgeq ▸ ⟨y, hy, rfl⟩
    exact this.2
  have hBinj : Set.InjOn (cc G Uᶜ) B := Set.injOn_of_ncard_image_eq (by omega)
  have hpsurj : partner hM '' (B ∩ M.verts) = U ∩ M.verts := by
    refine Set.eq_of_subset_of_ncard_le hpimg ?_
    rw [hpinj.ncard_image]; omega
  have hUB : ∀ u ∈ U, ∀ x, M.Adj u x → x ∈ B := by
    intro u hu x hx
    have : u ∈ partner hM '' (B ∩ M.verts) := hpsurj ▸ ⟨hu, hUM hu⟩
    obtain ⟨y, hy, rfl⟩ := this
    have := partner_adj hM hy.2
    rw [hM.eq_of_adj_left hx this.symm]
    exact hy.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    have hx := partner_adj hM (hUM hu)
    have hxB := hUB u hu _ hx
    exact ⟨_, hx, hxB.1, hBodd _ hxB⟩
  · intro u hu u' hu' x x' hne hx hx' hcc
    have hxx : x = x' := hBinj (hUB u hu x hx) (hUB u' hu' x' hx') hcc
    rw [hxx] at hx
    exact hne (hM.eq_of_adj_right hx hx')
  · intro K hK y hy z hz hne
    by_contra hcon
    push Not at hcon
    have hyB : y ∈ B := by
      refine ⟨comps_subset hK.1 hy, ?_⟩
      rw [← comps_eq_cc hK.1 hy]
      exact fun ⟨w, hw, h⟩ => hcon.1 w hw h
    have hzB : z ∈ B := by
      refine ⟨comps_subset hK.1 hz, ?_⟩
      rw [← comps_eq_cc hK.1 hz]
      exact fun ⟨w, hw, h⟩ => hcon.2 w hw h
    exact hne (hBinj hyB hzB (by rw [← comps_eq_cc hK.1 hy, ← comps_eq_cc hK.1 hz]))
  · intro y hy heven
    by_contra hcon
    exact (Nat.not_even_iff_odd.mpr (hBodd y ⟨hy, hcon⟩)) heven

end GallaiEdmonds
