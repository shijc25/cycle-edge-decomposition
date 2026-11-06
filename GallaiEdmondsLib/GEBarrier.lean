/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BergeLib.Berge
public import GallaiEdmondsLib.GEMatching

/-!
# Barriers

Auxiliary material for the Gallai–Edmonds structure theorem. A *barrier* is a vertex set `U`
attaining equality in the Tutte–Berge formula. We work with a barrier `U` for which the set of
vertices lying in odd components of `G − U` is as small as possible, and show that the odd
components of `G − U` are factor-critical and that `U` has positive surplus towards them.
-/

@[expose] public section

open SimpleGraph

namespace GallaiEdmonds

variable {V : Type*} {G : SimpleGraph V}

/-- `U` attains equality in the Tutte–Berge formula. -/
def IsBarrier (G : SimpleGraph V) (U : Set V) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard

/-- The vertices lying in odd components of `G − U`. -/
def oddPart (G : SimpleGraph V) (U : Set V) : Set V := {y | y ∉ U ∧ Odd (cc G Uᶜ y).ncard}

/-- A barrier minimizing the number of vertices in odd components. -/
def IsMinBarrier (G : SimpleGraph V) (U : Set V) : Prop :=
  IsBarrier G U ∧ ∀ U', IsBarrier G U' → (oddPart G U).ncard ≤ (oddPart G U').ncard

lemma verts_le_of_max [Finite V] {M M' : G.Subgraph} (hM' : M'.IsMatching) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M'.verts.ncard ≤ M.verts.ncard := by
  rw [ncard_verts_eq_two_mul hM', ncard_verts_eq_two_mul hM]
  have := hmax M' hM'
  omega

lemma IsBarrier.eq [Finite V] {U : Set V} (hU : IsBarrier G U) {M : G.Subgraph}
    (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by
  obtain ⟨M0, hM0, h0⟩ := hU
  have := verts_le_of_max hM0 hM hmax
  have := tb_le hM U
  omega

lemma isBarrier_of_le [Finite V] {U : Set V} {M : G.Subgraph} (hM : M.IsMatching)
    (h : Nat.card V + U.ncard ≤ M.verts.ncard + oddC G Uᶜ) : IsBarrier G U :=
  ⟨M, hM, le_antisymm (tb_le hM U) h⟩

lemma exists_minBarrier [Finite V] (G : SimpleGraph V) : ∃ U, IsMinBarrier G U := by
  classical
  obtain ⟨M, U, hM, -, h⟩ := tb_eq G
  have hex : ∃ n, ∃ U, IsBarrier G U ∧ (oddPart G U).ncard = n := ⟨_, U, ⟨M, hM, h⟩, rfl⟩
  obtain ⟨U0, hU0, hn⟩ := Nat.find_spec hex
  refine ⟨U0, hU0, fun U' hU' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨U', hU', rfl⟩

/-- The odd components of `G − U` are factor-critical, for a minimal barrier `U`. -/
lemma minBarrier_factorCritical [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {K : Set V} (hK : K ∈ oddComps G Uᶜ) {v : V} (hv : v ∈ K) :
    ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ {v} := by
  by_contra hno
  push Not at hno
  set S := K \ {v} with hS
  obtain ⟨N, hN, hNS, T, hTS, hineq⟩ := tb_restricted G S
  have hNne : N.verts ≠ S := hno N hN
  have hlt : N.verts.ncard < S.ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hNS, hNne⟩)
  have hSK : S.ncard + 1 = K.ncard := Set.ncard_sdiff_singleton_add_one hv
  have hev := even_ncard_verts hN
  have hodd := hK.2
  have hlt2 : N.verts.ncard + 2 ≤ S.ncard := by
    obtain ⟨a, ha⟩ := hev; obtain ⟨b, hb⟩ := hodd; omega
  set U' := U ∪ insert v T with hU'
  have hvU : v ∉ U := comps_subset hK.1 hv
  have hTK : T ⊆ K := fun t ht => (hTS ht).1
  have hTv : v ∉ T := fun h => (hTS h).2 rfl
  have hTU : Disjoint U (insert v T) := by
    rw [Set.disjoint_left]
    intro x hxU hx
    rcases hx with rfl | hx
    · exact hvU hxU
    · exact comps_subset hK.1 (hTK hx) hxU
  have hcardU' : U'.ncard = U.ncard + T.ncard + 1 := by
    rw [hU', Set.ncard_union_eq hTU, Set.ncard_insert_of_notMem hTv]
    ring
  have hsub1 : S \ T ⊆ U'ᶜ := by
    intro x hx
    simp only [hU', Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, not_or]
    exact ⟨comps_subset hK.1 hx.1.1, hx.1.2, hx.2⟩
  have hcl1 : Closed G U'ᶜ (S \ T) := by
    intro y hy z hz hadj
    simp only [hU', Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, not_or] at hz
    exact ⟨⟨comps_closed hK.1 y hy.1.1 z hz.1 hadj, hz.2.1⟩, hz.2.2⟩
  have hrest : U'ᶜ \ (S \ T) = Uᶜ \ K := by
    ext x
    simp only [hU', hS, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
    constructor
    · rintro ⟨⟨hxU, hxv, hxT⟩, h⟩
      exact ⟨hxU, fun hxK => h ⟨⟨hxK, hxv⟩, hxT⟩⟩
    · rintro ⟨hxU, hxK⟩
      exact ⟨⟨hxU, fun h => hxK (h ▸ hv), fun h => hxK (hTK h)⟩, fun h => hxK h.1.1⟩
  have hsplit1 := oddC_split hsub1 hcl1
  rw [hrest] at hsplit1
  have hsplit2 := oddC_split (comps_subset hK.1) (comps_closed hK.1)
  have hK1 : oddC G K = 1 := by rw [oddC, oddComps_self hK.1 hK.2, Set.ncard_singleton]
  have heq := hU.1.eq hM hmax
  have hU'bar : IsBarrier G U' := isBarrier_of_le hM (by omega)
  have hsubOP : oddPart G U' ⊆ oddPart G U \ {v} := by
    rintro y ⟨hyU', hyodd⟩
    by_cases hyST : y ∈ S \ T
    · refine ⟨⟨comps_subset hK.1 hyST.1.1, ?_⟩, hyST.1.2⟩
      rw [← comps_eq_cc hK.1 hyST.1.1]
      exact hK.2
    · have hy0 : y ∈ U'ᶜ \ (S \ T) := ⟨hyU', hyST⟩
      have hy1 : y ∈ Uᶜ \ K := hrest ▸ hy0
      have e1 : cc G (U'ᶜ \ (S \ T)) y = cc G U'ᶜ y :=
        cc_eq_of_closed Set.sdiff_subset (closed_compl hcl1) hy0
      have e2 : cc G (Uᶜ \ K) y = cc G Uᶜ y :=
        cc_eq_of_closed Set.sdiff_subset (closed_compl (comps_closed hK.1)) hy1
      rw [hrest] at e1
      refine ⟨⟨hy1.1, ?_⟩, ?_⟩
      · rw [← e2, e1]; exact hyodd
      · rintro rfl; exact hy1.2 hv
  have hvOP : v ∈ oddPart G U := ⟨hvU, by rw [← comps_eq_cc hK.1 hv]; exact hK.2⟩
  have h1 := Set.ncard_le_ncard hsubOP
  have h2 : (oddPart G U \ {v}).ncard < (oddPart G U).ncard :=
    Set.ncard_sdiff_singleton_lt_of_mem hvOP
  have h3 := hU.2 U' hU'bar
  omega

/-- Hall's condition with surplus: every `s ⊆ U` is adjacent to at least `|s|` odd components
other than the component of a given vertex `v` of an odd component. -/
lemma minBarrier_surplus [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {v : V} (hv : v ∈ oddPart G U) {s : Set V} (hs : s ⊆ U) :
    s.ncard ≤
      {K | K ∈ oddComps G Uᶜ ∧ K ≠ cc G Uᶜ v ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x}.ncard := by
  by_contra hlt
  push Not at hlt
  set K0 := cc G Uᶜ v with hK0
  set N := {K | K ∈ oddComps G Uᶜ ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x} with hNdef
  set N' := {K | K ∈ oddComps G Uᶜ ∧ K ≠ K0 ∧ ∃ u ∈ s, ∃ x ∈ K, G.Adj u x} with hN'def
  have heq := hU.1.eq hM hmax
  obtain ⟨h1a, h1b, -, -⟩ := step1 hM heq
  have hsN : s.ncard ≤ N.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun u => cc G Uᶜ (partner hM u)) ?_ ?_
    · intro u hu
      obtain ⟨x, hx, hxU, hodd⟩ := h1a u (hs hu)
      simp only [partner_eq hM hx]
      exact ⟨⟨cc_mem_comps hxU, hodd⟩, u, hu, x, mem_cc_self hxU, M.adj_sub hx⟩
    · intro u hu u' hu' h
      by_contra hne
      obtain ⟨x, hx, -⟩ := h1a u (hs hu)
      obtain ⟨x', hx', -⟩ := h1a u' (hs hu')
      simp only [partner_eq hM hx, partner_eq hM hx'] at h
      exact h1b u (hs hu) u' (hs hu') x x' hne hx hx' h
  have hNsub : N ⊆ insert K0 N' := by
    rintro K ⟨hK, hadj⟩
    by_cases h : K = K0
    · exact Or.inl h
    · exact Or.inr ⟨hK, h, hadj⟩
  have hK0N : K0 ∈ N := by
    by_contra hK0
    have : N ⊆ N' := fun K hK => ⟨hK.1, fun h => hK0 (h ▸ hK), hK.2⟩
    have := Set.ncard_le_ncard this
    omega
  have hNle : N.ncard ≤ N'.ncard + 1 :=
    (Set.ncard_le_ncard hNsub).trans (Set.ncard_insert_le _ _)
  set U' := U \ s with hU'
  set Q := oddComps G Uᶜ \ N with hQ
  have hQsub : Q ⊆ oddComps G U'ᶜ := by
    rintro K ⟨hK, hKN⟩
    obtain ⟨x, hx⟩ := comps_nonempty hK.1
    have hKU' : K ⊆ U'ᶜ := fun y hy hyU' => comps_subset hK.1 hy hyU'.1
    have hcl : Closed G U'ᶜ K := by
      intro y hy z hz hadj
      by_cases hzU : z ∈ U
      · exfalso
        have hzs : z ∈ s := by
          by_contra h
          exact hz ⟨hzU, h⟩
        exact hKN ⟨hK, z, hzs, y, hy, hadj.symm⟩
      · exact comps_closed hK.1 y hy z hzU hadj
    refine ⟨⟨x, hKU' hx, ?_⟩, hK.2⟩
    rw [← cc_eq_of_closed hKU' hcl hx,
      cc_eq_of_closed (comps_subset hK.1) (comps_closed hK.1) hx, comps_eq_cc hK.1 hx]
  have hNodd : N ⊆ oddComps G Uᶜ := fun K hK => hK.1
  have hQcard : Q.ncard + N.ncard = (oddComps G Uᶜ).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hNodd
  have hU'card : U'.ncard + s.ncard = U.ncard := Set.ncard_sdiff_add_ncard_of_subset hs
  have hQle := Set.ncard_le_ncard hQsub
  unfold oddC at heq
  have hU'bar : IsBarrier G U' := isBarrier_of_le hM (by unfold oddC; omega)
  have heq' := hU'bar.eq hM hmax
  unfold oddC at heq'
  have hQeq : Q = oddComps G U'ᶜ := Set.eq_of_subset_of_ncard_le hQsub (by omega)
  have hsubOP : oddPart G U' ⊆ oddPart G U \ K0 := by
    rintro y ⟨hyU', hyodd⟩
    have hK : cc G U'ᶜ y ∈ Q := hQeq ▸ ⟨cc_mem_comps hyU', hyodd⟩
    have hyK : y ∈ cc G U'ᶜ y := mem_cc_self hyU'
    have hyUc : y ∈ Uᶜ := comps_subset hK.1.1 hyK
    have hcc : cc G U'ᶜ y = cc G Uᶜ y := comps_eq_cc hK.1.1 hyK
    refine ⟨⟨hyUc, ?_⟩, fun hyK0 => ?_⟩
    · rw [← hcc]; exact hK.1.2
    · have : cc G U'ᶜ y = K0 := comps_eq_of_mem hK.1.1 (cc_mem_comps hv.1) hyK hyK0
      exact hK.2 (this ▸ hK0N)
  have hvK0 : v ∈ K0 := mem_cc_self hv.1
  have h1 := Set.ncard_le_ncard hsubOP
  have h2 : (oddPart G U \ K0).ncard < (oddPart G U).ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset,
      fun h => (by rw [h]; exact hv : v ∈ oddPart G U \ K0).2 hvK0⟩)
  have h3 := hU.2 U' hU'bar
  omega

end GallaiEdmonds
