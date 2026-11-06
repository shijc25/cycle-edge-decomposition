/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import BergeLib.Berge

/-!
# Connected components as vertex sets

Auxiliary material for the Gallai–Edmonds structure theorem: the components of an induced
subgraph `G[W]` described as subsets of `V`, and the translation of
`BergeMatching.oddCount` into this language.
-/

@[expose] public section

open SimpleGraph

namespace GallaiEdmonds

variable {V : Type*}

/-- The vertex set of the component of `x` in `G[W]` (empty if `x ∉ W`). -/
def cc (G : SimpleGraph V) (W : Set V) (x : V) : Set V :=
  {y | ∃ (hx : x ∈ W) (hy : y ∈ W), (G.induce W).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- The vertex sets of the connected components of `G[W]`. -/
def comps (G : SimpleGraph V) (W : Set V) : Set (Set V) := {S | ∃ x ∈ W, S = cc G W x}

/-- The vertex sets of the odd connected components of `G[W]`. -/
def oddComps (G : SimpleGraph V) (W : Set V) : Set (Set V) :=
  {S | S ∈ comps G W ∧ Odd S.ncard}

/-- The number of odd connected components of `G[W]`. -/
noncomputable def oddC (G : SimpleGraph V) (W : Set V) : ℕ := (oddComps G W).ncard

/-- The graph `G` with only the edges inside `S`. -/
def restrictG (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.1 _ h.1⟩

variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}

lemma mem_cc_self (hx : x ∈ W) : x ∈ cc G W x := ⟨hx, hx, Reachable.refl _⟩

lemma cc_subset : cc G W x ⊆ W := fun _ ⟨_, hy, _⟩ => hy

lemma mem_of_mem_cc (h : y ∈ cc G W x) : x ∈ W := h.1

lemma cc_of_not_mem (hx : x ∉ W) : cc G W x = ∅ := by
  ext y; exact ⟨fun h => (hx h.1).elim, fun h => h.elim⟩

lemma cc_symm (h : y ∈ cc G W x) : x ∈ cc G W y := by
  obtain ⟨hx, hy, r⟩ := h; exact ⟨hy, hx, r.symm⟩

lemma cc_eq_of_mem (h : y ∈ cc G W x) : cc G W y = cc G W x := by
  obtain ⟨hx, hy, r⟩ := h
  ext z; constructor
  · rintro ⟨_, hz, r'⟩; exact ⟨hx, hz, r.trans r'⟩
  · rintro ⟨_, hz, r'⟩; exact ⟨hy, hz, r.symm.trans r'⟩

lemma mem_cc_of_adj (h : y ∈ cc G W x) (hz : z ∈ W) (hadj : G.Adj y z) : z ∈ cc G W x := by
  obtain ⟨hx, hy, r⟩ := h
  exact ⟨hx, hz, r.trans (Adj.reachable (G := G.induce W) (u := ⟨y, hy⟩) (v := ⟨z, hz⟩) hadj)⟩

lemma cc_subset_of_closed (hxS : x ∈ S) (hS : ∀ y ∈ S, ∀ z ∈ W, G.Adj y z → z ∈ S) :
    cc G W x ⊆ S := by
  rintro y ⟨hx, hy, ⟨p⟩⟩
  suffices h : ∀ (a b : W) (_ : (G.induce W).Walk a b), a.1 ∈ S → b.1 ∈ S from h _ _ p hxS
  intro a b p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun ha => ih (hS _ ha _ (Subtype.prop _) h)

lemma cc_mono (h : W' ⊆ W) : cc G W' x ⊆ cc G W x := by
  by_cases hx : x ∈ W'
  · exact cc_subset_of_closed (mem_cc_self (h hx)) fun y hy z hz hadj =>
      mem_cc_of_adj hy (h hz) hadj
  · rw [cc_of_not_mem hx]; exact Set.empty_subset _

/-- A subset `W'` of `W` is closed in `W` if no edge of `G[W]` leaves it. -/
def Closed (G : SimpleGraph V) (W W' : Set V) : Prop := ∀ y ∈ W', ∀ z ∈ W, G.Adj y z → z ∈ W'

lemma cc_eq_of_closed (hW : W' ⊆ W) (hc : Closed G W W') (hx : x ∈ W') :
    cc G W' x = cc G W x := by
  refine (cc_mono hW).antisymm (cc_subset_of_closed (mem_cc_self hx) fun y hy z hz hadj => ?_)
  exact mem_cc_of_adj hy (hc y (cc_subset hy) z hz hadj) hadj

lemma cc_congr_graph {H : SimpleGraph V} (h : ∀ a ∈ W, ∀ b ∈ W, H.Adj a b ↔ G.Adj a b) :
    cc H W x = cc G W x := by
  by_cases hx : x ∈ W
  · refine (cc_subset_of_closed (mem_cc_self hx) fun y hy z hz hadj => ?_).antisymm
      (cc_subset_of_closed (mem_cc_self hx) fun y hy z hz hadj => ?_)
    · exact mem_cc_of_adj hy hz ((h y (cc_subset hy) z hz).1 hadj)
    · exact mem_cc_of_adj hy hz ((h y (cc_subset hy) z hz).2 hadj)
  · rw [cc_of_not_mem hx, cc_of_not_mem hx]

/-! ### Components -/

lemma cc_mem_comps (hx : x ∈ W) : cc G W x ∈ comps G W := ⟨x, hx, rfl⟩

lemma comps_subset {K : Set V} (hK : K ∈ comps G W) : K ⊆ W := by
  obtain ⟨x, -, rfl⟩ := hK; exact cc_subset

lemma comps_nonempty {K : Set V} (hK : K ∈ comps G W) : K.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hK; exact ⟨x, mem_cc_self hx⟩

lemma comps_eq_cc {K : Set V} (hK : K ∈ comps G W) (hy : y ∈ K) : K = cc G W y := by
  obtain ⟨x, -, rfl⟩ := hK; exact (cc_eq_of_mem hy).symm

lemma comps_eq_of_mem {K K' : Set V} (hK : K ∈ comps G W) (hK' : K' ∈ comps G W)
    (hy : y ∈ K) (hy' : y ∈ K') : K = K' := by
  rw [comps_eq_cc hK hy, comps_eq_cc hK' hy']

lemma comps_closed {K : Set V} (hK : K ∈ comps G W) : Closed G W K := by
  obtain ⟨x, -, rfl⟩ := hK
  exact fun y hy z hz hadj => mem_cc_of_adj hy hz hadj

lemma comps_of_closed (hW : W' ⊆ W) (hc : Closed G W W') :
    comps G W' = {K | K ∈ comps G W ∧ K ⊆ W'} := by
  ext K; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [cc_eq_of_closed hW hc hx]; exact cc_mem_comps (hW hx), cc_subset⟩
  · rintro ⟨hK, hKW'⟩
    obtain ⟨x, hx⟩ := comps_nonempty hK
    refine ⟨x, hKW' hx, ?_⟩
    rw [cc_eq_of_closed hW hc (hKW' hx), comps_eq_cc hK hx]

lemma oddComps_of_closed (hW : W' ⊆ W) (hc : Closed G W W') :
    oddComps G W' = {K | K ∈ oddComps G W ∧ K ⊆ W'} := by
  ext K
  simp only [oddComps, comps_of_closed hW hc, Set.mem_ofPred_eq]
  tauto

lemma comps_self {K : Set V} (hK : K ∈ comps G W) : comps G K = {K} := by
  rw [comps_of_closed (comps_subset hK) (comps_closed hK)]
  ext K'
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hK', hsub⟩
    obtain ⟨y, hy⟩ := comps_nonempty hK'
    exact comps_eq_of_mem hK' hK hy (hsub hy)
  · rintro rfl; exact ⟨hK, le_rfl⟩

lemma oddComps_self {K : Set V} (hK : K ∈ comps G W) (hodd : Odd K.ncard) :
    oddComps G K = {K} := by
  ext K'
  simp only [oddComps, comps_self hK, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hodd⟩

lemma closed_compl (hc : Closed G W W') : Closed G W (W \ W') := by
  intro y hy z hz hadj
  exact ⟨hz, fun hz' => hy.2 (hc z hz' y hy.1 hadj.symm)⟩

lemma closed_iUnion_comps {Q : Set (Set V)} (hQ : Q ⊆ comps G W) : Closed G W (⋃₀ Q) := by
  rintro y ⟨K, hKQ, hyK⟩ z hz hadj
  exact ⟨K, hKQ, comps_closed (hQ hKQ) y hyK z hz hadj⟩

/-- Splitting `W` into a closed part and its complement splits the odd components. -/
lemma oddC_split [Finite V] (hW : W' ⊆ W) (hc : Closed G W W') :
    oddC G W = oddC G W' + oddC G (W \ W') := by
  have h1 := oddComps_of_closed hW hc
  have h2 := oddComps_of_closed (Set.sdiff_subset) (closed_compl hc)
  have hU : oddComps G W = oddComps G W' ∪ oddComps G (W \ W') := by
    rw [h1, h2]
    ext K
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hK
      obtain ⟨y, hy⟩ := comps_nonempty hK.1
      by_cases hyW' : y ∈ W'
      · left
        refine ⟨hK, ?_⟩
        rw [comps_eq_cc hK.1 hy, ← cc_eq_of_closed hW hc hyW']
        exact cc_subset
      · right
        refine ⟨hK, ?_⟩
        have hyd : y ∈ W \ W' := ⟨comps_subset hK.1 hy, hyW'⟩
        rw [comps_eq_cc hK.1 hy, ← cc_eq_of_closed Set.sdiff_subset (closed_compl hc) hyd]
        exact cc_subset
    · rintro (h | h) <;> exact h.1
  have hD : Disjoint (oddComps G W') (oddComps G (W \ W')) := by
    rw [Set.disjoint_left]
    intro K hK hK'
    obtain ⟨y, hy⟩ := comps_nonempty hK.1
    exact (comps_subset hK'.1 hy).2 (comps_subset hK.1 hy)
  unfold oddC
  rw [hU, Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _)]

/-! ### Translation to Mathlib's connected components -/

lemma image_supp_mk (H : SimpleGraph V) (W : Set V) (a : W) :
    Subtype.val '' ((H.induce W).connectedComponentMk a).supp = cc H W a.1 := by
  ext y
  simp only [Set.mem_image, ConnectedComponent.mem_supp_iff,
    ConnectedComponent.eq]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨a.2, b.2, hb.symm⟩
  · rintro ⟨_, hy, r⟩; exact ⟨⟨y, hy⟩, r.symm, rfl⟩

lemma image_supp_injective (H : SimpleGraph V) (W : Set V) :
    Function.Injective fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp :=
  (Set.image_injective.mpr Subtype.val_injective).comp ConnectedComponent.supp_injective

lemma image_univ_supp (H : SimpleGraph V) (W : Set V) :
    (fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp) '' Set.univ =
      comps H W := by
  ext K; constructor
  · rintro ⟨c, -, rfl⟩
    induction c using ConnectedComponent.ind with
    | h a => exact ⟨a.1, a.2, image_supp_mk H W a⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, Set.mem_univ _, image_supp_mk H W ⟨x, hx⟩⟩

lemma image_odd_supp [Finite V] (H : SimpleGraph V) (W : Set V) :
    (fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp) ''
      (H.induce W).oddComponents = oddComps H W := by
  ext K; constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← image_univ_supp]; exact ⟨c, Set.mem_univ _, rfl⟩
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective]; exact hc
  · rintro ⟨hK, hodd⟩
    rw [← image_univ_supp] at hK
    obtain ⟨c, -, rfl⟩ := hK
    refine ⟨c, ?_, rfl⟩
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hodd
    exact hodd

lemma natCard_components_eq [Finite V] (H : SimpleGraph V) (W : Set V) :
    Nat.card (H.induce W).ConnectedComponent = (comps H W).ncard := by
  rw [← image_univ_supp, Set.ncard_image_of_injective _ (image_supp_injective H W),
    Set.ncard_univ]

lemma oddComponents_ncard_eq [Finite V] (H : SimpleGraph V) (W : Set V) :
    (H.induce W).oddComponents.ncard = oddC H W := by
  rw [oddC, ← image_odd_supp, Set.ncard_image_of_injective _ (image_supp_injective H W)]

lemma oddCount_eq [Finite V] (H : SimpleGraph V) (U : Set V) :
    BergeMatching.oddCount H U = oddC H Uᶜ := by
  have h : (⊤ : H.Subgraph).deleteVerts U = (⊤ : H.Subgraph).induce Uᶜ := by
    ext a b
    · simp [Set.compl_eq_univ_sdiff]
    · simp only [Subgraph.verts_top, Set.mem_univ, Subgraph.top_adj,
        true_and, Subgraph.induce_adj, Set.mem_compl_iff, Set.mem_sdiff]
  have e := induce_eq_coe_induce_top (G := H) Uᶜ
  rw [BergeMatching.oddCount, h]
  exact (congrArg (fun K : SimpleGraph (Uᶜ : Set V) => K.oddComponents.ncard) e).symm.trans
    (oddComponents_ncard_eq H Uᶜ)

end GallaiEdmonds
