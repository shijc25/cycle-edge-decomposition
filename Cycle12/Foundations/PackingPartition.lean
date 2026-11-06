import Cycle12.Foundations.PackingOperations

/-! Restrict a packing to edge-disjoint copies when every cycle lies in one copy.
The proof accounts for both cycles and every remaining singleton edge. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I : Type} [Fintype V] [Fintype W] [Fintype I]

theorem packing_cost_partition (G : SimpleGraph V) (H : SimpleGraph W)
    (f : I → G →g H) (hf : ∀ i, Function.Injective (f i))
    (hd : Pairwise (fun i j => Disjoint (Sym2.map (f i) '' G.edgeSet)
      (Sym2.map (f j) '' G.edgeSet)))
    (hu : (⋃ i, Sym2.map (f i) '' G.edgeSet) = H.edgeSet)
    (hc : ∀ (v : W) (p : H.Walk v v), p.IsCycle →
      ∃ (i : I) (u : V) (q : G.Walk u u), q.IsCycle ∧
        p.edgeSet = Sym2.map (f i) '' q.edgeSet)
    (P : CyclePacking H) :
    ∃ Q : I → CyclePacking G, (∑ i, (Q i).cost) = P.cost := by
  classical
  have hlocal : ∀ j : Fin P.count,
      ∃ (i : I) (u : V) (q : G.Walk u u), q.IsCycle ∧
        P.parts j = Sym2.map (f i) '' q.edgeSet := by
    intro j
    obtain ⟨v, p, hp, he⟩ := P.cycles j
    obtain ⟨i, u, q, hq, heq⟩ := hc v p hp
    exact ⟨i, u, q, hq, he.trans heq⟩
  choose a u q hq he using hlocal
  let J := fun i : I => {j : Fin P.count // a j = i}
  let parts := fun i (j : J i) => Sym2.map (f i) ⁻¹' P.parts j.1
  have hcycles : ∀ i (j : J i), ∃ (v : V) (p : G.Walk v v),
      p.IsCycle ∧ parts i j = p.edgeSet := by
    intro i j
    refine ⟨u j.1, q j.1, hq j.1, ?_⟩
    dsimp only [parts]
    rw [he j.1, j.2]
    exact Set.preimage_image_eq _ (Sym2.map.injective (hf i))
  have hpartsdisj : ∀ i, Pairwise (fun j k : J i => Disjoint (parts i j) (parts i k)) := by
    intro i j k hjk
    exact (P.disjoint (fun h => hjk (Subtype.ext h))).preimage _
  let Q := fun i => CyclePacking.ofIndexed (parts i) (hcycles i) (hpartsdisj i)
  have hused : ∀ i, (Q i).used = ⋃ j : J i, parts i j :=
    fun i => CyclePacking.used_ofIndexed _ _ _
  have hpartsub : ∀ j, P.parts j ⊆ Sym2.map (f (a j)) '' G.edgeSet := by
    intro j
    rw [he j]
    exact Set.image_mono (q j).edges_subset_edgeSet
  have hmap : ∀ i e, e ∈ G.edgeSet → Sym2.map (f i) e ∈ H.edgeSet := by
    intro i e heG
    induction e using Sym2.ind with
    | _ x y => exact (f i).map_adj heG
  have hresidue : ∀ i e, e ∈ (Q i).residue.edgeSet ↔
      e ∈ G.edgeSet ∧ Sym2.map (f i) e ∈ P.residue.edgeSet := by
    intro i e
    rw [show (Q i).residue.edgeSet = G.edgeSet \ (Q i).used from G.edgeSet_deleteEdges _]
    change (e ∈ G.edgeSet ∧ e ∉ (Q i).used) ↔
      e ∈ G.edgeSet ∧ Sym2.map (f i) e ∈ P.residue.edgeSet
    rw [hused i]
    constructor
    · rintro ⟨heG, heQ⟩
      refine ⟨heG, ?_⟩
      rw [CyclePacking.residue, edgeSet_deleteEdges]
      refine ⟨hmap i e heG, ?_⟩
      intro heP
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heP
      have hai : a j = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hd hne) (hpartsub j hj) ⟨e, heG, rfl⟩
      exact heQ (Set.mem_iUnion.mpr ⟨⟨j, hai⟩, hj⟩)
    · rintro ⟨heG, heP⟩
      refine ⟨heG, ?_⟩
      intro heQ
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heQ
      rw [CyclePacking.residue, edgeSet_deleteEdges] at heP
      exact heP.2 (Set.mem_iUnion.mpr ⟨j.1, hj⟩)
  let R := fun i => Sym2.map (f i) '' (Q i).residue.edgeSet
  have hRdisj : Pairwise (fun i j => Disjoint (R i) (R j)) := by
    intro i j hij
    exact (hd hij).mono
      (Set.image_mono (SimpleGraph.edgeSet_mono (Q i).residue_le))
      (Set.image_mono (SimpleGraph.edgeSet_mono (Q j).residue_le))
  have hRcover : (⋃ i, R i) = P.residue.edgeSet := by
    ext e
    constructor
    · intro heR
      obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp heR
      exact (hresidue i x).mp hx |>.2
    · intro heP
      have heH := SimpleGraph.edgeSet_mono P.residue_le heP
      rw [← hu] at heH
      obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp heH
      exact Set.mem_iUnion.mpr ⟨i, x, (hresidue i x).mpr ⟨hx, heP⟩, rfl⟩
  have hcounts : ∑ i, (Q i).count = P.count := by
    change (∑ i, Fintype.card (J i)) = P.count
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv a)).trans (Fintype.card_fin _)
  have hsingles : ∑ i, (Q i).singles = P.singles := by
    calc
      _ = ∑ i, (R i).ncard := by
        apply sum_congr rfl
        intro i _
        exact (Set.ncard_image_of_injective _ (Sym2.map.injective (hf i))).symm
      _ = (⋃ i, R i).ncard := (ncard_iUnion_disjoint R hRdisj).symm
      _ = P.singles := by rw [hRcover]; rfl
  refine ⟨Q, ?_⟩
  simp only [CyclePacking.cost, sum_add_distrib, ← mul_sum, hcounts, hsingles]

theorem packing_cost_copies_lower_bound (G : SimpleGraph V) (H : SimpleGraph W)
    (f : I → G →g H) (hf : ∀ i, Function.Injective (f i))
    (hd : Pairwise (fun i j => Disjoint (Sym2.map (f i) '' G.edgeSet)
      (Sym2.map (f j) '' G.edgeSet)))
    (hu : (⋃ i, Sym2.map (f i) '' G.edgeSet) = H.edgeSet)
    (hc : ∀ (v : W) (p : H.Walk v v), p.IsCycle →
      ∃ (i : I) (u : V) (q : G.Walk u u), q.IsCycle ∧
        p.edgeSet = Sym2.map (f i) '' q.edgeSet)
    (M : ℕ) (hM : ∀ Q : CyclePacking G, M ≤ Q.cost) (P : CyclePacking H) :
    Fintype.card I * M ≤ P.cost := by
  obtain ⟨Q, hQ⟩ := packing_cost_partition G H f hf hd hu hc P
  rw [← hQ]
  calc
    _ = ∑ _i : I, M := by simp
    _ ≤ _ := sum_le_sum (fun i _ => hM (Q i))

end
end Cycle13
