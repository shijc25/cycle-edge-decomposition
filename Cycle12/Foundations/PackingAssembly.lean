import Cycle12.Foundations.PackingOperations

/-! Exact assembly of weighted cycle packings in edge-disjoint subgraphs.
Vertex sets may overlap arbitrarily. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I]

namespace CyclePacking
variable {G : SimpleGraph V}

def assemble (H : I → SimpleGraph V) (hle : ∀ i, H i ≤ G)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (Q : ∀ i, CyclePacking (H i)) : CyclePacking G :=
  ofIndexed (I := Σ i : I, Fin (Q i).count) (fun p => (Q p.1).parts p.2)
    (by
      rintro ⟨i, j⟩
      obtain ⟨v, p, hp, he⟩ := (Q i).cycles j
      exact ⟨v, p.mapLe (hle i), hp.mapLe _, by simpa using he⟩)
    (by
      rintro ⟨i, j⟩ ⟨k, l⟩ hne
      by_cases hik : i = k
      · subst k
        exact (Q i).disjoint (fun he => hne (by cases he; rfl))
      · exact (hd hik).mono ((Q i).parts_subset j) ((Q k).parts_subset l))

theorem assemble_count (H : I → SimpleGraph V) (hle : ∀ i, H i ≤ G)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (Q : ∀ i, CyclePacking (H i)) :
    (assemble H hle hd Q).count = ∑ i, (Q i).count := by
  simp only [assemble, ofIndexed, Fintype.card_sigma, Fintype.card_fin]

theorem assemble_used (H : I → SimpleGraph V) (hle : ∀ i, H i ≤ G)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (Q : ∀ i, CyclePacking (H i)) :
    (assemble H hle hd Q).used = ⋃ i, (Q i).used := by
  unfold assemble
  calc
    _ = ⋃ p : (Σ i : I, Fin (Q i).count), (Q p.1).parts p.2 :=
      used_ofIndexed _ _ _
    _ = ⋃ i, (Q i).used := by simp only [Set.iUnion_sigma, used]

theorem assemble_residue (H : I → SimpleGraph V) (hle : ∀ i, H i ≤ G)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (hu : (⋃ i, (H i).edgeSet) = G.edgeSet) (Q : ∀ i, CyclePacking (H i)) :
    (assemble H hle hd Q).residue.edgeSet = ⋃ i, (Q i).residue.edgeSet := by
  rw [residue, edgeSet_deleteEdges, assemble_used]
  ext e
  constructor
  · rintro ⟨he, hnot⟩
    rw [← hu] at he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [residue, edgeSet_deleteEdges]
    exact ⟨hi, fun h => hnot (Set.mem_iUnion.mpr ⟨i, h⟩)⟩
  · intro he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    rw [residue, edgeSet_deleteEdges] at hi
    refine ⟨edgeSet_mono (hle i) hi.1, ?_⟩
    intro hused
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hused
    by_cases hij : i = j
    · subst j
      exact hi.2 hj
    · exact Set.disjoint_left.mp (hd hij) hi.1 ((Q j).used_subset hj)

theorem assemble_singles (H : I → SimpleGraph V) (hle : ∀ i, H i ≤ G)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (hu : (⋃ i, (H i).edgeSet) = G.edgeSet) (Q : ∀ i, CyclePacking (H i)) :
    (assemble H hle hd Q).singles = ∑ i, (Q i).singles := by
  unfold singles
  rw [assemble_residue H hle hd hu]
  apply ncard_iUnion_disjoint
  intro i j hij
  exact (hd hij).mono (edgeSet_mono (Q i).residue_le) (edgeSet_mono (Q j).residue_le)

theorem assemble_cost (H : I → SimpleGraph V) (hle : ∀ i, H i ≤ G)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (hu : (⋃ i, (H i).edgeSet) = G.edgeSet) (Q : ∀ i, CyclePacking (H i)) :
    (assemble H hle hd Q).cost = ∑ i, (Q i).cost := by
  simp only [cost, assemble_count, assemble_singles H hle hd hu,
    sum_add_distrib, mul_sum]

end CyclePacking
end
end Cycle13
