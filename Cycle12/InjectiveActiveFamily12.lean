import OAI.Combinatorics.CycleDecomposition.BatchIndexing

namespace Cycle12
open OAI.ErdosGallai.Indexing
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The upstream active-family construction, strengthened to retain its
actual injective router assignment. This is needed for full-core quotient
lifting: a single batch contains at most one active block in each core. -/
theorem choose_injective_active_family {V R B : Type} [Fintype V] [Fintype R] [Fintype B]
    (F : SimpleGraph V) (Y : Finset V) (W : B → Finset V) (U : R → Finset V) (a L : ℝ)
    (hL : 0 ≤ L) (hW : ∀ b, W b ⊆ Y) (hU : ∀ r, U r ⊆ Y)
    (hcov : Y ⊆ univ.biUnion W) (hUd : Pairwise fun r s => Disjoint (U r) (U s)) :
    ∃ A : ActiveFamily F Y W U a L, ∀ b, Function.Injective (A.router b) := by
  classical
  let good := goodVertices F Y a
  let S (b : B) (r : R) := W b ∩ U r ∩ good
  let keep (b : B) (r : R) := L ≤ ((S b r).card:ℝ)
  let I (b : B) := {r : R // keep b r}
  let X (b : B) (i : I b) := S b i.val
  have hsum (b : B) : (∑ i : I b, ((X b i).card:ℝ)) =
      ∑ r, if keep b r then ((S b r).card:ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simpa only [Finset.subtype_univ] using (Finset.sum_subtype_eq_sum_filter (s := univ) (p := keep b) (fun r => ((S b r).card:ℝ)))
  have hadd := active_occurrences Y good W U hW hU hcov hUd keep
  dsimp only at hadd
  have hlow : (∑ r, ((U r).card:ℝ)) ≤
      (∑ b, ∑ r, if keep b r then ((S b r).card:ℝ) else 0) +
      (∑ b, ∑ r, if keep b r then 0 else ((S b r).card:ℝ)) + ((Y \ good).card:ℝ) := by
    exact_mod_cast hadd.1
  have hhigh : (∑ b, ∑ r, if keep b r then ((S b r).card:ℝ) else 0) + Y.card ≤
      (∑ r, ((U r).card:ℝ)) + ∑ b, ((W b).card:ℝ) := by exact_mod_cast hadd.2
  have hskip : (∑ b, ∑ r, if keep b r then 0 else ((S b r).card:ℝ)) ≤
      L * Fintype.card B * Fintype.card R := by
    calc
      _ ≤ ∑ _b : B, ∑ _r : R, L := by
        apply Finset.sum_le_sum; intro b _
        apply Finset.sum_le_sum; intro r _
        split_ifs with hk
        · exact hL
        · exact le_of_lt (lt_of_not_ge hk)
      _ = _ := by simp; ring
  refine ⟨{
    Index := I
    finite := fun _ => inferInstance
    vertices := X
    router := fun _ i => i.val
    subset_batch := fun _ _ => Finset.inter_subset_left.trans Finset.inter_subset_left
    subset_router := fun _ _ => Finset.inter_subset_left.trans Finset.inter_subset_right
    disjoint := ?_
    degree_le := ?_
    large := fun _ i => i.property
    lower := ?_
    upper := ?_ },fun _ => Subtype.val_injective⟩
  · intro b i j hij
    exact (hUd (fun h => hij (Subtype.ext h))).mono
      (Finset.inter_subset_left.trans Finset.inter_subset_right)
      (Finset.inter_subset_left.trans Finset.inter_subset_right)
  · intro b i v hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  · simp_rw [hsum]
    dsimp only [good] at hlow hskip
    linarith
  · simpa only [hsum] using hhigh


end
end Cycle12
