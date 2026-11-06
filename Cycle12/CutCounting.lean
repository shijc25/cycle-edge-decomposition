import Mathlib

/-! Undirected cut edges are counted once, using the actual edge set of a simple graph. -/
namespace Cycle12

universe u
variable {V : Type u}
open scoped Classical
open Finset

def Crosses (S T : Finset V) (e : Sym2 V) : Prop :=
  ∃ v ∈ S, ∃ w ∈ T, e = s(v,w)

theorem crosses_pair (S T : Finset V) (v w : V) :
    Crosses S T s(v,w) ↔ (v ∈ S ∧ w ∈ T) ∨ (w ∈ S ∧ v ∈ T) := by
  simp only [Crosses, Sym2.eq_iff]
  aesop

noncomputable def cutIndicator (G : SimpleGraph V) (S T : Finset V) (e : Sym2 V) : ℕ :=
  if e ∈ G.edgeSet ∧ Crosses S T e then 1 else 0

noncomputable def cutCount [Fintype V] (G : SimpleGraph V) (S T : Finset V) : ℕ :=
  ∑ e : Sym2 V, cutIndicator G S T e

noncomputable def boundaryCount [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  cutCount G S Sᶜ

theorem cutCount_eq_filter_card [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    cutCount G S T = (G.edgeFinset.filter (Crosses S T)).card := by
  simp only [cutCount, cutIndicator, Finset.sum_boole, Nat.cast_id]
  congr 1
  ext e
  simp

theorem boundaryCount_empty [Fintype V] (G : SimpleGraph V) : boundaryCount G ∅ = 0 := by
  simp [boundaryCount, cutCount, cutIndicator, Crosses]

theorem boundary_union_le [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    boundaryCount G (S ∪ T) ≤ boundaryCount G S + cutCount G T (S ∪ T)ᶜ := by
  unfold boundaryCount cutCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  induction e using Sym2.ind with
  | _ v w =>
    simp only [cutIndicator, crosses_pair, mem_union, mem_compl]
    by_cases hvS : v ∈ S <;> by_cases hwS : w ∈ S <;>
      by_cases hvT : v ∈ T <;> by_cases hwT : w ∈ T <;>
      simp [hvS, hwS, hvT, hwT]

theorem boundary_delete_loss [Fintype V] (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (S : Finset V) :
    boundaryCount G S ≤ F.card + boundaryCount (G.deleteEdges F) S := by
  have hp : ∀ e : Sym2 V,
      cutIndicator G S Sᶜ e ≤ (if e ∈ F then 1 else 0) +
        cutIndicator (G.deleteEdges F) S Sᶜ e := by
    intro e
    by_cases he : e ∈ F
    · simp only [cutIndicator, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
        Finset.mem_coe, he, not_true_eq_false, and_false, ite_true]
      split_ifs <;> omega
    · simp [cutIndicator, SimpleGraph.edgeSet_deleteEdges, he]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  simpa [Finset.sum_add_distrib, boundaryCount, cutCount] using hs

theorem three_cut_delete_bound [Fintype V] (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (S T : Finset V) (hST : Disjoint S T) :
    boundaryCount G S + boundaryCount G T + boundaryCount G (S ∪ T)ᶜ ≤
      2*F.card + 2*(boundaryCount (G.deleteEdges F) S +
        cutCount (G.deleteEdges F) T (S ∪ T)ᶜ) := by
  have hp : ∀ e : Sym2 V,
      cutIndicator G S Sᶜ e + cutIndicator G T Tᶜ e +
        cutIndicator G (S ∪ T)ᶜ ((S ∪ T)ᶜ)ᶜ e ≤
      2*(if e ∈ F then 1 else 0) +
        2*(cutIndicator (G.deleteEdges F) S Sᶜ e +
          cutIndicator (G.deleteEdges F) T (S ∪ T)ᶜ e) := by
    intro e
    induction e using Sym2.ind with
    | _ v w =>
      have hv : v ∈ S → v ∉ T := fun hv => Finset.disjoint_left.mp hST hv
      have hw : w ∈ S → w ∉ T := fun hw => Finset.disjoint_left.mp hST hw
      simp only [cutIndicator, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
        Finset.mem_coe, crosses_pair, mem_union, mem_compl, compl_compl]
      by_cases hvS : v ∈ S <;> by_cases hwS : w ∈ S <;>
        by_cases hvT : v ∈ T <;> by_cases hwT : w ∈ T <;>
        by_cases hG : s(v,w) ∈ G.edgeSet <;> by_cases hF : s(v,w) ∈ F <;>
        simp_all
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole] at hs
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter, boundaryCount, cutCount, Nat.cast_id,
    mul_comm F.card 2] using hs

theorem cutCount_mono_right [Fintype V] (G : SimpleGraph V) (S : Finset V)
    {T U : Finset V} (hTU : T ⊆ U) : cutCount G S T ≤ cutCount G S U := by
  rw [cutCount_eq_filter_card, cutCount_eq_filter_card]
  apply Finset.card_le_card
  intro e he
  obtain ⟨heG, v, hv, w, hw, heq⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heG, v, hv, w, hTU hw, heq⟩

theorem cutCount_union_right_le [Fintype V] (G : SimpleGraph V) (S T U : Finset V) :
    cutCount G S (T ∪ U) ≤ cutCount G S T + cutCount G S U := by
  simp only [cutCount_eq_filter_card]
  have hset : G.edgeFinset.filter (Crosses S (T ∪ U)) =
      G.edgeFinset.filter (Crosses S T) ∪ G.edgeFinset.filter (Crosses S U) := by
    ext e
    simp only [mem_filter, mem_union, Crosses]
    aesop
  rw [hset]
  exact Finset.card_union_le _ _

theorem cutCount_le_product [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    cutCount G S T ≤ S.card*T.card := by
  rw [cutCount_eq_filter_card]
  have hsub : G.edgeFinset.filter (Crosses S T) ⊆
      (S ×ˢ T).image (fun p : V × V => s(p.1,p.2)) := by
    intro e he
    obtain ⟨_, v, hv, w, hw, heq⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨(v,w), mem_product.mpr ⟨hv,hw⟩, heq.symm⟩
  calc
    _ ≤ ((S ×ˢ T).image (fun p : V × V => s(p.1,p.2))).card := card_le_card hsub
    _ ≤ (S ×ˢ T).card := card_image_le
    _ = S.card*T.card := card_product S T

theorem cutCount_delete_vertices [Fintype V] (G : SimpleGraph V) (U W T : Finset V) :
    cutCount G T (U \ T) ≤ cutCount G T (W \ T) + T.card*(U \ W).card := by
  have hsub : U \ T ⊆ (W \ T) ∪ (U \ W) := by
    intro v hv
    simp only [mem_sdiff, mem_union] at *
    tauto
  calc
    _ ≤ cutCount G T ((W \ T) ∪ (U \ W)) := cutCount_mono_right G T hsub
    _ ≤ cutCount G T (W \ T) + cutCount G T (U \ W) := cutCount_union_right_le G T _ _
    _ ≤ cutCount G T (W \ T) + T.card*(U \ W).card :=
      Nat.add_le_add_left (cutCount_le_product G T _) _

theorem cutCount_comm [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    cutCount G S T = cutCount G T S := by
  unfold cutCount
  apply Finset.sum_congr rfl
  intro e _
  have hc : Crosses S T e ↔ Crosses T S e := by
    induction e using Sym2.ind with
    | _ v w => simp only [crosses_pair]; tauto
  simp [cutIndicator, hc]

theorem cutCount_zero_of_no_edges [Fintype V] {G : SimpleGraph V} {S T : Finset V}
    (hno : ∀ v ∈ S, ∀ w ∈ T, ¬G.Adj v w) : cutCount G S T = 0 := by
  rw [cutCount_eq_filter_card, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heG, v, hv, w, hw, rfl⟩ := Finset.mem_filter.mp he
  exact hno v hv w hw (SimpleGraph.mem_edgeFinset.mp heG)

end Cycle12
