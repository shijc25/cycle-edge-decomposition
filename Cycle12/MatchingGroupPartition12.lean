import Cycle12.BoundedDemandGroups12
import Cycle12.Foundations.StarPairing

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [DecidableEq I]

def matchingPairVertices (M : (⊤ : SimpleGraph I).Subgraph) (e : M.edgeSet) : Finset I :=
  {e.val.out.1,e.val.out.2}

theorem matchingPairVertices_card (M : (⊤ : SimpleGraph I).Subgraph) (e : M.edgeSet) :
    (matchingPairVertices M e).card=2 := by
  have ha := edge_out_adj M.spanningCoe e
  have hn : e.val.out.1 ≠ e.val.out.2 := M.adj_sub ha
  simp [matchingPairVertices,hn]

theorem matchingPairVertices_disjoint (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching) :
    Pairwise (fun e f : M.edgeSet => Disjoint (matchingPairVertices M e) (matchingPairVertices M f)) := by
  intro e f hef
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have he := edge_out_adj M.spanningCoe e
  have hf := edge_out_adj M.spanningCoe f
  simp only [matchingPairVertices,mem_insert,mem_singleton] at hv hw
  apply hef
  apply Subtype.ext
  rw [←e.val.out_eq,←f.val.out_eq]
  change s(e.val.out.1,e.val.out.2)=s(f.val.out.1,f.val.out.2)
  rcases hv with hv|hv <;> rcases hw with hw|hw
  · have hx := hv.symm.trans hw
    have he' := hx ▸ he
    rw [hx,hM.eq_of_adj_left he' hf]
  · have hx := hv.symm.trans hw
    have he' := hx ▸ he
    rw [hx,hM.eq_of_adj_left he' hf.symm]
    exact Sym2.eq_swap
  · have hx := hv.symm.trans hw
    have he' := hx ▸ he.symm
    rw [hx,hM.eq_of_adj_left he' hf]
    exact Sym2.eq_swap
  · have hx := hv.symm.trans hw
    have he' := hx ▸ he.symm
    rw [hx,hM.eq_of_adj_left he' hf.symm]

theorem matchingPairVertices_union (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching) :
    univ.biUnion (matchingPairVertices M)=M.verts.toFinset := by
  ext v
  simp only [mem_biUnion,mem_univ,true_and,Set.mem_toFinset,matchingPairVertices,mem_insert,mem_singleton]
  constructor
  · rintro ⟨e,rfl|rfl⟩
    · exact (edge_out_adj M.spanningCoe e).fst_mem
    · exact (edge_out_adj M.spanningCoe e).snd_mem
  · intro hv
    obtain ⟨w,hw,_⟩ := hM hv
    let e : M.edgeSet := ⟨s(v,w),hw⟩
    refine ⟨e,?_⟩
    have hh : v∈s(e.val.out.1,e.val.out.2) := by
      rw [show s(e.val.out.1,e.val.out.2)=e.val from e.val.out_eq]
      simp [e]
    exact Sym2.mem_iff.mp hh

def matchingEvenGroup (M : (⊤ : SimpleGraph I).Subgraph) (Q : ℕ)
    (b : Fin (Fintype.card M.edgeSet/Q+1)) : Finset I :=
  univ.biUnion (fun e : {e : M.edgeSet // demandGroup Q e=b} => matchingPairVertices M e.val)

theorem matchingEvenGroup_card (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (Q : ℕ) (b : Fin (Fintype.card M.edgeSet/Q+1)) :
    (matchingEvenGroup M Q b).card=2*Fintype.card {e : M.edgeSet // demandGroup Q e=b} := by
  rw [matchingEvenGroup,Finset.card_biUnion (fun e _ f _ hef =>
    matchingPairVertices_disjoint M hM (Subtype.val_injective.ne hef))]
  simp only [matchingPairVertices_card,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_comm]

theorem matchingEvenGroup_bounded (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    {Q : ℕ} (hQ : 0<Q) (b : Fin (Fintype.card M.edgeSet/Q+1)) :
    Even (matchingEvenGroup M Q b).card ∧ (matchingEvenGroup M Q b).card ≤ 2*Q := by
  rw [matchingEvenGroup_card M hM]
  exact ⟨even_two_mul _,Nat.mul_le_mul_left 2 (demandGroup_fiber_card hQ b)⟩

theorem matchingEvenGroup_disjoint (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (Q : ℕ) : Pairwise (fun a b => Disjoint (matchingEvenGroup M Q a) (matchingEvenGroup M Q b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨e,_,he⟩ := mem_biUnion.mp hv
  obtain ⟨f,_,hf⟩ := mem_biUnion.mp hw
  have hef : e.val ≠ f.val := by
    intro h
    exact hab (e.property.symm.trans ((congrArg (demandGroup Q) h).trans f.property))
  exact Finset.disjoint_left.mp (matchingPairVertices_disjoint M hM hef) he hf

theorem matchingEvenGroup_union (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (Q : ℕ) : univ.biUnion (matchingEvenGroup M Q)=M.verts.toFinset := by
  rw [←matchingPairVertices_union M hM]
  ext v
  simp only [mem_biUnion,mem_univ,true_and,matchingEvenGroup]
  constructor
  · rintro ⟨b,e,he⟩
    exact ⟨e.val,he⟩
  · rintro ⟨e,he⟩
    exact ⟨demandGroup Q e,⟨e,rfl⟩,he⟩

/-- Pair the finite index set, retain at most one item, and partition
every other item into even groups of size at most 2Q. The group charge
is at most |I|/(2Q)+1, with no extra charge per paired item. -/
theorem finite_even_group_partition {Q : ℕ} (hQ : 0<Q) :
    ∃ M : (⊤ : SimpleGraph I).Subgraph, M.IsMatching ∧
      M.vertsᶜ.ncard ≤ 1 ∧
      (univ.biUnion (matchingEvenGroup M Q))∪M.vertsᶜ.toFinset=univ ∧
      (∀ b,Disjoint (matchingEvenGroup M Q b) M.vertsᶜ.toFinset) ∧
      Pairwise (fun a b => Disjoint (matchingEvenGroup M Q a) (matchingEvenGroup M Q b)) ∧
      (∀ b,Even (matchingEvenGroup M Q b).card ∧ (matchingEvenGroup M Q b).card ≤ 2*Q) ∧
      (Fintype.card (Fin (Fintype.card M.edgeSet/Q+1)):ℝ) ≤ (Fintype.card I:ℝ)/(2*Q)+1 := by
  obtain ⟨M,hM,hrem,hcard⟩ := complete_matching_leaves_at_most_one (I:=I)
  refine ⟨M,hM,hrem,?_,?_,matchingEvenGroup_disjoint M hM Q,
    matchingEvenGroup_bounded M hM hQ,?_⟩
  · rw [matchingEvenGroup_union M hM]
    ext v
    simp
  · intro b
    apply Finset.disjoint_left.mpr
    intro v hv hn
    apply (Set.mem_toFinset.mp hn)
    apply Set.mem_toFinset.mp
    rw [←matchingEvenGroup_union M hM Q]
    exact mem_biUnion.mpr ⟨b,mem_univ _,hv⟩
  · have hE : 2*Fintype.card M.edgeSet ≤ Fintype.card I := by
      rw [Set.fintypeCard_eq_ncard]
      omega
    have hER : 2*(Fintype.card M.edgeSet:ℝ) ≤ Fintype.card I := by exact_mod_cast hE
    have hQR : (0:ℝ)<Q := by exact_mod_cast hQ
    have hd : (Fintype.card M.edgeSet:ℝ)/Q ≤ (Fintype.card I:ℝ)/(2*Q) := by
      apply (div_le_div_iff₀ hQR (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hER hQR.le]
    exact (demandGroup_count_bound (I:=M.edgeSet) hQ).trans (add_le_add hd (le_refl 1))

end
end Cycle12
