import Cycle12.JointCutError

namespace Cycle12
open SimpleGraph Finset Cycle13
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem interedges_card_comm (G : SimpleGraph V) (A B : Finset V) :
    (G.interedges A B).card = (G.interedges B A).card := by
  letI : Std.Symm G.Adj := ⟨fun _ _ h => G.adj_symm h⟩
  exact Rel.card_interedges_comm (r:=G.Adj) A B

theorem interedges_card_insert_left (G : SimpleGraph V) (A B : Finset V)
    {v : V} (hv : v∉A) :
    (G.interedges (insert v A) B).card =
      (neighborsIn G v B).card+(G.interedges A B).card := by
  simp only [card_interedges_eq_sum_neighborsIn, sum_insert hv]

theorem interedges_card_insert_right (G : SimpleGraph V) (A B : Finset V)
    {v : V} (hv : v∉B) :
    (G.interedges A (insert v B)).card =
      (neighborsIn G v A).card+(G.interedges A B).card := by
  rw [interedges_card_comm G A,interedges_card_insert_left G B A hv,
    interedges_card_comm G B A]

theorem relative_complement_involutive (U A : Finset V) (hA : A⊆U) :
    U\(U\A)=A := by
  ext v
  simp only [mem_sdiff]
  constructor
  · intro h
    by_contra hv
    exact h.2 ⟨h.1,hv⟩
  · intro hv
    exact ⟨hA hv,fun h => h.2 hv⟩

/-- Exact edge accounting for moving an outside vertex into one side. -/
theorem cut_insert_identity (G : SimpleGraph V) (U A : Finset V)
    {v : V} (hvU : v∈U) (hvA : v∉A) :
    (G.interedges (insert v A) (U\insert v A)).card+(neighborsIn G v A).card =
      (G.interedges A (U\A)).card+(neighborsIn G v (U\A)).card := by
  let C := U\insert v A
  have hvC : v∉C := by simp [C]
  have hC : insert v C=U\A := by
    ext w
    simp only [C,mem_insert,mem_sdiff]
    constructor
    · rintro (rfl | h)
      · exact ⟨hvU,hvA⟩
      · exact ⟨h.1,fun hw => h.2 (Or.inr hw)⟩
    · intro h
      by_cases hw : w=v
      · exact Or.inl hw
      · exact Or.inr ⟨h.1,fun hh => hh.elim hw h.2⟩
  have hn : neighborsIn G v C=neighborsIn G v (U\A) := by
    rw [← hC]
    ext w
    simp only [neighborsIn,mem_filter,mem_insert]
    constructor
    · intro h
      exact ⟨Or.inr h.1,h.2⟩
    · rintro ⟨rfl | hw,hadj⟩
      · exact (G.irrefl hadj).elim
      · exact ⟨hw,hadj⟩
  change (G.interedges (insert v A) C).card+_=_
  rw [interedges_card_insert_left G A C hvA,← hC,
    interedges_card_insert_right G A C hvC]
  rw [← hC] at hn
  rw [← hn]
  omega

/-- Moving one vertex changes the smaller-side cardinality by at most one. -/
theorem cut_insert_min_card_lower (U A : Finset V) {v : V}
    (hvU : v∈U) (hvA : v∉A) :
    min A.card (U\A).card ≤ min (insert v A).card (U\insert v A).card+1 := by
  have hC : U\insert v A=(U\A).erase v := by
    ext w
    simp only [mem_sdiff,mem_insert,mem_erase]
    tauto
  have hv : v∈U\A := mem_sdiff.mpr ⟨hvU,hvA⟩
  rw [card_insert_of_notMem hvA,hC,card_erase_of_mem hv]
  have hp := card_pos.mpr (show (U\A).Nonempty from ⟨v,hv⟩)
  omega

end
end Cycle12
