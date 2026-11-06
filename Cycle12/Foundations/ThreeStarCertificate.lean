import Cycle12.Foundations.IndexedFactorization
import Cycle12.Foundations.PartitionListColoring

/-! The finite core of three prescribed lifting colors. Each of three
stars has two possible orders of its other colors. An inter-star conflict
excludes exactly two of the eight choices; at most three conflicts leave
a valid choice. All finite checks use kernel reduction. -/
namespace Cycle13
open SimpleGraph Finset

def threeStarColor (r : Fin 3) (slot flip : Bool) : Fin 3 :=
  r+(if slot=flip then 1 else 2)

theorem threeStarColor_ne : ∀ (r : Fin 3) (slot flip : Bool),
    threeStarColor r slot flip≠r := by decide

theorem threeStarColor_injective : ∀ (r : Fin 3) (flip : Bool),
    Function.Injective (fun slot => threeStarColor r slot flip) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem threeStar_bad_count : ∀ (r s : Fin 3) (u v : Bool), r≠s →
    ((univ : Finset (Fin 3 → Bool)).filter (fun θ =>
      threeStarColor r u (θ r)=threeStarColor s v (θ s))).card=2 := by decide

noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [DecidableEq I]

theorem exists_three_star_coloring (K : SimpleGraph I) (group : I → Fin 3) (slot : I → Bool)
    (hedges : K.edgeFinset.card ≤ 3) (hgroup : ∀ i j, K.Adj i j → group i≠group j) :
    ∃ c : I → Fin 3,
      (∀ i, c i≠group i) ∧
      (∀ i j, group i=group j → slot i≠slot j → c i≠c j) ∧
      (∀ i j, K.Adj i j → c i≠c j) := by
  let bad : K.edgeSet → Finset (Fin 3 → Bool) := fun e => univ.filter (fun θ =>
    threeStarColor (group e.val.out.1) (slot e.val.out.1) (θ (group e.val.out.1))=
      threeStarColor (group e.val.out.2) (slot e.val.out.2) (θ (group e.val.out.2)))
  have hbad : ∀ e, (bad e).card=2 := by
    intro e
    exact threeStar_bad_count _ _ _ _ (hgroup _ _ (edge_out_adj K e))
  let B := univ.biUnion bad
  have hB : B.card ≤ 6 := by
    have hh := card_biUnion_le (s:=(univ : Finset K.edgeSet)) (t:=bad)
    simp only [hbad,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,
      ← K.edgeFinset_card] at hh
    change B.card ≤ K.edgeFinset.card*2 at hh
    omega
  have htotal : (univ : Finset (Fin 3 → Bool)).card=8 := by decide
  obtain ⟨θ,hθ,hθB⟩ := exists_mem_notMem_of_card_lt_card (show B.card < (univ : Finset (Fin 3 → Bool)).card by omega)
  let c : I → Fin 3 := fun i => threeStarColor (group i) (slot i) (θ (group i))
  refine ⟨c,fun i => threeStarColor_ne _ _ _,?_,?_⟩
  · intro i j hg hs hc
    apply hs
    apply threeStarColor_injective (group j) (θ (group j))
    simpa only [c,hg] using hc
  · intro i j hij hc
    apply hθB
    let e : K.edgeSet := ⟨s(i,j),hij⟩
    refine mem_biUnion.mpr ⟨e,mem_univ _,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    have hout : s(e.val.out.1,e.val.out.2)=s(i,j) := e.val.out_eq
    rcases Sym2.eq_iff.mp hout with h | h
    · simpa only [h.1,h.2] using hc
    · simpa only [h.1,h.2] using hc.symm

end
end Cycle13
