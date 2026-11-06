import Cycle12.Foundations.KargerCuts
import Cycle12.Foundations.GraphBranchCut

/-! The contraction cut-count bound for the project's actual SimpleGraph
cut function, including the half-integer levels used in the edge split. -/
namespace Cycle13
open SimpleGraph Finset ARA ARA.MultiGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def simpleAsMulti : MultiGraph V where
  verts := univ
  edges := G.edgeFinset.toList

theorem simpleAsMulti_wf : (simpleAsMulti G).WF where
  incidence _ _ _ _ := mem_univ _
  loopless e he := G.not_isDiag_of_mem_edgeSet (by simpa [simpleAsMulti] using he)

theorem simpleAsMulti_cutValue (S : Finset V) :
    (simpleAsMulti G).cutValue S=cutSize G S := by
  have hf : G.edgeFinset.filter (Crossing S)=(cutGraph G S).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_filter,G.mem_edgeFinset,(cutGraph G S).mem_edgeFinset,crossing_mk]
      change (G.Adj x y ∧ ¬(x ∈ S ↔ y ∈ S)) ↔
        (G.Adj x y ∧ (x ∈ S ∧ y ∉ S ∨ x ∉ S ∧ y ∈ S))
      tauto
  change (G.edgeFinset.toList.countP (fun e => decide (Crossing S e))) = _
  rw [← G.edgeFinset.nodup_toList.card_eq_countP (P:=Crossing S),
    Finset.toList_toFinset,hf]
  simp only [cutSize,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']

theorem simpleAsMulti_minCut_lower {l : ℕ} (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ S : Finset V, S.Nonempty → S ≠ univ → l ≤ cutSize G S) :
    l ≤ (simpleAsMulti G).minCutValue := by
  obtain ⟨S,hS,heq⟩ := exists_minCut (simpleAsMulti G) (by simpa [simpleAsMulti] using hn)
  rw [← heq,simpleAsMulti_cutValue]
  apply hcut S hS.nonempty
  rintro rfl
  obtain ⟨v,_,hv⟩ := hS.proper
  exact hv (mem_univ _)

theorem simple_small_cut_count {d K l : ℕ} (hd : 2 ≤ d) (hl : 0 < l)
    (hK : 2*K ≤ d*l) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ S : Finset V, S.Nonempty → S ≠ univ → l ≤ cutSize G S) :
    (univ.filter (fun S : Finset V => cutSize G S ≤ K)).card ≤
      2*(Fintype.card V)^d := by
  have h := smallCuts_polynomial_bound (simpleAsMulti G) (simpleAsMulti_wf G)
    hd hl hK (simpleAsMulti_minCut_lower G hn hcut) (by simpa [simpleAsMulti] using hn)
  simp only [smallCuts,simpleAsMulti_cutValue] at h
  simpa only [simpleAsMulti,Finset.powerset_univ,Finset.card_univ] using h

def cutBucket (l j : ℕ) : Finset (Finset V) :=
  univ.filter (fun S => (j+2)*l ≤ 2*cutSize G S ∧ 2*cutSize G S < (j+3)*l)

theorem cutBucket_card {l : ℕ} (hl : 0 < l) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ S : Finset V, S.Nonempty → S ≠ univ → l ≤ cutSize G S) (j : ℕ) :
    (cutBucket G l j).card ≤ 2*(Fintype.card V)^(j+3) := by
  have hs : cutBucket G l j ⊆ univ.filter (fun S : Finset V => cutSize G S ≤ ((j+3)*l)/2) := by
    intro S hS
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have hh := (mem_filter.mp hS).2.2
    omega
  apply (card_le_card hs).trans
  apply simple_small_cut_count G (by omega) hl _ hn hcut
  omega

theorem mem_some_cutBucket {l : ℕ} (hl : 0 < l) (S : Finset V)
    (hS : l ≤ cutSize G S) : ∃ j, S ∈ cutBucket G l j := by
  have hq : 2 ≤ (2*cutSize G S)/l := (Nat.le_div_iff_mul_le hl).mpr (by omega)
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hq
  have hlo := Nat.div_mul_le_self (2*cutSize G S) l
  have hhi := Nat.mod_lt (2*cutSize G S) hl
  have heq := Nat.mod_add_div (2*cutSize G S) l
  refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_,?_⟩⟩
  · rw [hj,add_comm] at hlo
    exact hlo
  · rw [hj] at heq
    nlinarith

end
end Cycle13
