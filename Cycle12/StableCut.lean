import Cycle12.CutFlipGeometry

namespace Cycle12
open SimpleGraph Finset Cycle13
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def cutObjective (G : SimpleGraph V) (U : Finset V) (c : ℝ) (A : Finset V) : ℝ :=
  (G.interedges A (U\A)).card-c*min (A.card:ℝ) (U\A).card

def IsStableCut (G : SimpleGraph V) (U A : Finset V) (c : ℝ) : Prop :=
  A⊆U ∧ ∀ B⊆U, cutObjective G U c A ≤ cutObjective G U c B

theorem cut_objective_complement (G : SimpleGraph V) (U A : Finset V)
    (hA : A⊆U) (c : ℝ) :
    cutObjective G U c (U\A)=cutObjective G U c A := by
  unfold cutObjective
  rw [relative_complement_involutive U A hA,interedges_card_comm G (U\A) A,
    min_comm]

theorem stable_cut_complement (G : SimpleGraph V) (U A : Finset V) {c : ℝ}
    (hstable : IsStableCut G U A c) : IsStableCut G U (U\A) c := by
  refine ⟨sdiff_subset,?_⟩
  intro B hB
  rw [cut_objective_complement G U A hstable.1]
  exact hstable.2 B hB

theorem exists_stable_cut (G : SimpleGraph V) (U : Finset V) (c : ℝ) :
    ∃ A, IsStableCut G U A c := by
  obtain ⟨A,hA,hmin⟩ := U.powerset.exists_min_image (cutObjective G U c)
    (show U.powerset.Nonempty from ⟨∅,mem_powerset.mpr (empty_subset _)⟩)
  exact ⟨A,mem_powerset.mp hA,fun B hB => hmin B (mem_powerset.mpr hB)⟩

/-- Minimality against every single-vertex move controls actual crossing degrees. -/
theorem stable_cut_outside_degree (G : SimpleGraph V) (U A : Finset V)
    {c : ℝ} (hc : 0 ≤ c) (hstable : IsStableCut G U A c)
    {v : V} (hvU : v∈U) (hvA : v∉A) :
    2*((neighborsIn G v A).card:ℝ) ≤ (neighborsIn G v U).card+c := by
  have hmove := hstable.2 (insert v A) (insert_subset hvU hstable.1)
  have he : ((G.interedges (insert v A) (U\insert v A)).card:ℝ)+
      (neighborsIn G v A).card = (G.interedges A (U\A)).card+
        (neighborsIn G v (U\A)).card := by
    exact_mod_cast cut_insert_identity G U A hvU hvA
  have hm : min (A.card:ℝ) (U\A).card ≤
      min ((insert v A).card:ℝ) (U\insert v A).card+1 := by
    exact_mod_cast cut_insert_min_card_lower U A hvU hvA
  have hscale := mul_le_mul_of_nonneg_left hm hc
  have hd : ((neighborsIn G v U).card:ℝ)=(neighborsIn G v A).card+
      (neighborsIn G v (U\A)).card := by
    exact_mod_cast neighborsIn_partition_card G v A U hstable.1
  unfold cutObjective at hmove
  nlinarith only [hmove,he,hscale,hd]

theorem stable_cut_cross_degree (G : SimpleGraph V) (U A : Finset V)
    {c : ℝ} (hc : 0 ≤ c) (hstable : IsStableCut G U A c)
    {v : V} (hvU : v∈U) :
    2*((neighborsIn G v (if v∈A then U\A else A)).card:ℝ) ≤
      (neighborsIn G v U).card+c := by
  by_cases hvA : v∈A
  · rw [if_pos hvA]
    exact stable_cut_outside_degree G U (U\A) hc
      (stable_cut_complement G U A hstable) hvU (by simp [hvA])
  · rw [if_neg hvA]
    exact stable_cut_outside_degree G U A hc hstable hvU hvA

/-- From any expansion failure choose a stable bad cut and orient its smaller side.
The minimization includes the empty and full sides, so negativity proves nonemptiness. -/
theorem exists_stable_bad_cut (G : SimpleGraph V) (U S : Finset V)
    (hS : S⊆U) {c : ℝ}
    (hbad : ((G.interedges S (U\S)).card:ℝ)<c*min (S.card:ℝ) (U\S).card) :
    ∃ A, IsStableCut G U A c ∧ A.Nonempty ∧ (U\A).Nonempty ∧
      2*A.card ≤ U.card ∧ ((G.interedges A (U\A)).card:ℝ)<c*A.card := by
  obtain ⟨A,hstable⟩ := exists_stable_cut G U c
  have hneg : cutObjective G U c A<0 := by
    have hh := hstable.2 S hS
    unfold cutObjective at hh ⊢
    linarith only [hh,hbad]
  have orient : ∀ B, IsStableCut G U B c → cutObjective G U c B<0 →
      B.card ≤ (U\B).card → B.Nonempty ∧ (U\B).Nonempty ∧
        2*B.card ≤ U.card ∧ ((G.interedges B (U\B)).card:ℝ)<c*B.card := by
    intro B hB hnegB hsmall
    have hsmallR : (B.card:ℝ) ≤ (U\B).card := by exact_mod_cast hsmall
    have hbadB : ((G.interedges B (U\B)).card:ℝ)<c*B.card := by
      simpa only [cutObjective,min_eq_left hsmallR,sub_neg] using hnegB
    have hnonempty : B.Nonempty := by
      by_contra hn
      have hz : B.card=0 := by simp [not_nonempty_iff_eq_empty.mp hn]
      rw [hz,Nat.cast_zero,mul_zero] at hbadB
      exact (not_lt_of_ge (Nat.cast_nonneg _)) hbadB
    have hcomp : (U\B).Nonempty := card_pos.mp ((card_pos.mpr hnonempty).trans_le hsmall)
    refine ⟨hnonempty,hcomp,?_,hbadB⟩
    have hh := card_sdiff_of_subset hB.1
    have hle := card_le_card hB.1
    omega
  by_cases hsmall : A.card ≤ (U\A).card
  · exact ⟨A,hstable,orient A hstable hneg hsmall⟩
  · have hc := stable_cut_complement G U A hstable
    have hn : cutObjective G U c (U\A)<0 := by
      rw [cut_objective_complement G U A hstable.1]
      exact hneg
    have hh : (U\A).card ≤ (U\(U\A)).card := by
      rw [relative_complement_involutive U A hstable.1]
      omega
    exact ⟨U\A,hc,orient (U\A) hc hn hh⟩

end
end Cycle12
