import Cycle12.Foundations.KargerCuts
import Cycle12.Foundations.FractionalCutArithmetic

namespace Cycle13
open Finset ARA ARA.MultiGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [DecidableEq V]

def properSmallCuts (g : MultiGraph V) (K : ℕ) : Finset (Finset V) :=
  (smallCuts g K).filter (fun S => S.Nonempty ∧ S≠g.verts)

theorem mem_properSmallCuts (g : MultiGraph V) (K : ℕ) (S : Finset V) :
    S∈properSmallCuts g K ↔ S⊆g.verts ∧ g.cutValue S ≤ K ∧ S.Nonempty ∧ S≠g.verts := by
  simp only [properSmallCuts,mem_filter,mem_smallCuts]
  tauto

theorem properSmallCuts_total (g : MultiGraph V) (K : ℕ) :
    (properSmallCuts g K).card ≤ 2^g.verts.card-2 := by
  by_cases hg : g.verts.Nonempty
  · have hs : properSmallCuts g K⊆g.verts.powerset\{∅,g.verts} := by
      intro S hS
      obtain ⟨hsub,_,hne,hproper⟩ := (mem_properSmallCuts g K S).mp hS
      apply mem_sdiff.mpr
      exact ⟨mem_powerset.mpr hsub,by simpa only [mem_insert,mem_singleton] using
        (not_or.mpr ⟨hne.ne_empty,hproper⟩)⟩
    have hsub : {∅,g.verts}⊆g.verts.powerset := by
      intro S hS
      rcases mem_insert.mp hS with rfl | hS
      · exact mem_powerset.mpr (empty_subset _)
      · have he : S=g.verts := mem_singleton.mp hS
        exact mem_powerset.mpr (he ▸ Subset.rfl)
    have hcard : ({∅,g.verts}:Finset (Finset V)).card=2 := by simp [hg.ne_empty.symm]
    have hh := card_le_card hs
    simpa only [card_sdiff_of_subset hsub,card_powerset,hcard] using hh
  · have hz : g.verts=∅ := not_nonempty_iff_eq_empty.mp hg
    have he : properSmallCuts g K=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hh := (mem_properSmallCuts g K S).mp hS
      have hS0 : S=∅ := subset_empty.mp (hz ▸ hh.1)
      exact hh.2.2.1.ne_empty hS0
    simp [he,hz]

theorem surviving_properSmallCuts_bound (g : MultiGraph V) (hwf : g.WF) (K : ℕ)
    (e : Sym2 V) (w : V) (hw : w∈e) :
    ((properSmallCuts g K).filter (fun S => ¬Crossing S e)).card ≤
      (properSmallCuts (g.contractEdgeTo e w) K).card := by
  apply card_le_card_of_injOn (fun S => S.image (redirectTo e w))
  · intro S hS
    obtain ⟨hS,hnc⟩ := mem_filter.mp hS
    obtain ⟨hsub,hval,hne,hproper⟩ := (mem_properSmallCuts g K S).mp hS
    apply (mem_properSmallCuts _ _ _).mpr
    refine ⟨?_,?_,hne.image _,?_⟩
    · rintro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      by_cases hye : y∈e
      · simp [redirectTo,hye]
      · simp [redirectTo,hye,hsub hy]
    · rw [cutValue_contractEdgeTo_of_pointwise hwf
        (fun x _ => contract_image_membership hw hnc x)]
      exact hval
    · intro heq
      change S.image (redirectTo e w)=(g.contractEdgeTo e w).verts at heq
      apply hproper
      apply Subset.antisymm hsub
      intro x hx
      apply (contract_image_membership hw hnc x).mp
      rw [heq]
      by_cases hxe : x∈e
      · simp [redirectTo,hxe]
      · simp [redirectTo,hxe,hx]
  · intro S hS T hT heq
    change S.image (redirectTo e w)=T.image (redirectTo e w) at heq
    ext x
    rw [← contract_image_membership hw (mem_filter.mp hS).2 x,
      ← contract_image_membership hw (mem_filter.mp hT).2 x,heq]

theorem properSmallCuts_contraction_step (g : MultiGraph V) (hwf : g.WF)
    {K l : ℕ} {a B : ℝ} (ha : 0 ≤ a) (hl : 0 < l)
    (hK : 2*(K:ℝ) ≤ a*l) (hmin : l ≤ g.minCutValue) (hn : 2 ≤ g.verts.card)
    (hB : ∀ e∈g.edges, ((properSmallCuts (g.contractEdgeTo e e.out.1) K).card:ℝ) ≤ B) :
    ((g.verts.card:ℝ)-a)*(properSmallCuts g K).card ≤ g.verts.card*B := by
  have hhand : g.verts.card*l ≤ 2*g.edges.length :=
    (Nat.mul_le_mul_left _ hmin).trans (card_mul_minCutValue_le g hwf hn)
  have hsurv : (∑ i : Fin g.edges.length,
      (((properSmallCuts g K).filter (fun S => ¬Crossing S g.edges[i.val])).card:ℝ)) ≤
      g.edges.length*B := by
    calc
      _ ≤ ∑ _i : Fin g.edges.length, B := by
        apply sum_le_sum
        intro i _
        exact (Nat.cast_le.mpr (surviving_properSmallCuts_bound g hwf K _ _ (Sym2.out_fst_mem _))).trans
          (hB _ (List.getElem_mem _))
      _ = _ := by simp
  have hcross : (∑ S∈properSmallCuts g K, (g.cutValue S:ℝ)) ≤ (K:ℝ)*(properSmallCuts g K).card := by
    calc
      _ ≤ ∑ _S∈properSmallCuts g K, (K:ℝ) := sum_le_sum (fun S hS =>
        Nat.cast_le.mpr ((mem_properSmallCuts g K S).mp hS).2.1)
      _ = _ := by simp [mul_comm]
  have hid := congrArg (fun z : ℕ => (z:ℝ)) (survival_count_identity g (properSmallCuts g K))
  simp only [Nat.cast_add,Nat.cast_sum,Nat.cast_mul] at hid
  exact real_contraction_arithmetic (m:=(g.edges.length:ℝ))
    (by exact_mod_cast hl) ha (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hK (by exact_mod_cast hhand) (by linarith)

end
end Cycle13
