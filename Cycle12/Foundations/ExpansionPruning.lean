import Cycle12.Foundations.CutPartition
import OAI.Combinatorics.CycleDecomposition.Routing

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Cut expansion on an actual retained vertex set. -/
def ExpansionWithin (G : SimpleGraph V) (S : Finset V) (h : ℝ) : Prop :=
  ∀ U : Finset V, U ⊆ S → 2*U.card ≤ S.card →
    h*U.card ≤ (G.interedges U (S\U)).card

theorem cutSize_deleteEdges_loss (G : SimpleGraph V) (F : Finset (Sym2 V)) (S : Finset V) :
    cutSize G S ≤ cutSize (G.deleteEdges F) S+F.card := by
  letI : DecidableRel (G.deleteEdges (F : Set (Sym2 V))).Adj := fun _ _ => Classical.propDecidable _
  have hc : G.interedges S Sᶜ ⊆
      (G.deleteEdges F).interedges S Sᶜ ∪
        (G.interedges S Sᶜ).filter (fun e => s(e.1,e.2) ∈ F) := by
    intro e he
    by_cases hf : s(e.1,e.2) ∈ F
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,hf⟩)
    · apply Finset.mem_union_left
      obtain ⟨hx,hy,hxy⟩ := G.mem_interedges_iff.mp he
      exact (G.deleteEdges F).mem_interedges_iff.mpr ⟨hx,hy,by simpa using And.intro hxy hf⟩
  have hh := (Finset.card_le_card hc).trans (Finset.card_union_le _ _)
  have hf := OAI.ErdosGallai.deleted_boundary_card_le G S F
  simpa only [cutSize_eq_interedges] using hh.trans (Nat.add_le_add_left hf _)

theorem cutSize_union_step (G : SimpleGraph V) {R U : Finset V} (hU : U ⊆ Rᶜ) :
    cutSize G (R∪U) ≤ cutSize G R+(G.interedges U (Rᶜ\U)).card := by
  have hd : Disjoint R U := by
    rw [Finset.disjoint_left]
    intro v hv hu
    exact (Finset.mem_compl.mp (hU hu)) hv
  have hcomp : (R∪U)ᶜ=Rᶜ\U := by ext v; simp
  rw [cutSize_eq_interedges,interedges_card_union_left G R U _ hd,cutSize_eq_interedges]
  have hm := Finset.card_le_card (G.interedges_mono (Finset.Subset.refl R)
    (show (R∪U)ᶜ ⊆ Rᶜ by intro v hv; simpa using (Finset.mem_compl.mp hv) ∘ Finset.mem_union_left U))
  rw [hcomp] at hm ⊢
  omega

theorem cutExpansion_small (G : SimpleGraph V) {h : ℝ}
    (hexp : OAI.ErdosGallai.CutExpansion G h) {S : Finset V}
    (hS : 2*S.card ≤ Fintype.card V) : h*S.card ≤ (cutSize G S:ℝ) := by
  have he : S.card+Sᶜ.card=Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ S)
  have hh : (S.card:ℝ) ≤ Sᶜ.card := by exact_mod_cast (show S.card ≤ Sᶜ.card by omega)
  simpa only [min_eq_left hh,← cutSize_eq_interedges] using hexp S

private theorem pruning_crossing_impossible {a h f n r s : ℝ}
    (ha : 0 ≤ a) (ha₁ : a < 1) (hh : 0 < h)
    (hremoved : (1-a)*h*r ≤ f) (hsize : 2*s ≤ n+r)
    (hcut : h*(n-s) ≤ a*h*s+f)
    (hbudget : f*(3-a) < (1-a)^2*h*n) : False := by
  have hs := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ (1+a)*h)
  have hmiddle : (1-a)*h*n ≤ 2*f+(1+a)*h*r := by nlinarith only [hs,hcut]
  have hm := mul_le_mul_of_nonneg_left hmiddle (sub_nonneg.mpr ha₁.le)
  have hr := mul_le_mul_of_nonneg_left hremoved (by positivity : 0 ≤ 1+a)
  nlinarith only [hm,hr,hbudget]

/-- Deleting F edges from an h-expander leaves an actual induced
a*h-expander after at most |F|/((1-a)*h) vertex deletions. The threshold
is |F| < (1-a)^2*h*n/(3-a). A largest small low-boundary set replaces
the iterative pruning algorithm, including the first-crossing argument. -/
theorem exists_pruned_expander (G : SimpleGraph V) (F : Finset (Sym2 V))
    {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (ha₁ : a < 1)
    (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hbudget : (F.card:ℝ)*(3-a) < (1-a)^2*h*Fintype.card V) :
    ∃ R : Finset V, 2*R.card ≤ Fintype.card V ∧
      (1-a)*h*R.card ≤ F.card ∧ ExpansionWithin (G.deleteEdges F) Rᶜ (a*h) := by
  let H := G.deleteEdges F
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  let candidates : Finset (Finset V) := Finset.univ.filter fun R =>
    2*R.card ≤ Fintype.card V ∧ (cutSize H R:ℝ) ≤ a*h*R.card
  have hempty : ∅ ∈ candidates := by
    simp [candidates,cutSize_eq_interedges,SimpleGraph.interedges_def]
  obtain ⟨R,hR,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨∅,hempty⟩
  have hR' := (Finset.mem_filter.mp hR).2
  have hremoved : (1-a)*h*R.card ≤ (F.card:ℝ) := by
    have hx := cutExpansion_small G hexp hR'.1
    have hl : (cutSize G R:ℝ) ≤ (cutSize H R:ℝ)+F.card := by
      exact_mod_cast cutSize_deleteEdges_loss G F R
    nlinarith only [hx,hl,hR'.2]
  refine ⟨R,hR'.1,hremoved,?_⟩
  intro U hU hsmall
  by_contra! hbad
  have hUpos : 0 < U.card := by
    by_contra! hz
    have he : U=∅ := Finset.card_eq_zero.mp (by omega)
    subst he
    simpa [SimpleGraph.interedges_def] using hbad
  have hdis : Disjoint R U := by
    rw [Finset.disjoint_left]
    intro v hv hu
    exact (Finset.mem_compl.mp (hU hu)) hv
  have hcard : (R∪U).card=R.card+U.card := Finset.card_union_of_disjoint hdis
  have hcomp : R.card+Rᶜ.card=Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ R)
  have hnew : (cutSize H (R∪U):ℝ) ≤ a*h*(R∪U).card := by
    have hl : (cutSize H (R∪U):ℝ) ≤ (cutSize H R:ℝ)+
        (H.interedges U (Rᶜ\U)).card := by exact_mod_cast cutSize_union_step H hU
    rw [hcard,Nat.cast_add]
    nlinarith only [hl,hR'.2,hbad]
  by_cases hhalf : 2*(R∪U).card ≤ Fintype.card V
  · have hmem : R∪U ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhalf,hnew⟩
    have hh := hmax _ hmem
    omega
  · have hcN : (R∪U).card+(R∪U)ᶜ.card=Fintype.card V := by
      rw [Finset.card_compl]
      exact Nat.add_sub_of_le (Finset.card_le_univ (R∪U))
    have hcsmall : 2*(R∪U)ᶜ.card ≤ Fintype.card V := by omega
    have hx := cutExpansion_small G hexp hcsmall
    rw [cutSize_compl] at hx
    have hl : (cutSize G (R∪U):ℝ) ≤ (cutSize H (R∪U):ℝ)+F.card := by
      exact_mod_cast cutSize_deleteEdges_loss G F (R∪U)
    have hcR : ((R∪U).card:ℝ)+(R∪U)ᶜ.card=Fintype.card V := by exact_mod_cast hcN
    have hcut : h*((Fintype.card V:ℝ)-(R∪U).card) ≤ a*h*(R∪U).card+F.card := by
      have he : (Fintype.card V:ℝ)-(R∪U).card=(R∪U)ᶜ.card := by linarith only [hcR]
      rw [he]
      linarith only [hx,hl,hnew]
    have hsizeN : 2*(R∪U).card ≤ Fintype.card V+R.card := by omega
    have hsize : 2*((R∪U).card:ℝ) ≤ (Fintype.card V:ℝ)+R.card := by exact_mod_cast hsizeN
    exact pruning_crossing_impossible ha ha₁ hh hremoved hsize hcut hbudget

theorem exists_pruned_six_elevenths (G : SimpleGraph V) (F : Finset (Sym2 V))
    {h : ℝ} (hh : 0 < h) (hexp : OAI.ErdosGallai.CutExpansion G h)
    (hbudget : (F.card:ℝ) < (25/297)*h*Fintype.card V) :
    ∃ R : Finset V, 2*R.card ≤ Fintype.card V ∧
      (R.card:ℝ) ≤ 11*F.card/(5*h) ∧
      ExpansionWithin (G.deleteEdges F) Rᶜ ((6/11)*h) := by
  obtain ⟨R,hR,hsize,hex⟩ := exists_pruned_expander G F hh
    (by norm_num : (0:ℝ) ≤ 6/11) (by norm_num : (6/11:ℝ) < 1) hexp (by nlinarith)
  refine ⟨R,hR,?_,hex⟩
  apply (le_div_iff₀ (by positivity : 0 < 5*h)).mpr
  nlinarith only [hsize]

end
end Cycle13
