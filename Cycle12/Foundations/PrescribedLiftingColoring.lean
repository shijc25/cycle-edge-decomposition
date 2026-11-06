import Cycle12.Foundations.ThreeSeedEdges
import Cycle12.Foundations.ColorExtension
import Cycle12.Foundations.MarkedColorBalance

/-! GMM Claim 9: prescribed, balanced lifting colors, including indexed
parallel edges. The initial coloring uses the eight-choice certificate;
the balancing step uses marked bichromatic components. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem exists_prescribed_lifting_coloring (a b : I → V) (w : Fin 3 ↪ V)
    (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    ∃ f : (liftingGraph a b).Coloring (Fin 3), ∀ r, f (.inl (w r))=r := by
  obtain ⟨c,havoid,hproper⟩ := exists_seed_edge_coloring a b w hsep hd
  let S := univ.filter (seedEdgePred a b w)
  let f₀ : I → Fin 3 := fun i => if hi : seedEdgePred a b w i then c ⟨i,hi⟩ else 0
  have hf₀ : ∀ i∈S, ∀ j∈S, (indexedLineGraph a b).Adj i j → f₀ i≠f₀ j := by
    intro i hi j hj hij
    have hi := (mem_filter.mp hi).2
    have hj := (mem_filter.mp hj).2
    simpa only [f₀,dif_pos hi,dif_pos hj] using hproper ⟨i,hi⟩ ⟨j,hj⟩ hij
  obtain ⟨edgeColor,hfixed⟩ := exists_coloring_extension (indexedLineGraph a b) S f₀ hf₀
    (fun i => by have hh := indexedLineGraph_degree_le_two a b hd i; simpa using Nat.lt_succ_of_le hh)
  have hedge : ∀ (i : I) (hi : seedEdgePred a b w i), edgeColor i=c ⟨i,hi⟩ := by
    intro i hi
    have hh := hfixed i (mem_filter.mpr ⟨mem_univ _,hi⟩)
    simpa only [f₀,dif_pos hi] using hh
  have hvcolor : ∀ v : V, ∃ x : Fin 3,
      (∀ i, (a i=v ∨ b i=v) → edgeColor i≠x) ∧ (∀ r, w r=v → x=r) := by
    intro v
    by_cases hv : ∃ r, w r=v
    · obtain ⟨r,rfl⟩ := hv
      refine ⟨r,?_,?_⟩
      · intro i hi
        have hPi : seedEdgePred a b w i := ⟨r,hi⟩
        rw [hedge i hPi]
        exact havoid ⟨i,hPi⟩ r hi
      · intro s hs
        exact (w.injective hs).symm
    · let bad := (indexedIncident a b v).image edgeColor
      have hbad : bad.card < (univ : Finset (Fin 3)).card := by
        have hh := (card_image_le (s:=indexedIncident a b v) (f:=edgeColor)).trans
          ((indexedIncident_card_le a b v).trans (hd v))
        simpa only [card_univ,Fintype.card_fin] using Nat.lt_succ_of_le hh
      obtain ⟨x,hx,hxbad⟩ := exists_mem_notMem_of_card_lt_card hbad
      refine ⟨x,?_,?_⟩
      · intro i hi he
        exact hxbad (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,he⟩)
      · intro r hr
        exact (hv ⟨r,hr⟩).elim
  choose vertexColor hvertex hseed using hvcolor
  refine ⟨Coloring.mk (Sum.elim vertexColor edgeColor) ?_,?_⟩
  · intro x y hxy
    rcases hxy with ⟨hne,v,hx,hy⟩
    cases x with
    | inl x =>
      cases y with
      | inl y => exact (hne (congrArg Sum.inl (hx.trans hy.symm))).elim
      | inr j =>
        change vertexColor x≠edgeColor j
        exact (hvertex x j (hx.symm ▸ hy)).symm
    | inr i =>
      cases y with
      | inl y =>
        change edgeColor i≠vertexColor y
        exact hvertex y i (hy.symm ▸ hx)
      | inr j =>
        apply edgeColor.valid
        exact (indexedLineGraph_adj a b i j).mpr
          ⟨fun h => hne (congrArg Sum.inr h),v,hx,hy⟩
  · intro r
    exact hseed (w r) r rfl

lemma original_marked_colorSize (f : V⊕I → Fin 3) (r : Fin 3) :
    markedColorSize f ((univ : Finset V).image Sum.inl) r=
      colorSize (fun v => f (.inl v)) r := by
  unfold markedColorSize colorSize
  symm
  apply card_bij (fun x _ => Sum.inl x)
  · intro x hx
    exact mem_filter.mpr ⟨mem_image.mpr ⟨x,mem_univ _,rfl⟩,(mem_filter.mp hx).2⟩
  · intro x hx y hy he
    exact Sum.inl.inj he
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
    exact ⟨v,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,rfl⟩

theorem exists_balanced_prescribed_lifting_coloring (a b : I → V) (w : Fin 3 ↪ V)
    (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    ∃ f : (liftingGraph a b).Coloring (Fin 3), (∀ r, f (.inl (w r))=r) ∧
      ∀ r s, colorSize (fun v => f (.inl v)) r ≤ colorSize (fun v => f (.inl v)) s+2 := by
  obtain ⟨f₀,hf₀⟩ := exists_prescribed_lifting_coloring a b w hsep hd
  let M : Finset (V⊕I) := univ.image Sum.inl
  obtain ⟨f,hfixed,hbalanced⟩ := exists_marked_balanced_coloring (liftingGraph a b) M
    (fun r => Sum.inl (w r)) (fun r => mem_image.mpr ⟨w r,mem_univ _,rfl⟩) f₀ hf₀
    (by
      intro f r s hrs c
      apply component_marked_le_two _ M (lifting_twoColor_degree a b f r s hrs)
      intro x hx
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
      exact lifting_twoColor_original_degree a b f r s hrs v)
  refine ⟨f,hfixed,fun r s => ?_⟩
  have hh := hbalanced r s
  simpa only [M,original_marked_colorSize] using hh

end
end Cycle13
