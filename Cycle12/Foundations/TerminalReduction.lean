import Cycle12.Foundations.InteriorFactor
import Cycle12.Foundations.ThreeHubReduction
import Cycle12.Foundations.LoopRemoval

/-! Interfaces for composing actual terminal-pairability reductions. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure TerminalReduction {V I : Type} [Fintype V] (a b : I → V) (drop cap : ℕ) where
  Vertices : Type
  vertexFintype : Fintype Vertices
  vertexDecidableEq : DecidableEq Vertices
  Edges : Type
  edgeFintype : Fintype Edges
  left : Edges → Vertices
  right : Edges → Vertices
  order : @Fintype.card Vertices vertexFintype+drop=Fintype.card V
  degree : ∀ v, @Suppression.incidenceDegree Edges Vertices edgeFintype vertexDecidableEq left right v ≤ cap
  pullback : Nonempty (DemandRouting (completeGraph Vertices) left right) →
    Nonempty (DemandRouting (completeGraph V) a b)

attribute [instance] TerminalReduction.vertexFintype TerminalReduction.vertexDecidableEq
  TerminalReduction.edgeFintype

variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def tripleOfFinset (B : Finset V) (hB : B.card=3) : Fin 3 ↪ V :=
  (Finset.equivFinOfCardEq hB).symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩

theorem tripleOfFinset_mem (B : Finset V) (hB : B.card=3) (r : Fin 3) :
    tripleOfFinset B hB r∈B := ((Finset.equivFinOfCardEq hB).symm r).property

theorem mem_tripleOfFinset (B : Finset V) (hB : B.card=3) {v : V} (hv : v∈B) :
    ∃ r, tripleOfFinset B hB r=v := by
  refine ⟨Finset.equivFinOfCardEq hB ⟨v,hv⟩,?_⟩
  exact congrArg Subtype.val ((Finset.equivFinOfCardEq hB).symm_apply_apply ⟨v,hv⟩)

theorem exists_independent_three (a b : I → V) (hne : ∀ i, a i≠b i) {d : ℕ}
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ d)
    (hspace : 2*(d+1) < Fintype.card V) :
    ∃ w : Fin 3 ↪ V, ∀ r s i, ¬(a i=w r ∧ b i=w s) := by
  obtain ⟨B,_,hB,_,hBi⟩ := exists_independent_extension (indexedSupport a b) ∅ ∅
    (fun v => (indexedSupport_degree_le a b v).trans (hd v)) (by simp) (by simp)
    (by simp : (∅ : Finset V).card ≤ 3) (by simpa using hspace)
  refine ⟨tripleOfFinset B hB,?_⟩
  intro r s i hi
  exact hBi (tripleOfFinset_mem B hB r) (tripleOfFinset_mem B hB s)
    (fun he => hne i (hi.1.trans (he.trans hi.2.symm)))
    ⟨fun he => hne i (hi.1.trans (he.trans hi.2.symm)),i,congrArg₂ Sym2.mk hi.1 hi.2⟩

theorem independent_inside_no_edge (a b : I → V) (hne : ∀ i, a i≠b i)
    (w : Fin 3 ↪ V) (B : Finset (SeedInterior w))
    (hB : (indexedSupport (seedKeepLeft a b w) (seedKeepRight a b w)).IsIndepSet B) :
    ∀ i, ¬(a i∈B.image Subtype.val ∧ b i∈B.image Subtype.val) := by
  intro i hi
  obtain ⟨x,hx,hexa⟩ := mem_image.mp hi.1
  obtain ⟨y,hy,heyb⟩ := mem_image.mp hi.2
  have hiK : ¬seedEdgePred a b w i := by
    rintro ⟨r,ha|hb⟩
    · exact x.property r (hexa.trans ha)
    · exact y.property r (heyb.trans hb)
  let j : SeedKeep a b w := ⟨i,hiK⟩
  have hxj : seedKeepLeft a b w j=x := Subtype.ext hexa.symm
  have hyj : seedKeepRight a b w j=y := Subtype.ext heyb.symm
  have hxy : x≠y := fun he => hne i (hexa.symm.trans ((congrArg Subtype.val he).trans heyb))
  exact hB hx hy hxy ⟨hxy,j,by rw [hxj,hyj]⟩

theorem residual_inl_factor_degree {a b : I → V} {w : Fin 3 ↪ V}
    (D : SeedEdgeData a b w) (target : SeedStar a b w ↪ SeedInterior w)
    (F : Finset (SeedKeep a b w)) (v : SeedInterior w) :
    indexedDegreeOn (D.residualLeft target) D.residualRight (F.image Sum.inl) v=
      indexedDegreeOn (seedKeepLeft a b w) (seedKeepRight a b w) F v := by
  exact indexedDegreeOn_image _ _ ⟨Sum.inl,Sum.inl_injective⟩ F v

end
end Cycle13
