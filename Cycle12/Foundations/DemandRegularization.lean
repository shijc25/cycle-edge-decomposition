import Cycle12.Foundations.IndexedDegreeSum
import Cycle12.Foundations.DemandRoutingOperations

/-! Regularization by adding a demand edge or lifting an existing edge.
The maximum finite edge count proves termination, and every operation
retains a pullback for actual edge-disjoint routes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure BoundedDemandExtension {V I : Type} [DecidableEq V] (a b : I → V) (q : ℕ) where
  Edges : Type
  edgeFintype : Fintype Edges
  left : Edges → V
  right : Edges → V
  loopless : ∀ i, left i≠right i
  degree : ∀ v, @Suppression.incidenceDegree Edges V edgeFintype _ left right v ≤ q
  pullback : Nonempty (DemandRouting (completeGraph V) left right) →
    Nonempty (DemandRouting (completeGraph V) a b)

attribute [instance] BoundedDemandExtension.edgeFintype

namespace BoundedDemandExtension
variable {V I : Type} [Fintype V] [DecidableEq V] {a b : I → V} {q : ℕ}

def addEdge (E : BoundedDemandExtension a b q) (x y : V) (hxy : x≠y)
    (hx : Suppression.incidenceDegree E.left E.right x < q)
    (hy : Suppression.incidenceDegree E.left E.right y < q) : BoundedDemandExtension a b q where
  Edges := E.Edges ⊕ Unit
  edgeFintype := inferInstance
  left := Sum.elim E.left (fun _ => x)
  right := Sum.elim E.right (fun _ => y)
  loopless := by rintro (i | i); exact E.loopless i; exact hxy
  degree := by
    intro v
    rw [append_edge_degree]
    by_cases hxv : x=v <;> by_cases hyv : y=v
    · exact (hxy (hxv.trans hyv.symm)).elim
    · have hh := hxv ▸ hx; simp only [if_pos hxv,if_neg hyv]; omega
    · have hh := hyv ▸ hy; simp only [if_neg hxv,if_pos hyv]; omega
    · have hh := E.degree v; simp only [if_neg hxv,if_neg hyv]; omega
  pullback := by
    rintro ⟨R⟩
    exact E.pullback ⟨R.restrict ⟨Sum.inl,Sum.inl_injective⟩⟩

theorem addEdge_card (E : BoundedDemandExtension a b q) (x y : V) (hxy : x≠y)
    (hx : Suppression.incidenceDegree E.left E.right x < q)
    (hy : Suppression.incidenceDegree E.left E.right y < q) :
    Fintype.card (E.addEdge x y hxy hx hy).Edges=Fintype.card E.Edges+1 := by
  change Fintype.card (E.Edges ⊕ Unit)=Fintype.card E.Edges+1
  rw [Fintype.card_sum]
  simp

def liftEdge (E : BoundedDemandExtension a b q) (z : V) (i : E.Edges)
    (hi : E.left i≠z ∧ E.right i≠z)
    (hz : Suppression.incidenceDegree E.left E.right z+2 ≤ q) : BoundedDemandExtension a b q where
  Edges := LiftIndex ({i} : Finset E.Edges)
  edgeFintype := inferInstance
  left := liftLeft E.left (fun _ => z) {i}
  right := liftRight E.right (fun _ => z) {i}
  loopless := lift_loopless _ _ _ _ E.loopless (by
    intro j hj; have he := mem_singleton.mp hj; subst j; exact ⟨hi.1.symm,hi.2.symm⟩)
  degree := by
    intro v
    rw [lift_incidence_degree]
    by_cases hzv : z=v
    · subst v; simpa using hz
    · simpa only [hzv,filter_false,card_empty,mul_zero,add_zero] using E.degree v
  pullback := by
    rintro ⟨R⟩
    exact E.pullback ⟨R.pullback_lift⟩

theorem liftEdge_card (E : BoundedDemandExtension a b q) (z : V) (i : E.Edges)
    (hi : E.left i≠z ∧ E.right i≠z)
    (hz : Suppression.incidenceDegree E.left E.right z+2 ≤ q) :
    Fintype.card (E.liftEdge z i hi hz).Edges=Fintype.card E.Edges+1 := by
  exact singleton_lift_card i

end BoundedDemandExtension

variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem exists_even_regular_completion (a b : I → V) (hne : ∀ i, a i≠b i) {k : ℕ}
    (hn : 2 ≤ Fintype.card V) (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2*k) :
    ∃ E : BoundedDemandExtension a b (2*k),
      ∀ v, Suppression.incidenceDegree E.left E.right v=2*k := by
  let E₀ : BoundedDemandExtension a b (2*k) := {
    Edges := I
    edgeFintype := inferInstance
    left := a
    right := b
    loopless := hne
    degree := hd
    pullback := id }
  let T := (range (2*k*Fintype.card V+1)).filter
    (fun m => ∃ E : BoundedDemandExtension a b (2*k), Fintype.card E.Edges=m)
  have hmem : ∀ E : BoundedDemandExtension a b (2*k), Fintype.card E.Edges∈T := by
    intro E
    refine mem_filter.mpr ⟨mem_range.mpr ?_,E,rfl⟩
    have hh := indexed_card_le_degree_cap E.left E.right E.degree
    omega
  obtain ⟨m,hm,hmax⟩ := exists_max_image T id ⟨_,hmem E₀⟩
  obtain ⟨E,hE⟩ := (mem_filter.mp hm).2
  have hmaxE : ∀ E' : BoundedDemandExtension a b (2*k), Fintype.card E'.Edges ≤ Fintype.card E.Edges := by
    intro E'; have hh := hmax _ (hmem E'); dsimp at hh; omega
  refine ⟨E,?_⟩
  intro v
  by_contra hv
  have hvlt : Suppression.incidenceDegree E.left E.right v < 2*k := by
    have hh := E.degree v; omega
  have hother : ∀ u, u≠v → Suppression.incidenceDegree E.left E.right u=2*k := by
    intro u huv
    by_contra hu
    have hult : Suppression.incidenceDegree E.left E.right u < 2*k := by
      have hh := E.degree u; omega
    have hh := hmaxE (E.addEdge u v huv hult hvlt)
    rw [BoundedDemandExtension.addEdge_card] at hh
    omega
  have hv2 := single_even_deficit E.left E.right v hvlt hother
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u,hu⟩ := exists_ne v
  obtain ⟨i,hi⟩ := exists_indexed_edge_away E.left E.right E.loopless
    (u:=u) (v:=v)
    (by rw [hother u hu]; exact hvlt)
  have hh := hmaxE (E.liftEdge v i hi hv2)
  rw [BoundedDemandExtension.liftEdge_card] at hh
  omega

end
end Cycle13
