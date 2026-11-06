import Cycle12.Foundations.OrderedListColoring

/-! Actual edge-disjoint two-edge Link paths through a reservoir, obtained
from exact ordered missing-neighbor and earlier-load inequalities. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I V : Type} [Fintype I] [LinearOrder I] [DecidableEq V]

def linkConflict (a b : I → V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ (a i=a j ∨ a i=b j ∨ b i=a j ∨ b i=b j)
  symm := ⟨by intro i j h; grind⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def priorLinkLoad (a b : I → V) (i : I) (v : V) : ℕ :=
  (univ.filter (fun j => j < i ∧ (v=a j ∨ v=b j))).card

def missingNeighbors (G : SimpleGraph V) (D : Finset V) (v : V) : ℕ :=
  (D.filter (fun w => ¬G.Adj v w)).card

def commonChoices (G : SimpleGraph V) (D : Finset V) (u v : V) : Finset V :=
  D.filter (fun w => G.Adj u w ∧ G.Adj v w)

lemma commonChoices_card (G : SimpleGraph V) (D : Finset V) (u v : V) :
    D.card ≤ (commonChoices G D u v).card + missingNeighbors G D u + missingNeighbors G D v := by
  let X := D.filter (fun w => ¬G.Adj u w)
  let Y := D.filter (fun w => ¬G.Adj v w)
  have hs : D ⊆ commonChoices G D u v ∪ X ∪ Y := by
    intro w hw
    by_cases hu : G.Adj u w <;> by_cases hv : G.Adj v w <;>
      simp_all [commonChoices, X, Y]
  have hc := card_le_card hs
  have h₁ := card_union_le (commonChoices G D u v ∪ X) Y
  have h₂ := card_union_le (commonChoices G D u v) X
  change D.card ≤ (commonChoices G D u v).card + X.card + Y.card
  omega

lemma earlier_link_conflicts_le (a b : I → V) (i : I) :
    (univ.filter (fun j => j < i ∧ (linkConflict a b).Adj i j)).card ≤
      priorLinkLoad a b i (a i) + priorLinkLoad a b i (b i) := by
  let X := univ.filter (fun j => j < i ∧ (a i=a j ∨ a i=b j))
  let Y := univ.filter (fun j => j < i ∧ (b i=a j ∨ b i=b j))
  have hs : univ.filter (fun j => j < i ∧ (linkConflict a b).Adj i j) ⊆ X ∪ Y := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    rcases hj'.2.2 with h | h | h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hj'.1,Or.inl h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hj'.1,Or.inr h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hj'.1,Or.inl h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hj'.1,Or.inr h⟩)
  exact (card_le_card hs).trans (card_union_le X Y)

theorem exists_link_labels (G : SimpleGraph V) (D : Finset V) (hD : D.Nonempty)
    (a b : I → V)
    (hroom : ∀ i, missingNeighbors G D (a i) + missingNeighbors G D (b i) +
      priorLinkLoad a b i (a i) + priorLinkLoad a b i (b i) < D.card) :
    ∃ f : (linkConflict a b).Coloring V,
      ∀ i, f i ∈ D ∧ G.Adj (a i) (f i) ∧ G.Adj (b i) (f i) := by
  letI : Nonempty V := ⟨hD.choose⟩
  obtain ⟨f,hf⟩ := exists_ordered_list_coloring (linkConflict a b)
    (fun i => commonChoices G D (a i) (b i)) (by
      intro i
      have h₁ := commonChoices_card G D (a i) (b i)
      have h₂ := earlier_link_conflicts_le a b i
      have h₃ := hroom i
      omega)
  exact ⟨f,fun i => mem_filter.mp (hf i)⟩

theorem exists_ordered_links (G : SimpleGraph V) (D : Finset V) (hD : D.Nonempty)
    (a b : I → V) (hne : ∀ i, a i ≠ b i)
    (ha : ∀ i, a i ∉ D) (hb : ∀ i, b i ∉ D)
    (hroom : ∀ i, missingNeighbors G D (a i) + missingNeighbors G D (b i) +
      priorLinkLoad a b i (a i) + priorLinkLoad a b i (b i) < D.card) :
    ∃ P : ∀ i, G.Path (a i) (b i),
      Pairwise (fun i j => Disjoint (P i).val.edgeSet (P j).val.edgeSet) ∧
      (∀ i, (P i).val.length=2) ∧
      ∀ i v, v ∈ (P i).val.support → v=a i ∨ v=b i ∨ v ∈ D := by
  obtain ⟨f,hf⟩ := exists_link_labels G D hD a b hroom
  let W := fun i => ((hf i).2.1).toWalk.append ((hf i).2.2.symm).toWalk
  have hWpath : ∀ i, (W i).IsPath := by
    intro i
    have hai : a i ≠ f i := fun h => ha i (h ▸ (hf i).1)
    have hbi : b i ≠ f i := fun h => hb i (h ▸ (hf i).1)
    simp [W, Walk.isPath_def, Adj.toWalk, Walk.support_append, hai, hbi.symm, hne i]
  have horigin : ∀ i e, e ∈ (W i).edgeSet →
      ∃ v, (v=a i ∨ v=b i) ∧ e=s(v,f i) := by
    intro i e he
    simp only [W, Walk.edgeSet_append, Adj.toWalk, Walk.edgeSet_cons,
      Walk.edgeSet_nil, Set.mem_union, Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at he
    rcases he with he | he
    · exact ⟨a i,Or.inl rfl,he⟩
    · exact ⟨b i,Or.inr rfl,he.trans (Sym2.eq_swap)⟩
  refine ⟨fun i => ⟨W i,hWpath i⟩,?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    obtain ⟨x,hx,hex⟩ := horigin i e hei
    obtain ⟨y,hy,hey⟩ := horigin j e hej
    rcases Sym2.eq_iff.mp (hex.symm.trans hey) with ⟨hxy,hijcolor⟩ | ⟨hxf,hfy⟩
    · have hadj : (linkConflict a b).Adj i j := by
        refine ⟨hij,?_⟩
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> grind
      exact f.valid hadj hijcolor
    · have hxD : x ∉ D := by rcases hx with rfl | rfl; exact ha i; exact hb i
      exact hxD (hxf ▸ (hf j).1)
  · intro i
    simp [W,Adj.toWalk]
  · intro i v hv
    simp only [W, Adj.toWalk, Walk.support_append, Walk.support_cons, Walk.support_nil,
      List.tail_cons, List.mem_append, List.mem_cons, List.mem_singleton] at hv
    simp only [List.not_mem_nil, or_false] at hv
    rcases hv with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (h ▸ (hf i).1))
    · exact Or.inr (Or.inl h)

end
end Cycle13
