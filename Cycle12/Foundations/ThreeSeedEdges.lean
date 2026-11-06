import Cycle12.Foundations.FiberBinaryLabels
import Cycle12.Foundations.IndexedLineGraph

/-! Reduction of arbitrary indexed multigraphs to the eight-choice
certificate for three independent prescribed vertices. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def seedEdgePred (a b : I → V) (w : Fin 3 → V) (i : I) : Prop :=
  ∃ r, a i=w r ∨ b i=w r

structure SeedEdgeData (a b : I → V) (w : Fin 3 ↪ V) where
  group : {i // seedEdgePred a b w i} → Fin 3
  other : {i // seedEdgePred a b w i} → V
  ends : ∀ i, (a i.val=w (group i) ∧ b i.val=other i) ∨
    (b i.val=w (group i) ∧ a i.val=other i)
  other_ne : ∀ i r, other i≠w r

lemma seed_group_unique (a b : I → V) (w : Fin 3 ↪ V)
    (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    (i : I) (r s : Fin 3) (hr : a i=w r ∨ b i=w r) (hs : a i=w s ∨ b i=w s) : r=s := by
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · exact w.injective (hr.symm.trans hs)
  · exact (hsep r s i ⟨hr,hs⟩).elim
  · exact (hsep s r i ⟨hs,hr⟩).elim
  · exact w.injective (hr.symm.trans hs)

def seedEdgeData (a b : I → V) (w : Fin 3 ↪ V)
    (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s)) : SeedEdgeData a b w := by
  let g : {i // seedEdgePred a b w i} → Fin 3 := fun i => Classical.choose i.property
  have hg : ∀ i, a i.val=w (g i) ∨ b i.val=w (g i) := fun i => Classical.choose_spec i.property
  let q : {i // seedEdgePred a b w i} → V := fun i => if a i.val=w (g i) then b i.val else a i.val
  have he : ∀ i, (a i.val=w (g i) ∧ b i.val=q i) ∨ (b i.val=w (g i) ∧ a i.val=q i) := by
    intro i
    by_cases ha : a i.val=w (g i)
    · exact Or.inl ⟨ha,by simp [q,ha]⟩
    · exact Or.inr ⟨(hg i).resolve_left ha,by simp [q,ha]⟩
  refine ⟨g,q,he,?_⟩
  intro i r hr
  rcases he i with hi | hi
  · exact hsep (g i) r i.val ⟨hi.1,hi.2.trans hr⟩
  · exact hsep r (g i) i.val ⟨hi.2.trans hr,hi.1⟩

namespace SeedEdgeData
variable {a b : I → V} {w : Fin 3 ↪ V} (D : SeedEdgeData a b w)

lemma group_incident (i : {i // seedEdgePred a b w i}) :
    a i.val=w (D.group i) ∨ b i.val=w (D.group i) :=
  (D.ends i).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
lemma other_incident (i : {i // seedEdgePred a b w i}) :
    a i.val=D.other i ∨ b i.val=D.other i :=
  (D.ends i).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

lemma fiber_le_two (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) (r : Fin 3) :
    (univ.filter (fun i => D.group i=r)).card ≤ 2 := by
  let F := univ.filter (fun i => D.group i=r)
  have hs : F.image Subtype.val ⊆ indexedIncident a b (w r) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2 ▸ D.group_incident j⟩
  have hh := (card_le_card hs).trans ((indexedIncident_card_le a b (w r)).trans (hd (w r)))
  rw [card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

def crossGraph : SimpleGraph {i // seedEdgePred a b w i} where
  Adj i j := D.group i≠D.group j ∧ D.other i=D.other j
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma cross_degree_le_one (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2)
    (i : {i // seedEdgePred a b w i}) : D.crossGraph.degree i ≤ 1 := by
  have hs : (D.crossGraph.neighborFinset i).image Subtype.val ⊆
      (indexedIncident a b (D.other i)).erase i.val := by
    intro j hj
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hj
    have hz := (D.crossGraph.mem_neighborFinset i z).mp hz
    have hne : z.val≠i.val := by intro h; exact hz.1 (congrArg D.group (Subtype.ext h).symm)
    exact mem_erase.mpr ⟨hne,mem_filter.mpr ⟨mem_univ _,hz.2.symm ▸ D.other_incident z⟩⟩
  have hh := card_le_card hs
  rw [card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at hh
  have hmem : i.val∈indexedIncident a b (D.other i) := mem_filter.mpr ⟨mem_univ _,D.other_incident i⟩
  have hc := (indexedIncident_card_le a b (D.other i)).trans (hd (D.other i))
  have her := card_erase_add_one hmem
  omega

include D in
lemma card_le_six (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    Fintype.card {i // seedEdgePred a b w i} ≤ 6 := by
  have hc := card_eq_sum_card_fiberwise (f:=D.group) (s:=univ) (t:=univ) (fun _ _ => mem_univ _)
  have hh := sum_le_sum (fun r (_ : r∈(univ : Finset (Fin 3))) => D.fiber_le_two hd r)
  rw [← hc] at hh
  simpa using hh

lemma cross_edges_le_three (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    D.crossGraph.edgeFinset.card ≤ 3 := by
  have hh := sum_le_sum (fun i (_ : i∈(univ : Finset {i // seedEdgePred a b w i})) => D.cross_degree_le_one hd i)
  rw [D.crossGraph.sum_degrees_eq_twice_card_edges] at hh
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at hh
  have hc := D.card_le_six hd
  omega

lemma cross_of_incident (i j : {i // seedEdgePred a b w i})
    (hij : (indexedLineGraph a b).Adj i.val j.val) (hg : D.group i≠D.group j) :
    D.crossGraph.Adj i j := by
  obtain ⟨hne,v,hi,hj⟩ := (indexedLineGraph_adj a b i.val j.val).mp hij
  refine ⟨hg,?_⟩
  have hvi : v=w (D.group i) ∨ v=D.other i := by
    rcases D.ends i with he | he <;> rcases hi with hi | hi
    · exact Or.inl (hi.symm.trans he.1)
    · exact Or.inr (hi.symm.trans he.2)
    · exact Or.inr (hi.symm.trans he.2)
    · exact Or.inl (hi.symm.trans he.1)
  have hvj : v=w (D.group j) ∨ v=D.other j := by
    rcases D.ends j with he | he <;> rcases hj with hj | hj
    · exact Or.inl (hj.symm.trans he.1)
    · exact Or.inr (hj.symm.trans he.2)
    · exact Or.inr (hj.symm.trans he.2)
    · exact Or.inl (hj.symm.trans he.1)
  rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
  · exact (hg (w.injective (hvi.symm.trans hvj))).elim
  · exact (D.other_ne j (D.group i) (hvj.symm.trans hvi)).elim
  · exact (D.other_ne i (D.group j) (hvi.symm.trans hvj)).elim
  · exact hvi.symm.trans hvj

end SeedEdgeData

theorem exists_seed_edge_coloring (a b : I → V) (w : Fin 3 ↪ V)
    (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) :
    ∃ c : {i // seedEdgePred a b w i} → Fin 3,
      (∀ i r, (a i.val=w r ∨ b i.val=w r) → c i≠r) ∧
      (∀ i j, (indexedLineGraph a b).Adj i.val j.val → c i≠c j) := by
  let D := seedEdgeData a b w hsep
  obtain ⟨slot,hslot⟩ := exists_fiber_binary_labels D.group (D.fiber_le_two hd)
  obtain ⟨c,hc,hwithin,hcross⟩ := exists_three_star_coloring D.crossGraph D.group slot
    (D.cross_edges_le_three hd) (fun _ _ h => h.1)
  refine ⟨c,?_,?_⟩
  · intro i r hi
    have hr := seed_group_unique a b w hsep i.val (D.group i) r (D.group_incident i) hi
    simpa only [hr] using hc i
  · intro i j hij
    by_cases hg : D.group i=D.group j
    · apply hwithin i j hg
      intro h
      exact ((indexedLineGraph_adj a b i.val j.val).mp hij).1
        (congrArg Subtype.val (hslot i j hg h))
    · exact hcross i j (D.cross_of_incident i j hij hg)

end
end Cycle13
