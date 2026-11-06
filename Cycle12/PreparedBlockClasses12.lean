import Cycle12.PreparedClassData12
import Cycle12.ClasswiseContraction12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- The retained class remembers the actual local preparation that
removed its other original edges. Outside edges, internal edges, pairs,
and alternating matching groups have distinct prescribed roles. -/
def PreparedClassOrigin12 (G : SimpleGraph V) (A : I → Finset V) (Q : ℕ)
    (e : Sym2 (Option I)) (H : SimpleGraph V) : Prop :=
  (∃ i,e=s(some i,some i) ∧ H=⊥) ∨
  (e=s(none,none) ∧ H=edgeLabelGraph G (blockLabel A) e) ∨
  (∃ i,e=s(some i,none) ∧
    ∃ D : OutsideLedger12 (edgeLabelGraph G (blockLabel A) e) (A i),H=D.pairs.residue) ∨
  (∃ i j,i ≠ j ∧ e=s(some i,some j) ∧
    ∃ D : CrossingLedger12 (edgeLabelGraph G (blockLabel A) e) (A i) (A j) Q,
      H=matchingRetainedGraph D.second.residue D.matching)

structure PreparedBlockClass12 (G : SimpleGraph V) (A : I → Finset V) (Q : ℕ)
    (e : Sym2 (Option I)) where
  retained : SimpleGraph V
  subset : retained ≤ edgeLabelGraph G (blockLabel A) e
  internal : ∀ i,e=s(some i,some i) → retained=⊥
  crossing : ∀ i j,i ≠ j → e=s(some i,some j) → retained.edgeSet.ncard ≤ 1
  outside : ∀ i,e=s(some i,none) → ∀ v,v∉blockUnion A → retained.degree v ≤ 1
  origin : PreparedClassOrigin12 G A Q e retained

theorem prepared_internal_class (G : SimpleGraph V) (A : I → Finset V) (Q : ℕ) (i : I) :
    Nonempty (PreparedBlockClass12 G A Q s(some i,some i)) := by
  refine ⟨⟨⊥,bot_le,fun _ _ => rfl,?_,?_,Or.inl ⟨i,rfl,rfl⟩⟩⟩
  · intro j k hjk he
    simp
  · intro j he v hv
    simp

theorem prepared_external_class (G : SimpleGraph V) (A : I → Finset V) (Q : ℕ) :
    Nonempty (PreparedBlockClass12 G A Q s(none,none)) := by
  refine ⟨⟨edgeLabelGraph G (blockLabel A) s(none,none),le_rfl,?_,?_,?_,
    Or.inr (Or.inl ⟨rfl,rfl⟩)⟩⟩
  · intro i he
    simp [Sym2.eq_iff] at he
  · intro i j hij he
    simp [Sym2.eq_iff] at he
  · intro i he
    simp [Sym2.eq_iff] at he

theorem prepared_outside_class (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (Q : ℕ) (i : I) :
    Nonempty (PreparedBlockClass12 G A Q s(some i,none)) := by
  have hU : Disjoint (A i) (blockUnion A)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro v hv hn
    exact (mem_compl.mp hn) ((mem_blockUnion A v).mpr ⟨i,hv⟩)
  have hcross : ∀ {x y},(edgeLabelGraph G (blockLabel A) s(some i,none)).Adj x y →
      (x∈A i ∧ y∈(blockUnion A)ᶜ) ∨ (x∈(blockUnion A)ᶜ ∧ y∈A i) := by
    intro x y hxy
    simpa only [mem_compl] using ((block_outside_graph G A hd i x y).mp hxy).2
  obtain ⟨D⟩ := outsideLedger_exists _ _ _ hU hcross
  refine ⟨⟨D.pairs.residue,fun _ _ h => h.1,?_,?_,?_,
    Or.inr (Or.inr (Or.inl ⟨i,rfl,D,rfl⟩))⟩⟩
  · intro j he
    simp [Sym2.eq_iff] at he
  · intro j k hjk he
    simp [Sym2.eq_iff] at he
  · intro j he v hv
    exact D.degree v (fun hvi => hv ((mem_blockUnion A v).mpr ⟨i,hvi⟩))

theorem prepared_crossing_class (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) {Q : ℕ} (hQ : 0 < Q)
    (i j : I) (hij : i ≠ j) : Nonempty (PreparedBlockClass12 G A Q s(some i,some j)) := by
  have hcross : ∀ {x y},(edgeLabelGraph G (blockLabel A) s(some i,some j)).Adj x y →
      (x∈A i ∧ y∈A j) ∨ (x∈A j ∧ y∈A i) := by
    intro x y hxy
    exact ((block_cross_graph G A hd i j x y).mp hxy).2
  obtain ⟨D⟩ := crossingLedger_exists _ _ _ (hd hij) hcross hQ
  refine ⟨⟨matchingRetainedGraph D.second.residue D.matching,D.retained_le,?_,
    fun _ _ _ _ => D.retained_small,?_,Or.inr (Or.inr (Or.inr ⟨i,j,hij,rfl,D,rfl⟩))⟩⟩
  · intro k he
    have h : i=k ∧ j=k := by simpa only [Sym2.eq_iff,Option.some.injEq,or_self] using he
    exact False.elim (hij (h.1.trans h.2.symm))
  · intro k he
    simp only [Sym2.eq_iff,Option.some_ne_none,and_false,false_and,or_self] at he

/-- Every actual endpoint-label class is prepared, with its original
pairing/grouping witness retained for the later joint routing call. -/
theorem prepared_block_class_exists (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) {Q : ℕ} (hQ : 0 < Q)
    (e : Sym2 (Option I)) : Nonempty (PreparedBlockClass12 G A Q e) := by
  induction e using Sym2.ind with
  | _ x y =>
    cases x with
    | none =>
      cases y with
      | none => exact prepared_external_class G A Q
      | some j =>
        rw [Sym2.eq_swap]
        exact prepared_outside_class G A hd Q j
    | some i =>
      cases y with
      | none => exact prepared_outside_class G A hd Q i
      | some j =>
        by_cases hij : i=j
        · subst j
          exact prepared_internal_class G A Q i
        · exact prepared_crossing_class G A hd hQ i j hij

structure PreparedBlockBatch12 (G : SimpleGraph V) (A : I → Finset V) (Q : ℕ) where
  classes : ∀ e : Sym2 (Option I),PreparedBlockClass12 G A Q e

theorem prepared_block_batch_exists (G : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) {Q : ℕ} (hQ : 0 < Q) :
    Nonempty (PreparedBlockBatch12 G A Q) :=
  ⟨⟨fun e => Classical.choice (prepared_block_class_exists G A hd hQ e)⟩⟩

def PreparedBlockBatch12.retained {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}
    (P : PreparedBlockBatch12 G A Q) : SimpleGraph V := ⨆ e,(P.classes e).retained

theorem PreparedBlockBatch12.quotient_unique {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}
    (P : PreparedBlockBatch12 G A Q) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    P.retained ≤ G ∧
      (∀ {x y},P.retained.Adj x y → contractVertex A x ≠ contractVertex A y) ∧
      Set.InjOn (Sym2.map (contractVertex A)) P.retained.edgeSet :=
  classwise_contraction_unique G A hd (fun e => (P.classes e).retained)
    (fun e => (P.classes e).subset)
    (fun i => (P.classes s(some i,some i)).internal i rfl)
    (fun i j hij => (P.classes s(some i,some j)).crossing i j hij rfl)
    (fun i v hv => (P.classes s(some i,none)).outside i rfl v hv)

end
end Cycle12
