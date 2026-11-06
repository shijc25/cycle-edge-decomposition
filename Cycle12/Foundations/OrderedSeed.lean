import Cycle12.Foundations.GLWExternalBlock

/-! Ordered seeds in an arbitrary finite graph, before changing to the
canonical external/prefix vertex types used by the suppression theorem. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def seedRho {V : Type} {p : ℕ} (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) (k : ℕ) : ℕ :=
  (univ.filter (fun i : Fin p => i.val<k ∧ ¬G.Adj root (a i))).card

def seedReservoir {V : Type} [Fintype V] [DecidableEq V] {p : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) : Finset V :=
  G.neighborFinset root \ univ.image a

structure OrderedSeed {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (t p : ℕ) where
  positive : 0<p
  small : p<t
  vertex : Fin p ↪ V
  first : vertex ⟨0,positive⟩=root
  missing : ∀ i, missingNeighbors G (seedReservoir G root vertex) (vertex i)≤
    p+i.val+1+seedRho G root vertex (i.val+1)

theorem seedRho_monotone {V : Type} {p : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) : Monotone (seedRho G root a) := by
  intro k l hkl
  apply card_le_card
  intro i hi
  have h := (mem_filter.mp hi).2
  exact mem_filter.mpr ⟨mem_univ _,h.1.trans_le hkl,h.2⟩

theorem seedRho_le {V : Type} {p : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) (k : ℕ) : seedRho G root a k≤k := by
  let S := univ.filter (fun i : Fin p => i.val<k ∧ ¬G.Adj root (a i))
  let f : S → Fin k := fun i => ⟨i.val.val,(mem_filter.mp i.property).2.1⟩
  have hf : Function.Injective f := by
    intro i j h
    exact Subtype.ext (Fin.ext (congrArg (fun x : Fin k => x.val) h))
  simpa only [Fintype.card_coe,Fintype.card_fin,S,seedRho] using Fintype.card_le_of_injective f hf

theorem seedReservoir_root_missing {V : Type} [Fintype V] [DecidableEq V] {p : ℕ}
    (G : SimpleGraph V) (root : V) (a : Fin p ↪ V) :
    missingNeighbors G (seedReservoir G root a) root=0 := by
  unfold missingNeighbors
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := mem_filter.mp hv
  exact h.2 ((G.mem_neighborFinset root v).mp (mem_sdiff.mp h.1).1)

namespace OrderedSeed
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V} {t p : ℕ}

def singletonVertex (root : V) : Fin 1 ↪ V where
  toFun := fun _ => root
  inj' := by intro i j _; exact Subsingleton.elim i j

def singleton (G : SimpleGraph V) (root : V) (ht : 1<t) : OrderedSeed G root t 1 where
  positive := by decide
  small := ht
  vertex := singletonVertex root
  first := rfl
  missing := by
    intro i
    change missingNeighbors G (seedReservoir G root (singletonVertex root)) root≤_
    rw [seedReservoir_root_missing]
    exact Nat.zero_le _

theorem exists_maximal (G : SimpleGraph V) (root : V) (ht : 1<t) :
    ∃ p : ℕ, ∃ A : OrderedSeed G root t p,
      ∀ q, Nonempty (OrderedSeed G root t q) → q≤p := by
  let P := fun q => Nonempty (OrderedSeed G root t q)
  have hP : P 1 := ⟨singleton G root ht⟩
  have h1 : 1≤t-1 := by omega
  obtain ⟨A⟩ := Nat.findGreatest_spec h1 hP
  refine ⟨Nat.findGreatest P (t-1),A,?_⟩
  rintro q ⟨B⟩
  apply Nat.le_findGreatest
  · have h := B.small; omega
  · exact ⟨B⟩

end OrderedSeed
end
end Cycle13
