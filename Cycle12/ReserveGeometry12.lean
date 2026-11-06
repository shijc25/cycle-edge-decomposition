import Cycle12.ReservedSpokeChoice12

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V J : Type} [Fintype V] [Fintype J]

/-- The spanning graph consisting of actual reserved spokes. -/
def spokeGraph (root f : J → V) : SimpleGraph V :=
  fromEdgeSet (Set.range (fun j => s(root j,f j)))

theorem spokeGraph_le (H : SimpleGraph V) (root f : J → V)
    (hadj : ∀ j, H.Adj (root j) (f j)) : spokeGraph root f ≤ H := by
  intro x y hxy
  change (∃ j, s(root j,f j) = s(x,y)) ∧ x ≠ y at hxy
  obtain ⟨⟨j,hj⟩,_⟩ := hxy
  have hh : s(root j,f j) ∈ H.edgeSet := hadj j
  change s(x,y) ∈ H.edgeSet
  exact hj ▸ hh

theorem spokeGraph_root_adj (root f : J → V) (j : J) (hne : root j ≠ f j) :
    (spokeGraph root f).Adj (root j) (f j) := ⟨⟨j,rfl⟩,hne⟩

theorem spokeGraph_adj_outside (U : Finset V) (root f : J → V)
    (hout : ∀ j, root j ∉ U) (hin : ∀ j, f j ∈ U) {x y : V} (hx : x ∉ U) :
    (spokeGraph root f).Adj x y ↔ ∃ j, root j = x ∧ f j = y := by
  constructor
  · rintro ⟨⟨j,hj⟩,_⟩
    rcases Sym2.eq_iff.mp hj with h | h
    · exact ⟨j,h⟩
    · exact (hx (h.2 ▸ hin j)).elim
  · rintro ⟨j,rfl,rfl⟩
    exact spokeGraph_root_adj root f j (fun h => hout j (h ▸ hin j))

theorem spokeGraph_degree_outside (U : Finset V) (root f : J → V)
    (hout : ∀ j, root j ∉ U) (hin : ∀ j, f j ∈ U)
    (hinj : Function.Injective (fun j => s(root j,f j))) (v : V) (hv : v ∉ U) :
    (spokeGraph root f).degree v = Fintype.card {j // root j = v} := by
  let e : {j // root j = v} → (spokeGraph root f).neighborSet v := fun j =>
    ⟨f j.val,(spokeGraph_adj_outside U root f hout hin hv).mpr ⟨j.val,j.property,rfl⟩⟩
  have hei : Function.Injective e := by
    intro i j he
    apply Subtype.ext
    apply hinj
    have hf : f i.val = f j.val := congrArg Subtype.val he
    change s(root i.val,f i.val) = s(root j.val,f j.val)
    rw [i.property,j.property,hf]
  have hes : Function.Surjective e := by
    intro w
    obtain ⟨j,hj,hf⟩ := (spokeGraph_adj_outside U root f hout hin hv).mp w.property
    exact ⟨⟨j,hj⟩,Subtype.ext hf⟩
  have hc := Fintype.card_congr (Equiv.ofBijective e ⟨hei,hes⟩)
  rw [card_neighborSet_eq_degree] at hc
  exact hc.symm

/-- The internal graph is kept on the original ambient vertex type. -/
def insideGraph (H : SimpleGraph V) (U : Finset V) : SimpleGraph V where
  Adj x y := H.Adj x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

theorem insideGraph_le (H : SimpleGraph V) (U : Finset V) : insideGraph H U ≤ H :=
  fun _ _ h => h.1

def bankReserve (H : SimpleGraph V) (U : Finset V) (root f : J → V) : SimpleGraph V :=
  spokeGraph root f ⊔ insideGraph H U

theorem bankReserve_le (H : SimpleGraph V) (U : Finset V) (root f : J → V)
    (hadj : ∀ j, H.Adj (root j) (f j)) : bankReserve H U root f ≤ H :=
  sup_le (spokeGraph_le H root f hadj) (insideGraph_le H U)

theorem bankReserve_degree_outside (H : SimpleGraph V) (U : Finset V) (root f : J → V)
    (hout : ∀ j, root j ∉ U) (hin : ∀ j, f j ∈ U)
    (hinj : Function.Injective (fun j => s(root j,f j))) (v : V) (hv : v ∉ U) :
    (bankReserve H U root f).degree v = Fintype.card {j // root j = v} := by
  have hn : (bankReserve H U root f).neighborFinset v = (spokeGraph root f).neighborFinset v := by
    ext w
    rw [(bankReserve H U root f).mem_neighborFinset,(spokeGraph root f).mem_neighborFinset]
    change ((spokeGraph root f).Adj v w ∨ H.Adj v w ∧ v ∈ U ∧ w ∈ U) ↔ _
    simp only [hv,false_and,and_false,or_false]
  have hh : (bankReserve H U root f).degree v = (spokeGraph root f).degree v := by
    simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card hn
  exact hh.trans (spokeGraph_degree_outside U root f hout hin hinj v hv)

end
end Cycle12
