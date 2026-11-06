import Cycle12.ReservoirReservedClosure12

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {A B V : Type} [Fintype A] [Fintype B]

/-- Match occurrences to pre-existing slots over the same vertex, with no
loss of injectivity. Different vertices may have different capacities. -/
theorem embedding_over_fibers (source : A → V) (root : B → V)
    (h : ∀ v, Fintype.card {a // source a = v} ≤ Fintype.card {b // root b = v}) :
    ∃ pick : A → B, Function.Injective pick ∧ ∀ a, root (pick a) = source a := by
  have he : ∀ v, Nonempty ({a // source a = v} ↪ {b // root b = v}) :=
    fun v => Function.Embedding.nonempty_of_card_le (h v)
  let e := fun v => Classical.choice (he v)
  let E : A ↪ B := (Equiv.sigmaFiberEquiv source).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl V) e).trans
      (Equiv.sigmaFiberEquiv root).toEmbedding)
  exact ⟨E,E.injective,fun a => (e (source a) ⟨a,rfl⟩).property⟩

def rootConflictGraph (root : A → V) : SimpleGraph A where
  Adj i j := i ≠ j ∧ root i = root j
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem rootConflictGraph_degree (root : A → V)
    (h : ∀ v, (univ.filter (fun i => root i = v)).card ≤ 2) (i : A) :
    (rootConflictGraph root).degree i ≤ 4 := by
  have hs : (rootConflictGraph root).neighborFinset i ⊆ univ.filter (fun j => root j = root i) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _,((rootConflictGraph root).mem_neighborFinset i j).mp hj |>.2.symm⟩
  have hh := (card_le_card hs).trans (h (root i))
  rw [card_neighborFinset_eq_degree] at hh
  omega

/-- Reserve one or two spokes per exterior root before the first pass.
The global representative load bound survives every subsequent restriction. -/
theorem choose_reserved_spokes [Fintype V] [Nonempty V]
    (H : SimpleGraph V) (U : Finset V) (root : A → V) {z upper : ℝ}
    (hU : ReservoirSample H U z upper) (hout : ∀ a, root a ∉ U)
    (hroot : ∀ v, (univ.filter (fun a => root a = v)).card ≤ 2)
    (hcard : Fintype.card A ≤ 2*Fintype.card V)
    (hz : 8192 ≤ z) (hzr : z ≤ (Fintype.card V:ℝ))
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) :
    ∃ f : A → V,
      (∀ a, f a ∈ U ∧ H.Adj (root a) (f a)) ∧
      Function.Injective (fun a => s(root a,f a)) ∧
      ∀ v, ((univ.filter (fun a => f a = v)).card:ℝ) ≤ z/64 := by
  obtain ⟨f,hf,_,hinj,hcap,hstrict⟩ := choose_reservoir_connectors H U root (rootConflictGraph root)
    hz hzr hsquare (by exact_mod_cast hcard) (rootConflictGraph_degree root hroot)
    (fun _ _ hij he => ⟨hij,he⟩) hout (fun a => hU.neighbors (root a))
  refine ⟨f,hf,hinj,fun v => ?_⟩
  exact (show ((univ.filter (fun a => f a = v)).card:ℝ) ≤ (⌈8*(Fintype.card V:ℝ)/z⌉₊:ℝ)
    by exact_mod_cast hcap v).trans hstrict.le

end
end Cycle12
