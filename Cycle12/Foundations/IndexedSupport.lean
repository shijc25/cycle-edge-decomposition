import Cycle12.Foundations.HubProtection

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def indexedSupport (a b : I → V) : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ i, s(a i,b i)=s(x,y)
  symm := ⟨by rintro x y ⟨hne,i,hi⟩; exact ⟨hne.symm,i,hi.trans Sym2.eq_swap⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem indexedSupport_degree_le (a b : I → V) (v : V) :
    (indexedSupport a b).degree v ≤ Suppression.incidenceDegree a b v := by
  let H := indexedSupport a b
  let pick : H.neighborSet v → I := fun u => u.property.2.choose
  have hp : ∀ u : H.neighborSet v, s(a (pick u),b (pick u))=s(v,u.val) :=
    fun u => u.property.2.choose_spec
  have hpi : ∀ u : H.neighborSet v, a (pick u)=v ∨ b (pick u)=v := by
    intro u
    rcases Sym2.eq_iff.mp (hp u) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  let code : H.neighborSet v → {i // a i=v ∨ b i=v} := fun u => ⟨pick u,hpi u⟩
  have hinj : Function.Injective code := by
    intro x y h
    have he : pick x=pick y := congrArg Subtype.val h
    have hh : s(v,x.val)=s(v,y.val) := (hp x).symm.trans (he ▸ hp y)
    apply Subtype.ext
    rcases Sym2.eq_iff.mp hh with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hh := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_subtype] at hh
  have hN : (univ.filter (fun x => x∈H.neighborSet v))=H.neighborFinset v := by
    ext x
    simp
  rw [hN,card_neighborFinset_eq_degree] at hh
  simpa only [H,← ncard_neighborSet] using hh.trans (indexedIncident_card_le a b v)

end
end Cycle13
