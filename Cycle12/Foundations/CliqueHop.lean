import Cycle12.Foundations.DemandRouting

namespace Cycle13
open SimpleGraph
noncomputable section
variable {V : Type}

theorem exists_clique_hop (x y : V) :
    ∃ p : (completeGraph V).Walk x y,
      ∀ e, e∈p.edgeSet ↔ x≠y ∧ e=s(x,y) := by
  classical
  by_cases h : x=y
  · subst y
    exact ⟨.nil,by simp⟩
  · refine ⟨(show (completeGraph V).Adj x y from h).toWalk,?_⟩
    intro e
    simp only [Adj.toWalk,Walk.edgeSet_cons,Walk.edgeSet_nil,Set.mem_insert_iff,
      Set.mem_empty_iff_false,or_false,ne_eq,h,not_false_eq_true,true_and]

def cliqueHop (x y : V) : (completeGraph V).Walk x y :=
  Classical.choose (exists_clique_hop x y)

theorem cliqueHop_edge (x y : V) (e : Sym2 V) :
    e∈(cliqueHop x y).edgeSet ↔ x≠y ∧ e=s(x,y) :=
  Classical.choose_spec (exists_clique_hop x y) e

def hubWalk (a b z : V) : (completeGraph V).Walk a b :=
  (cliqueHop a z).append (cliqueHop z b)

theorem hubWalk_edge (a b z : V) (e : Sym2 V) :
    e∈(hubWalk a b z).edgeSet ↔
      ∃ x, (x=a ∨ x=b) ∧ x≠z ∧ e=s(x,z) := by
  rw [hubWalk,Walk.edgeSet_append]
  simp only [Set.mem_union,cliqueHop_edge]
  constructor
  · rintro (⟨ha,he⟩ | ⟨hb,he⟩)
    · exact ⟨a,Or.inl rfl,ha,he⟩
    · exact ⟨b,Or.inr rfl,hb.symm,he.trans Sym2.eq_swap⟩
  · rintro ⟨x,(rfl | rfl),hne,he⟩
    · exact Or.inl ⟨hne,he⟩
    · exact Or.inr ⟨hne.symm,he.trans Sym2.eq_swap⟩

end
end Cycle13
