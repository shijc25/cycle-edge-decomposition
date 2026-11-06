import Cycle12.Foundations.ImmersionPaths

namespace Cycle13
open SimpleGraph

instance (t : ℕ) : Fintype (CliquePair t) :=
  inferInstanceAs (Fintype {p : Fin t × Fin t // p.1 < p.2})

namespace CliquePair
variable {t : ℕ}

def edge (p : CliquePair t) : Sym2 (Fin t) := s(p.1.1, p.1.2)

theorem edge_injective : Function.Injective (edge (t := t)) := by
  intro p q h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · have hp := p.2
    have hq := q.2
    omega

theorem edge_mem (p : CliquePair t) : edge p ∈ (completeGraph (Fin t)).edgeSet :=
  ne_of_lt p.2

theorem edge_image_incident (i : Fin t) :
    edge '' {p : CliquePair t | i = p.1.1 ∨ i = p.1.2} =
      (completeGraph (Fin t)).incidenceSet i := by
  ext e
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨edge_mem p, Sym2.mem_iff.mpr hp⟩
  · rintro ⟨he, hi⟩
    obtain ⟨j, rfl⟩ := Sym2.mem_iff_exists.mp hi
    have hij : i ≠ j := he
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨⟨(i,j), hij⟩, Or.inl rfl, rfl⟩
    · exact ⟨⟨(j,i), hji⟩, Or.inr rfl, Sym2.eq_swap⟩

theorem ncard_incident (i : Fin t) :
    {p : CliquePair t | i = p.1.1 ∨ i = p.1.2}.ncard = t - 1 := by
  classical
  rw [← Set.ncard_image_of_injective _ edge_injective, edge_image_incident,
    SimpleGraph.ncard_incidenceSet, SimpleGraph.complete_graph_degree, Fintype.card_fin]

end CliquePair
end Cycle13
