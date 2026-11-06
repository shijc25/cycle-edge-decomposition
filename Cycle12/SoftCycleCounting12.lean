import Cycle12.Foundations.SoftTrailClosure

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem disjoint_interiors_union_card (D : Finset V) (Z : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    (D∪univ.biUnion Z).card+(∑ i,(Z i∩D).card)=D.card+∑ i,(Z i).card := by
  have hZ : (univ.biUnion Z).card=∑ i,(Z i).card :=
    Finset.card_biUnion (fun i _ j _ hij => hd hij)
  have he : (univ.biUnion Z)∩D=univ.biUnion (fun i => Z i∩D) := by
    ext v
    simp only [mem_inter,mem_biUnion,mem_univ,true_and]
    tauto
  have hI : ((univ.biUnion Z)∩D).card=∑ i,(Z i∩D).card := by
    rw [he]
    exact Finset.card_biUnion (fun i _ j _ hij => (hd hij).mono inter_subset_left inter_subset_left)
  have hh := Finset.card_union_add_card_inter D (univ.biUnion Z)
  rw [Finset.inter_comm D,hI,hZ] at hh
  exact hh

/-- A lifted closed trail pays one cycle plus its actual soft collisions.
In particular there is no extra unit charge for each routing demand. -/
theorem soft_closed_trail_count {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsTrail) (D : Finset V) (Z : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hsupport : p.support.toFinset=D∪univ.biUnion Z)
    (hlength : p.length=D.card+∑ i,(Z i).card) :
    ∃ P : CyclePacking G, P.used=p.edgeSet ∧ P.count≤1+∑ i,(Z i∩D).card := by
  obtain ⟨P,hP,hcount⟩ := closed_trail_cycle_decomposition p hp
  have hcard := disjoint_interiors_union_card D Z hd
  rw [hsupport,hlength] at hcount
  exact ⟨P,hP,by omega⟩

end
end Cycle12
