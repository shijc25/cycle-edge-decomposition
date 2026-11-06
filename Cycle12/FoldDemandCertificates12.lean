import Cycle12.JointEndpointCertificate12
import Cycle12.LowDemandIncidence12
import Cycle12.MatchingDemandIncidence12
import Cycle12.OutlineEndpointIncidence12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq I]

/-- Actual low-path requests supply the certificate used in the joint
router, after every color group has been cyclically reconnected. -/
theorem low_path_endpoint_certificate (F : SimpleGraph V) (a b z : I → V)
    (ha : ∀ i,F.Adj (z i) (a i)) (hb : ∀ i,F.Adj (z i) (b i))
    (hne : ∀ i,a i ≠ b i)
    (hd : Pairwise (fun i j => Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet
      (twoEdgeWalk (ha j) (hb j)).edgeSet)) (next : Equiv.Perm I) :
    Nonempty (OriginalEndpointCertificate F b (a ∘ next)
      (⋃ i,(twoEdgeWalk (ha i) (hb i)).edgeSet)) := by
  obtain ⟨neighbor,hm,hi⟩ := low_demands_original_incidences F a b z ha hb hne hd next
  exact ⟨⟨neighbor,fun k => (hm k).1,fun k => (hm k).2,hi⟩⟩

def matchingDemandSource (a b : I → V) (M : (⊤ : SimpleGraph I).Subgraph) :
    M.edgeSet ⊕ M.edgeSet → V := Sum.elim (fun e => a e.val.out.2) (fun e => b e.val.out.1)
def matchingDemandTarget (a b : I → V) (M : (⊤ : SimpleGraph I).Subgraph)
    (next : Equiv.Perm M.edgeSet) : M.edgeSet ⊕ M.edgeSet → V :=
  Sum.elim (fun e => a (next e).val.out.1) (fun e => b e.val.out.2)

theorem matching_demand_port_identity (a b : I → V) (M : (⊤ : SimpleGraph I).Subgraph)
    (next : Equiv.Perm M.edgeSet) (k : (M.edgeSet ⊕ M.edgeSet) × Bool) :
    (if k.2 then matchingDemandTarget a b M next k.1 else matchingDemandSource a b M k.1)=
      (if (matchingDemandPick M next k).2 then b (matchingDemandPick M next k).1
        else a (matchingDemandPick M next k).1) := by
  rcases k with ⟨e,d⟩
  cases e <;> cases d <;> rfl

/-- Both sides of the alternating matching closure are certified together;
the retained unmatched edge is not charged to these requests. -/
theorem matching_endpoint_certificate (F : SimpleGraph V) (a b : I → V)
    (ha : ∀ i,F.Adj (a i) (b i)) (hedge : Function.Injective (fun i => s(a i,b i)))
    (M : (⊤ : SimpleGraph I).Subgraph) (hM : M.IsMatching)
    (next : Equiv.Perm M.edgeSet) (S : Set (Sym2 V))
    (hS : ∀ i,i∈M.verts → s(a i,b i)∈S) :
    Nonempty (OriginalEndpointCertificate F (matchingDemandSource a b M)
      (matchingDemandTarget a b M next) S) := by
  obtain ⟨neighbor,hm,hi⟩ := matching_demands_class_incidences F a b ha hedge M hM next S hS
  refine ⟨⟨neighbor,?_,?_,?_⟩⟩
  · intro k
    rw [matching_demand_port_identity]
    exact (hm k).1
  · intro k
    rw [matching_demand_port_identity]
    exact (hm k).2
  · simpa only [matching_demand_port_identity] using hi

/-- All actual representative quotient cycles, before routing, provide
the third edge-disjoint request class for the joint certificate. -/
theorem quotient_endpoint_certificate (F G : SimpleGraph V) (c : J → CycleOutline G)
    (hsub : ∀ j,(c j).edges⊆F.edgeSet)
    (hd : Pairwise (fun j k => Disjoint (c j).edges (c k).edges)) :
    Nonempty (OriginalEndpointCertificate F
      (fun k : Σ j,(c j).Switch => (c k.1).start k.2)
      (fun k : Σ j,(c j).Switch => (c k.1).finish k.2) (⋃ j,(c j).edges)) := by
  obtain ⟨next,hm,hi⟩ := outline_family_original_incidences F c hsub hd
  let pick : (Σ j,(c j).Switch) × Bool → Σ j,(c j).Switch × Bool :=
    fun k => ⟨k.1.1,(k.1.2,k.2)⟩
  have hp : Function.Injective pick := by
    let unpick : (Σ j,(c j).Switch × Bool) → (Σ j,(c j).Switch) × Bool :=
      fun k => (⟨k.1,k.2.1⟩,k.2.2)
    have hh : Function.LeftInverse unpick pick := fun k => rfl
    exact hh.injective
  refine ⟨⟨next ∘ pick,?_,?_,?_⟩⟩
  · intro k
    exact (hm (pick k)).1
  · intro k
    exact Set.mem_iUnion.mpr ⟨k.1.1,(hm (pick k)).2⟩
  · exact hi.comp hp

end
end Cycle12
