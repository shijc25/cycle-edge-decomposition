import Cycle12.MixedEndpointIncidence12
import Cycle12.CycleOutlinePortLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V J : Type} [Fintype V] [Fintype J] [DecidableEq V]
  {G : SimpleGraph V}

def outlineSwitchPort (c : CycleOutline G) (k : c.Switch × Bool) : V :=
  if k.2 then c.finish k.1 else c.start k.1

theorem outlineSwitchPort_project (c : CycleOutline G) (k : c.Switch × Bool) :
    c.project (outlineSwitchPort c k)=k.1.val := by
  rcases k with ⟨z,b⟩
  cases b
  · exact (c.projects z z.property.1).1
  · exact (c.projects z z.property.1).2

/-- A single quotient cycle has distinct original switch endpoints,
including both ports at every nontrivial switch. -/
theorem outlineSwitchPort_injective (c : CycleOutline G) :
    Function.Injective (outlineSwitchPort c) := by
  rintro ⟨z,b⟩ ⟨w,d⟩ he
  have hzw : z=w := by
    apply Subtype.ext
    exact (outlineSwitchPort_project c (z,b)).symm.trans
      ((congrArg c.project he).trans (outlineSwitchPort_project c (w,d)))
  subst w
  have hbd : b=d := by
    have hn := z.property.2
    cases b <;> cases d <;> simp_all [outlineSwitchPort,eq_comm]
  rw [hbd]

/-- Every switch port is incident to a concrete original representative
edge of this cycle, before any route is selected. -/
theorem outlineSwitchPort_original_neighbor (c : CycleOutline G) (k : c.Switch × Bool) :
    ∃ v,G.Adj (outlineSwitchPort c k) v ∧ s(outlineSwitchPort c k,v)∈c.edges := by
  rcases k with ⟨z,b⟩
  cases b
  · obtain ⟨d,hd,he⟩ := c.incoming z z.property.1
    have hp : c.start z=(c.rep d).snd := by rw [←he]; exact (c.ports d hd).2
    refine ⟨(c.rep d).fst,?_,?_⟩
    · change G.Adj (c.start z) (c.rep d).fst
      rw [hp]
      exact (c.rep d).adj.symm
    · change ∃ e∈c.cycle.darts,s(c.start z,(c.rep d).fst)=(c.rep e).edge
      refine ⟨d,hd,?_⟩
      rw [hp]
      exact Sym2.eq_swap
  · obtain ⟨d,hd,he⟩ := c.outgoing z z.property.1
    have hp : c.finish z=(c.rep d).fst := by rw [←he]; exact (c.ports d hd).1
    refine ⟨(c.rep d).snd,?_,?_⟩
    · change G.Adj (c.finish z) (c.rep d).snd
      rw [hp]
      exact (c.rep d).adj
    · change ∃ e∈c.cycle.darts,s(c.finish z,(c.rep d).snd)=(c.rep e).edge
      exact ⟨d,hd,by rw [hp]; rfl⟩

/-- The complete family of quotient switches, across all quotient cycles,
has an actual injection into original incidences. The degree bound may
therefore be taken in the whole descendant graph F. -/
theorem outline_family_original_incidences (F : SimpleGraph V) (c : J → CycleOutline G)
    (hsub : ∀ j,(c j).edges⊆F.edgeSet)
    (hd : Pairwise (fun j k => Disjoint (c j).edges (c k).edges)) :
    ∃ next : (Σ j,(c j).Switch × Bool) → V,
      (∀ k,F.Adj (outlineSwitchPort (c k.1) k.2) (next k) ∧
        s(outlineSwitchPort (c k.1) k.2,next k)∈(c k.1).edges) ∧
      Function.Injective (fun k => (outlineSwitchPort (c k.1) k.2,next k)) := by
  choose next hn using fun k : (Σ j,(c j).Switch × Bool) =>
    outlineSwitchPort_original_neighbor (c k.1) k.2
  refine ⟨next,?_,?_⟩
  · intro k
    exact ⟨hsub k.1 (hn k).2,(hn k).2⟩
  · apply mixed_incidence_injective (fun j => (c j).Switch × Bool)
      (fun j => (c j).edges) (fun k => outlineSwitchPort (c k.1) k.2) next
      (fun k => (hn k).2) hd
    intro j k l hkl
    exact outlineSwitchPort_injective (c j) (congrArg Prod.fst hkl)

end
end Cycle12
