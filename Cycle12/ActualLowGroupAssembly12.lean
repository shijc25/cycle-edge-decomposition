import Cycle12.ActualJointCoreRouting12
import Cycle12.ActualHighCenterBudget12
import Mathlib.GroupTheory.Perm.ViaEmbedding

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

abbrev CoreLowPairs (r : L.FoldCoreIndex i) :=
  (F.coreExternalPairs P r).low (F.coreCenterThreshold r)

def lowColor (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i) :
    (lowPathConflict (F.CoreLowPairs P r).left (F.CoreLowPairs P r).right
      (F.CoreLowPairs P r).center).Coloring
      (Fin (2*⌊routingAllowance (logScale (originalLog V) L.stopIndex i)⌋₊+
        ⌊F.coreCenterThreshold r/2⌋₊)) := Classical.choice (F.core_low_coloring hi P r)

abbrev LowGroup (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i) :=
  ColoredDemandGroups (F.lowColor P hi r) (routingTeamSize (logScale (originalLog V) L.stopIndex i))

abbrev lowGroup (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i) :
    (F.CoreLowPairs P r).Index → F.LowGroup P hi r :=
  coloredDemandGroup (F.lowColor P hi r) (routingTeamSize (logScale (originalLog V) L.stopIndex i))

theorem lowGroup_capacity (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i)
    (t : F.LowGroup P hi r) :
    teamLoad (F.lowGroup P hi r) t ≤ routingTeamSize (logScale (originalLog V) L.stopIndex i) :=
  colored_group_teamLoad (F.lowColor P hi r)
    (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1 t

def lowGroupPorts (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i)
    (t : F.LowGroup P hi r) : Finset V :=
  groupPorts (F.lowGroup P hi r) (F.CoreLowPairs P r).left (F.CoreLowPairs P r).right t

theorem lowGroupPorts_capacity (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i)
    (t : F.LowGroup P hi r) :
    (F.lowGroupPorts P hi r t).card ≤ 2*routingTeamSize (logScale (originalLog V) L.stopIndex i) :=
  (groupPorts_card _ _ _ _).trans (Nat.mul_le_mul_left 2 (F.lowGroup_capacity P hi r t))

theorem lowGroupPorts_subset (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i)
    (t : F.LowGroup P hi r) : F.lowGroupPorts P hi r t⊆(L.foldCorePiece i r).vertices := by
  intro v hv
  obtain ⟨j,hj,he|he⟩ := (mem_groupPorts _ _ _ _ _).mp hv
  · exact he ▸ (F.coreExternal_endpoints P r j.val).1
  · exact he ▸ (F.coreExternal_endpoints P r j.val).2

/-- All low pairs at a parent are embedded into the original aggregated
pair index. The owner equation rules out duplication between cores. -/
def lowPairEmbedding (z : L.FoldBoxIndex i) :
    (Σ r : Fin (L.foldCores i z).length,(F.CoreLowPairs P ⟨z,r⟩).Index) ↪ (F.boxPairs P z).Index where
  toFun j := j.2.val.val.val
  inj' := by
    rintro ⟨r,a⟩ ⟨t,b⟩ he
    have hr : (F.boxPairs P z).owner a.val.val.val=r := a.val.val.property
    have ht : (F.boxPairs P z).owner b.val.val.val=t := b.val.val.property
    have hrt : r=t := hr.symm.trans ((congrArg (F.boxPairs P z).owner he).trans ht)
    subst t
    have hab : a=b := Subtype.ext (Subtype.ext (Subtype.ext he))
    cases hab
    rfl

theorem lowPairEmbedding_owner (z : L.FoldBoxIndex i)
    (j : Σ r : Fin (L.foldCores i z).length,(F.CoreLowPairs P ⟨z,r⟩).Index) :
    (F.boxPairs P z).owner (F.lowPairEmbedding P z j)=j.1 := j.2.val.val.property

def lowPairNext (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i) :
    Equiv.Perm (Σ r : Fin (L.foldCores i z).length,(F.CoreLowPairs P ⟨z,r⟩).Index) :=
  Equiv.sigmaCongrRight (fun r => groupedCycleNext (F.lowGroup P hi ⟨z,r⟩))

/-- Rotate actual low groups and fix every high or internal pair.
Routing the enlarged family is harmless: only the low routes are used
for these closures, and all discarded auxiliary routes can remain unused. -/
def jointPairNext (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i) :
    Equiv.Perm (F.boxPairs P z).Index :=
  (F.lowPairNext P hi z).viaEmbedding (F.lowPairEmbedding P z)

theorem jointPairNext_on_low (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i)
    (r : Fin (L.foldCores i z).length) (j : (F.CoreLowPairs P ⟨z,r⟩).Index) :
    F.jointPairNext P hi z (F.lowPairEmbedding P z ⟨r,j⟩)=
      F.lowPairEmbedding P z ⟨r,groupedCycleNext (F.lowGroup P hi ⟨z,r⟩) j⟩ :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem jointPairNext_fixed (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.boxPairs P z).Index) (hj : j∉Set.range (F.lowPairEmbedding P z)) :
    F.jointPairNext P hi z j=j := Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hj

theorem jointPairNext_owner (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.boxPairs P z).Index) :
    (F.boxPairs P z).owner (F.jointPairNext P hi z j)=(F.boxPairs P z).owner j := by
  by_cases hj : j∈Set.range (F.lowPairEmbedding P z)
  · obtain ⟨⟨r,k⟩,rfl⟩ := hj
    rw [F.jointPairNext_on_low P hi z r k,F.lowPairEmbedding_owner,F.lowPairEmbedding_owner]
  · rw [F.jointPairNext_fixed P hi z j hj]

theorem lowGroup_count_with_high_centers (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i) :
    (Fintype.card (F.LowGroup P hi r):ℝ)+(F.coreHighCenters P r).card ≤
      (Fintype.card (F.CoreLowPairs P r).Index:ℝ)/
        routingTeamSize (logScale (originalLog V) L.stopIndex i)+
        (L.foldCorePiece i r).vertices.card/2048 := by
  have hQ := (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1
  have hcount := (F.coreExternalPairs P r).low_group_count
    (routingAllowance_pos _).le (show 0 ≤ F.coreCenterThreshold r from Nat.cast_nonneg _)
    (F.lowColor P hi r) hQ
  have hhigh := (F.core_high_palette_budget hi P r).2
  change (Fintype.card (F.LowGroup P hi r):ℝ) ≤ _ at hcount
  linarith only [hcount,hhigh]

theorem lowPairCount_le_all (z : L.FoldBoxIndex i) :
    (∑ r : Fin (L.foldCores i z).length,Fintype.card (F.CoreLowPairs P ⟨z,r⟩).Index) ≤
      Fintype.card (F.boxPairs P z).Index := by
  simpa only [Fintype.card_sigma] using
    Fintype.card_le_of_injective (F.lowPairEmbedding P z) (F.lowPairEmbedding P z).injective

end ActualFoldStage12
end
end Cycle12.Even12
