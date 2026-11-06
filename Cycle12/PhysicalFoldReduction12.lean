import Cycle12.GlobalFoldCoefficient12
import Cycle12.PotentialInductionReduction12

namespace Cycle12.Global12
open Cycle12.Even12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The precise remaining graph construction. This is a proposition,
not an axiom and not a proved theorem. All graph partitions, completion
packings and their physical costs must still be constructed to prove it. -/
def PhysicalFoldConstruction12 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : EvenScaleLayers12 G)
    (i : ℕ) (_hi : i≤L.stopIndex) (F : ActualFoldStage12 L i),PotentialBelow n →
      ∃ T : CyclePacking G,
        let w := logScale (originalLog (Fin n)) L.stopIndex i
        T.weight≤(1+C*eta)*(∑ j : Fin (L.stopIndex+3) with j.val ≤ i+2, L.coreMass j.val)+
          sigma*L.coreMass i+(1/2048:ℝ)*L.coreMass i+
          (batchFee w+groupFee w)*F.activeMass+
          C*globalPhi (b*w)*(F.batchMass-kappa*F.activeMass)+(lossJ w+lossV w)*n

/-- The previously missing numerical fold payments are now discharged.
The unproved graph-construction premise remains explicit in the type. -/
theorem potential_fold_from_physical_construction (hphysical : PhysicalFoldConstruction12) :
    PotentialFoldBranch := by
  intro n G L ih hf
  obtain ⟨p,i,hi,_,hscale,hfold⟩ := L.active_fold_witness hf
  let F := Classical.choice (L.actual_fold_stage hi)
  obtain ⟨T,hT⟩ := hphysical n G L i hi F ih
  refine ⟨T,?_⟩
  have hh := actual_fold_ledger_payment L hi F p hscale hfold (cost:=T.weight)
    (by simpa only [Fintype.card_fin] using hT)
  simpa only [Fintype.card_fin] using hh

/-- A conditional dependency-chain endpoint. It must not be renamed
coefficient12 or accepted by the final checker while hphysical is unproved. -/
theorem coefficient12_from_physical_construction (hphysical : PhysicalFoldConstruction12) :
    Cycle12.Coefficient12Statement :=
  coefficient12_from_potential_fold (potential_fold_from_physical_construction hphysical)

end
end Cycle12.Global12
