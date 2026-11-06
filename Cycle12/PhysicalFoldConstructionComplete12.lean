import Cycle12.ActualFoldTargetPayment12
import Cycle12.ActualFoldPrefixAssembly12
import Cycle12.PhysicalFoldReduction12

namespace Cycle12.Global12
open Cycle12.Even12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The remaining physical construction is supplied by the actual
four-family original-edge partition and the exact prefix replacement. -/
theorem physical_fold_construction12 : PhysicalFoldConstruction12 := by
  intro n G L i hi F ih
  have ih' : PotentialBelow (Fintype.card (Fin n)) := by simpa only [Fintype.card_fin] using ih
  obtain ⟨T,hT⟩ := F.actual_fold_target_payment hi ih'
  obtain ⟨R,hR⟩ := L.fold_prefix_assembly hi ih' T
  have hm := L.foldOther_mass i
  rw [L.fold_prefix_mass hi] at hm
  have hpay := congrArg (fun x : ℝ => (1+C*eta)*x) hm
  refine ⟨R,?_⟩
  dsimp only at hT ⊢
  simp only [Fintype.card_fin] at hT hR
  nlinarith only [hT,hR,hpay]

end
end Cycle12.Global12
