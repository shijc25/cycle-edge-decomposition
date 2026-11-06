import Cycle12.CoverRectangleClosure
import Cycle12.CoverAssembly.Full

namespace Cycle12
open SimpleGraph
noncomputable section

/-- The complete hard-case theorem follows from actual routed samples on a
kernel-checked cover of both continuous parameters. -/
theorem irreducible_cover : IrreducibleCoverTheorem :=
  irreducible_cover_of_rectangle CoverAssembly.Full.sound

/-- Actual circles and singleton edges for every finite simple graph, with
B=43/10, A=3 and the accepted cycle discount. -/
theorem mixed_cover {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    FineCover G 2 ∧ CoarseCover G 1 := cover_induction irreducible_cover G

end
end Cycle12
