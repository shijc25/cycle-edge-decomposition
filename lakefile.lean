import Lake
open Lake DSL
package cycle12 where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxRecDepth, 10000⟩, ⟨`maxHeartbeats, 4000000⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI where
  roots := #[`OAI.Combinatorics.CycleDecomposition.Main]
  globs := #[`OAI.Combinatorics.CycleDecomposition.+]
lean_lib MengerHamilton
lean_lib LeanPool where
  leanOptions := #[⟨`maxHeartbeats, 4000000⟩]
lean_lib BergeLib where
  leanOptions := #[⟨`maxHeartbeats, 4000000⟩]
lean_lib GallaiEdmondsLib where
  leanOptions := #[⟨`maxHeartbeats, 4000000⟩]
lean_lib ARA where
  leanOptions := #[⟨`autoImplicit, true⟩, ⟨`maxHeartbeats, 4000000⟩]
lean_lib Euler where
  leanOptions := #[⟨`maxHeartbeats, 4000000⟩]
lean_lib HaxellLib
@[default_target] lean_lib Cycle12
