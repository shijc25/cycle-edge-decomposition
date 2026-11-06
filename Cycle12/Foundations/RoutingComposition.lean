import Cycle12.Foundations.ImmersionMap

/-! Composition of actual strong edge routings. -/
namespace Cycle13.EdgeRouting
open SimpleGraph
universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
    {K : SimpleGraph U} {H : SimpleGraph V} {G : SimpleGraph W}

def compose (R : EdgeRouting H G) (S : EdgeRouting K H) : EdgeRouting K G where
  vertex := S.vertex.trans R.vertex
  route h := R.liftWalk (S.route h)
  disjoint h k hne := R.liftWalk_disjoint _ _ (S.disjoint h k hne)
  avoids h a ha := S.avoids h a (R.liftWalk_support (S.route h) (S.vertex a) ha)

def identity (G : SimpleGraph V) : EdgeRouting G G :=
  ofCopy {
    toHom := {
      toFun := id
      map_rel' := fun h => h }
    injective' := Function.injective_id }

end Cycle13.EdgeRouting
