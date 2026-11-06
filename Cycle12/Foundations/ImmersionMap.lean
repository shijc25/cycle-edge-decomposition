import Cycle12.Foundations.ImmersionPaths

namespace Cycle13
open SimpleGraph
universe u v

namespace EdgeRouting
variable {V : Type u} {W : Type v} {H : SimpleGraph V} {G : SimpleGraph W}

def ofCopy (f : H.Copy G) : EdgeRouting H G where
  vertex := f.toEmbedding
  route h := (f.toHom.map_adj h).toWalk
  disjoint := by
    intro x y a b hxy hab hne
    apply Set.disjoint_left.mpr
    intro e he₁ he₂
    change e ∈ (f.toHom.map_adj hxy).toWalk.edgeSet at he₁
    change e ∈ (f.toHom.map_adj hab).toWalk.edgeSet at he₂
    have h₁ : e = s(f.toHom x, f.toHom y) := by simpa only [Adj.toWalk,
      Walk.edgeSet_cons, Walk.edgeSet_nil, Set.mem_insert_iff, Set.mem_empty_iff_false,
      or_false] using he₁
    have h₂ : e = s(f.toHom a, f.toHom b) := by simpa only [Adj.toWalk,
      Walk.edgeSet_cons, Walk.edgeSet_nil, Set.mem_insert_iff, Set.mem_empty_iff_false,
      or_false] using he₂
    apply hne
    exact Sym2.map.injective f.injective (h₁.symm.trans h₂)
  avoids := by
    intro x y hxy a ha
    change f.toHom a ∈ (f.toHom.map_adj hxy).toWalk.support at ha
    have h : f.toHom a = f.toHom x ∨ f.toHom a = f.toHom y := by simpa only [Adj.toWalk,
      Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] using ha
    exact h.imp (fun h => f.injective h) (fun h => f.injective h)

end EdgeRouting

namespace StrongCliqueImmersion
variable {V : Type u} {W : Type v} {H : SimpleGraph V} {G : SimpleGraph W} {t : ℕ}

noncomputable def mapCopy (M : StrongCliqueImmersion t H) (f : H.Copy G) :
    StrongCliqueImmersion t G := M.lift (EdgeRouting.ofCopy f)

@[simp] theorem mapCopy_branch (M : StrongCliqueImmersion t H) (f : H.Copy G) (i : Fin t) :
    (M.mapCopy f).branch i = f (M.branch i) := rfl

end StrongCliqueImmersion
end Cycle13
