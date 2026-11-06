import Cycle12.TerminalCertificateFast

namespace Cycle12
open SimpleGraph

/-- Pull the forbidden-cycle condition back along an injective graph map. -/
theorem noLongCycle_of_injective_hom {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    {T : ℕ} (hG : Cycle13.NoCycleAtLeast G T)
    (f : H →g G) (hf : Function.Injective f) : Cycle13.NoCycleAtLeast H T := by
  intro u p hp
  have hh := hG (f u) (p.map f) (hp.map hf)
  simpa only [Walk.length_map] using hh

/-- A finite word certificate excludes an injective copy in the actual graph. -/
theorem noLongCycle_excludes_word_embedding {V W : Type}
    {G : SimpleGraph V} {H : SimpleGraph W} {T : ℕ}
    (hG : Cycle13.NoCycleAtLeast G T) (f : H →g G) (hf : Function.Injective f)
    (c : CycleWord W) (hc : c.Valid H) (hlen : T≤c.tail.length+1) : False := by
  have hh := noLongCycle_of_injective_hom hG f hf c.root
    (c.toWalk H hc) (c.isCycle_toWalk H hc)
  rw [c.length_toWalk] at hh
  omega

theorem adj_of_sym2_eq {V W : Type} {G : SimpleGraph V} (f : W → V)
    {a b x y : W} (hab : G.Adj (f a) (f b)) (he : s(a,b)=s(x,y)) :
    G.Adj (f x) (f y) := by
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hab
  · exact hab.symm

end Cycle12
