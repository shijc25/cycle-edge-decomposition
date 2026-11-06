import Cycle12.TwoConnectedPaths

namespace Cycle12
open SimpleGraph Finset
variable {V : Type}

def fanApex (G : SimpleGraph V) (S : Finset V) : SimpleGraph (Option V) where
  Adj
    | none,none => False
    | none,some v => v∈S
    | some u,none => u∈S
    | some u,some v => G.Adj u v
  symm := ⟨by intro u v h; cases u <;> cases v <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro u h; cases u <;> simp_all⟩

def fanApexHom (G : SimpleGraph V) (S : Finset V) : G →g fanApex G S where
  toFun := some
  map_rel' := fun h => h

noncomputable section
attribute [local instance] Classical.propDecidable
variable [Fintype V] [DecidableEq V]

/-- The auxiliary apex has two internally disjoint paths from each vertex
outside S. A one-vertex separator is excluded using connectivity of G-a. -/
theorem fan_apex_two_paths (G : SimpleGraph V) (S : Finset V) (hS : 2 ≤ S.card)
    (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (x : V) (hx : x∉S) :
    ∃ p q : (fanApex G S).Walk (some x) none, p.IsPath ∧ q.IsPath ∧
      (∀ z∈p.support, z∈q.support → z=some x ∨ z=none) := by
  let H := fanApex G S
  have hnonadj : ¬H.Adj (some x) none := hx
  obtain ⟨X,hxX,hnX,hsep,paths,hpaths,hdisjoint⟩ :=
    Menger.exists_separator_and_paths_of_not_adj H (by simp) hnonadj
  have htwo : 2 ≤ X.card := by
    by_contra hbad
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0<S.card)
    obtain ⟨r⟩ := hconn x b
    have hbn : H.Adj (some b) none := hb
    obtain ⟨z,hz,_⟩ := hsep ((r.map (fanApexHom G S)).concat hbn)
    have hpos := Finset.card_pos.mpr (show X.Nonempty from ⟨z,hz⟩)
    have hone : X.card=1 := by omega
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hone
    cases a with
    | none => exact hnX (by simp [ha])
    | some a =>
      have hxa : x≠a := by simpa only [ha,Finset.mem_singleton,Option.some.injEq] using hxX
      obtain ⟨c,hc,hca⟩ := Finset.exists_mem_ne (by omega : 1<S.card) a
      have hxin : x∈({a}ᶜ : Set V) := hxa
      have hcin : c∈({a}ᶜ : Set V) := hca
      obtain ⟨q⟩ := hrobust a ⟨x,hxin⟩ ⟨c,hcin⟩
      let f := (fanApexHom G S).comp (SimpleGraph.Embedding.induce (G:=G) ({a}ᶜ : Set V)).toHom
      have hcn : H.Adj (some c) none := hc
      obtain ⟨z,hz,hzq⟩ := hsep ((q.map f).concat hcn)
      have hza : z=some a := by simpa only [ha,Finset.mem_singleton] using hz
      subst z
      erw [Walk.support_concat,Walk.support_map] at hzq
      rw [List.mem_append,List.mem_singleton] at hzq
      rcases hzq with hzq | hzq
      · obtain ⟨w,_,hw⟩ := List.mem_map.mp hzq
        have hwa : w.val≠a := w.property
        exact hwa (Option.some.inj hw)
      · cases hzq
  let i : Fin X.card := ⟨0,by omega⟩
  let j : Fin X.card := ⟨1,by omega⟩
  have hij : i≠j := by intro he; have hh := congrArg Fin.val he; norm_num [i,j] at hh
  exact ⟨paths i,paths j,hpaths i,hpaths j,hdisjoint i j hij⟩

end
end Cycle12
