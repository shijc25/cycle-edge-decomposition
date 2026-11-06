import Cycle12.Foundations.ClonePorts

/-! Transport a clone-complement matching to the actual port indices.
Output edge uniqueness and absence are preserved under this transport. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ClonePortMatching
variable {I V U : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph U) (v : V ↪ U) (D : Finset V) (E : (V ⊕ D) ↪ I)

def hom : (cloneGraph (H.comap v) D)ᶜ →g (⊤ : SimpleGraph I) where
  toFun := E
  map_rel' := by intro a b hab; exact E.injective.ne hab.ne

def ported (M : (cloneGraph (H.comap v) D)ᶜ.Subgraph) : (⊤ : SimpleGraph I).Subgraph :=
  M.map (hom H v D E)

theorem ported_matching (M : (cloneGraph (H.comap v) D)ᶜ.Subgraph) (hM : M.IsMatching) :
    (ported H v D E M).IsMatching :=
  hM.map (hom H v D E) E.injective

theorem ported_covered (M : (cloneGraph (H.comap v) D)ᶜ.Subgraph)
    (hcover : M.verts=Set.univ) {i : I} (hi : ∃ a, E a=i) : i∈(ported H v D E M).verts := by
  obtain ⟨a,rfl⟩ := hi
  exact ⟨a,by rw [hcover]; trivial,rfl⟩

variable (o : I → U) (hE : ∀ a, o (E a)=v (cloneOrigin D a))
    (M : (cloneGraph (H.comap v) D)ᶜ.Subgraph)
include hE

theorem ported_no_loop {i j : I} (h : (ported H v D E M).Adj i j) : o i≠o j := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := h
  change o (E a)≠o (E b)
  rw [hE,hE]
  exact v.injective.ne (CloneMatching.origin_ne_of_adj (M.adj_sub hab))

theorem ported_not_adj {i j : I} (h : (ported H v D E M).Adj i j) : ¬H.Adj (o i) (o j) := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := h
  change ¬H.Adj (o (E a)) (o (E b))
  rw [hE,hE]
  exact CloneMatching.not_adj_of_adj (M.adj_sub hab)

theorem ported_ends {i j : I} (h : (ported H v D E M).Adj i j) :
    o i∈Set.range v ∧ o j∈Set.range v := by
  obtain ⟨a,b,hab,rfl,rfl⟩ := h
  exact ⟨⟨cloneOrigin D a,(hE a).symm⟩,⟨cloneOrigin D b,(hE b).symm⟩⟩

theorem ported_output_injective (hM : M.IsMatching) :
    Set.InjOn (Sym2.map o) (ported H v D E M).edgeSet := by
  intro e he f hf hef
  induction e using Sym2.ind with
  | h i j =>
    induction f using Sym2.ind with
    | h k l =>
      change (ported H v D E M).Adj i j at he
      change (ported H v D E M).Adj k l at hf
      obtain ⟨a,b,hab,rfl,rfl⟩ := he
      obtain ⟨c,d,hcd,rfl,rfl⟩ := hf
      change s(o (E a),o (E b))=s(o (E c),o (E d)) at hef
      have ho : Sym2.map (cloneOrigin D) s(a,b)=Sym2.map (cloneOrigin D) s(c,d) := by
        apply Sym2.map.injective v.injective
        simpa only [Sym2.map_mk,hE] using hef
      have hp := CloneMatching.output_edge_injective M hM hab hcd ho
      exact congrArg (Sym2.map E) hp

end ClonePortMatching
end
end Cycle13
