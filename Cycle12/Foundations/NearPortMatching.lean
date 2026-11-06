import Cycle12.Foundations.NearSuppression

/-! Near-perfect clone matchings yield actual external port matchings.
Even total degree forces an available internal port for the unmatched external one. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace ClonePortMatching
variable {I V U : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph U) (v : V ↪ U) (D : Finset V) (E : (V ⊕ D) ↪ I)
    (M : (cloneGraph (H.comap v) D)ᶜ.Subgraph) (a : V ⊕ D)
    (hcover : M.verts=Set.univ \ {a})
include hcover

theorem ported_omitted : E a∉(ported H v D E M).verts := by
  rintro ⟨b,hb,he⟩
  have hab : b=a := E.injective he
  simpa [hcover,hab] using hb

theorem ported_near_covered {i : I} (hi : ∃ b, E b=i) (hne : i≠E a) :
    i∈(ported H v D E M).verts := by
  obtain ⟨b,rfl⟩ := hi
  refine ⟨b,?_,rfl⟩
  rw [hcover]
  exact ⟨Set.mem_univ _,fun h => hne (congrArg E h)⟩

end ClonePortMatching

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)

theorem exists_internal_port_of_near_matching (S : Set {v : V // v≠z})
    (M : (⊤ : SimpleGraph (R.Ports z)).Subgraph) (hM : M.IsMatching)
    (a : R.Ports z) (ha : a∉M.verts)
    (hcover : ∀ i, R.portTip z i∈S → i≠a → i∈M.verts)
    (heven : Even (R.degree z)) : ∃ b : R.Ports z, R.portTip z b∉S := by
  obtain ⟨N,hN,hNv,hMN,_,_⟩ := R.exists_suppressed_prescribed z M hM heven
  obtain ⟨b,hab,_⟩ := hN (show a∈N.verts by rw [hNv]; trivial)
  refine ⟨b,?_⟩
  intro hb
  have hbm := hcover b hb hab.ne.symm
  have hm : M.Adj b a := (matching_extension_adj hM hN hMN hbm).mp hab.symm
  exact ha hm.snd_mem

variable [Fintype V]

theorem near_port_matching_of_clone_near (S X : Set {v : V // v≠z})
    (hXS : X⊆S) (hports : ∀ i, R.portTip z i∈S → R.portTip z i∈X)
    (hpos : ∀ x : X, 0<R.multiplicity z x.val.val)
    (hmax : ∀ x : X, R.multiplicity z x.val.val≤2) (x : X)
    (hnear : ∃ M : (cloneGraph (R.externalGraph z X) (R.doubleExternal z X))ᶜ.Subgraph,
      M.IsMatching ∧ M.verts=Set.univ \ {Sum.inl x}) :
    ∃ P : (⊤ : SimpleGraph (R.Ports z)).Subgraph, ∃ a : R.Ports z,
      P.IsMatching ∧ R.portTip z a=x.val ∧ a∉P.verts ∧
      (∀ i, R.portTip z i∈S → i≠a → i∈P.verts) ∧
      (∀ i j, P.Adj i j → R.portTip z i∈S ∧ R.portTip z j∈S) ∧
      (∀ i j, P.Adj i j → R.portTip z i≠R.portTip z j) ∧
      Set.InjOn (Sym2.map (R.portTip z)) P.edgeSet ∧
      (∀ i j, P.Adj i j → R.multiplicity (R.portTip z i).val (R.portTip z j).val=0) := by
  obtain ⟨E,hE,hErange⟩ := R.exists_clone_port_embedding z X hpos hmax
  obtain ⟨M,hM,hMcover⟩ := hnear
  let H := R.graph.comap (Subtype.val : {v : V // v≠z} → V)
  let v : X ↪ {v : V // v≠z} := Function.Embedding.subtype X
  let D := R.doubleExternal z X
  let P := ClonePortMatching.ported H v D E M
  have hP : P.IsMatching := ClonePortMatching.ported_matching H v D E M hM
  have hPl : ∀ i j, P.Adj i j → R.portTip z i≠R.portTip z j := by
    intro i j hij
    exact ClonePortMatching.ported_no_loop H v D E (R.portTip z) hE M hij
  refine ⟨P,E (Sum.inl x),hP,hE (Sum.inl x),
    ClonePortMatching.ported_omitted H v D E M (Sum.inl x) hMcover,?_,?_,hPl,
    ClonePortMatching.ported_output_injective H v D E (R.portTip z) hE M hM,?_⟩
  · intro i hi hne
    exact ClonePortMatching.ported_near_covered H v D E M (Sum.inl x) hMcover
      (hErange i (hports i hi)) hne
  · intro i j hij
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := ClonePortMatching.ported_ends H v D E (R.portTip z) hE M hij
    exact ⟨hXS (ha ▸ a.property),hXS (hb ▸ b.property)⟩
  · intro i j hij
    have hn := ClonePortMatching.ported_not_adj H v D E (R.portTip z) hE M hij
    have hne : (R.portTip z i).val≠(R.portTip z j).val := fun h => hPl i j hij (Subtype.ext h)
    change ¬R.graph.Adj (R.portTip z i).val (R.portTip z j).val at hn
    rw [graph_adj_iff_multiplicity] at hn
    have hz : ¬0<R.multiplicity (R.portTip z i).val (R.portTip z j).val := fun h => hn ⟨hne,h⟩
    omega

theorem near_suppression_of_clone_near (S X : Set {v : V // v≠z})
    (hXS : X⊆S) (hports : ∀ i, R.portTip z i∈S → R.portTip z i∈X)
    (hpos : ∀ x : X, 0<R.multiplicity z x.val.val)
    (hmax : ∀ x : X, R.multiplicity z x.val.val≤2) (x : X)
    (heven : Even (R.degree z)) (hold : R.SimpleOn (Subtype.val '' S))
    (hnear : ∃ M : (cloneGraph (R.externalGraph z X) (R.doubleExternal z X))ᶜ.Subgraph,
      M.IsMatching ∧ M.verts=Set.univ \ {Sum.inl x}) :
    ∃ b : R.Ports z, R.portTip z b∉S ∧
      ∃ N : (⊤ : SimpleGraph (R.Ports z)).Subgraph, ∃ hN : N.IsMatching,
        N.verts=Set.univ ∧ (R.suppress z N hN).SimpleOn S ∧
        (∀ u v, u∈S → v∉S → (R.suppress z N hN).multiplicity u v=
          R.multiplicity u.val v.val+(if s(x.val,R.portTip z b)=s(u,v) then 1 else 0)) ∧
        (∀ v, (R.suppress z N hN).degree v=R.degree v.val) := by
  obtain ⟨M,a,hM,hatip,ha,hcov,hends,hloop,hi,habsent⟩ :=
    R.near_port_matching_of_clone_near z S X hXS hports hpos hmax x hnear
  obtain ⟨b,hb⟩ := R.exists_internal_port_of_near_matching z S M hM a ha hcov heven
  obtain ⟨N,hN,hNv,_,hNs,hcross,hdeg⟩ := R.exists_near_controlled_suppression z S M hM a b
    (hatip ▸ hXS x.property) hb ha hcov hends hloop hi habsent heven hold
  refine ⟨b,hb,N,hN,hNv,hNs,?_,hdeg⟩
  simpa only [hatip] using hcross

end RoutedEdges
end
end Cycle13
