import Cycle12.TerminalVertexGluing

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Failure of connectivity after deleting a vertex yields two strictly
smaller induced sides meeting at that vertex, with no cross edges. -/
theorem vertex_separator_sets (G : SimpleGraph V) (a : V)
    (hdisc : ¬(G.induce ({a}ᶜ : Set V)).Preconnected) :
    ∃ S T : Finset V, S∪T=Finset.univ ∧ S∩T={a} ∧
      S.card < Fintype.card V ∧ T.card < Fintype.card V ∧
      (∀ x∈S\T, ∀ y∈T\S, ¬G.Adj x y) := by
  let H := G.induce ({a}ᶜ : Set V)
  obtain ⟨u,v,huv⟩ : ∃ u v : ({a}ᶜ : Set V), ¬H.Reachable u v := by
    simpa only [SimpleGraph.Preconnected,not_forall] using hdisc
  let R : Finset V := Finset.univ.filter fun x =>
    ∃ hx : x∈({a}ᶜ : Set V), H.Reachable u ⟨x,hx⟩
  have hR : ∀ x, x∈R ↔ ∃ hx : x∈({a}ᶜ : Set V), H.Reachable u ⟨x,hx⟩ := by
    intro x
    simp only [R,Finset.mem_filter,Finset.mem_univ,true_and]
  have haR : a∉R := by simp [hR]
  have huR : u.val∈R := (hR _).mpr ⟨u.property,SimpleGraph.Reachable.refl _⟩
  have hvR : v.val∉R := by
    intro hv
    obtain ⟨hv,hr⟩ := (hR _).mp hv
    exact huv hr
  let S := insert a R
  let T := Rᶜ
  have hcover : S∪T=Finset.univ := by ext x; simp [S,T]
  have hinter : S∩T={a} := by ext x; simp [S,T]; aesop
  have hva : v.val≠a := v.property
  have hvS : v.val∉S := by simp [S,hvR,hva]
  have huT : u.val∉T := by simpa only [T,Finset.mem_compl,not_not] using huR
  have hsmallS : S.card < Fintype.card V := by
    have hp : S ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,fun he => hvS (he ▸ Finset.mem_univ _)⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hp
  have hsmallT : T.card < Fintype.card V := by
    have hp : T ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,fun he => huT (he ▸ Finset.mem_univ _)⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hp
  refine ⟨S,T,hcover,hinter,hsmallS,hsmallT,?_⟩
  intro x hx y hy hxy
  have hxR : x∈R := by
    have hh := (Finset.mem_sdiff.mp hx).2
    simpa only [T,Finset.mem_compl,not_not] using hh
  have hyR : y∉R := by
    have hh := (Finset.mem_sdiff.mp hy).1
    exact Finset.mem_compl.mp hh
  have hya : y≠a := by
    have hh := (Finset.mem_sdiff.mp hy).2
    simp only [S,Finset.mem_insert,not_or] at hh
    exact hh.1
  obtain ⟨hxmem,hr⟩ := (hR x).mp hxR
  have hymem : y∈({a}ᶜ : Set V) := hya
  have he : H.Adj ⟨x,hxmem⟩ ⟨y,hymem⟩ := hxy
  exact hyR ((hR y).mpr ⟨hymem,hr.trans he.reachable⟩)

/-- With at least three vertices, connectivity after every single-vertex
deletion already implies connectivity of the original graph. -/
theorem connected_of_all_vertex_deletions (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected) : G.Connected := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine ⟨?_⟩
  intro u v
  by_cases huv : u=v
  · subst v; exact SimpleGraph.Reachable.refl _
  have hR : (({u,v}:Finset V)ᶜ).Nonempty := by
    apply Finset.card_pos.mp
    have hh := Finset.card_add_card_compl ({u,v}:Finset V)
    rw [Finset.card_pair huv] at hh
    omega
  obtain ⟨a,ha⟩ := hR
  have hne : a≠u ∧ a≠v := by simpa only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or] using ha
  have hu : u∈({a}ᶜ : Set V) := hne.1.symm
  have hv : v∈({a}ᶜ : Set V) := hne.2.symm
  exact ((hrobust a) ⟨u,hu⟩ ⟨v,hv⟩).map (SimpleGraph.Embedding.induce (G:=G) ({a}ᶜ : Set V)).toHom

end
end Cycle12
