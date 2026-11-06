import Cycle12.Foundations.ComponentObstruction
import Cycle12.Foundations.SplitRouting

/-! High degree at the pivot and bounded neighbour degrees force a perfect
or hypomatchable complement, by the proved DY obstruction. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem comap_degree_le {U : Type} [Fintype U] (G : SimpleGraph V) (f : U ↪ V) (u : U) :
    (G.comap f).degree u ≤ G.degree (f u) := by
  simp only [← ncard_neighborSet]
  rw [← Set.ncard_image_of_injective _ f.injective]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  rintro v ⟨x,hx,rfl⟩
  exact hx

theorem high_neighbor_complement_matchable (G : SimpleGraph V) (u : V) {D t : ℕ}
    (hno : ¬Nonempty (StrongCliqueImmersion t G)) (hu : D+t < G.degree u)
    (hnei : ∀ v, G.Adj u v → G.degree v ≤ D) :
    HasPerfectMatchingOn (G.induce (G.neighborSet u))ᶜ Set.univ ∨
      Hypomatchable (G.induce (G.neighborSet u))ᶜ := by
  let H := G.induce (G.neighborSet u)
  have hHno : ¬Nonempty (StrongCliqueImmersion t H) := by
    rintro ⟨M⟩
    let f : H.Copy G := {
      toHom := {
        toFun := Subtype.val
        map_rel' := fun h => h }
      injective' := Subtype.val_injective }
    exact hno ⟨M.mapCopy f⟩
  by_contra! hn
  obtain ⟨W,L,hW,hWt,hdis,hcard,hcomp,hfull⟩ := exists_DY_small_block H t hHno hn.1 hn.2
  obtain ⟨v,hv⟩ := hW
  have hc := hcomp v hv
  have hdeg : H.degree v ≤ D :=
    (comap_degree_le G (Function.Embedding.subtype (· ∈ G.neighborSet u)) v).trans
      (hnei v v.property)
  have hncard : Fintype.card (G.neighborSet u)=G.degree u := card_neighborSet_eq_degree G u
  have hcompl := H.degree_compl (v:=v)
  simp only [← ncard_neighborSet] at hc hdeg hu hncard hcompl
  omega

theorem exists_neighbor_matching_except (G : SimpleGraph V) (u : V) {D t : ℕ}
    (hno : ¬Nonempty (StrongCliqueImmersion t G)) (hu : D+t < G.degree u)
    (hnei : ∀ v, G.Adj u v → G.degree v ≤ D) (a : G.neighborSet u) :
    ∃ M : ((G.induce (G.neighborSet u))ᶜ).Subgraph,
      M.IsMatching ∧ ∀ b : G.neighborSet u, b≠a → b∈M.verts := by
  rcases high_neighbor_complement_matchable G u hno hu hnei with hp | hh
  · obtain ⟨M,hM,hcov⟩ := hp
    exact ⟨M,hM,fun b _ => by rw [hcov]; trivial⟩
  · obtain ⟨M,hM,hcov⟩ := hh a
    exact ⟨M,hM,fun b hb => by rw [hcov]; exact ⟨Set.mem_univ _,hb⟩⟩

end
end Cycle13
