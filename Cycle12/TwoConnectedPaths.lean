import Cycle12.VertexSeparator
import MengerHamilton.Menger

/-! A genuine two-path consequence of Menger for the circumference
classification, with the one-vertex deletion hypothesis discharged. -/
namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem two_disjoint_paths_of_vertex_robust (G : SimpleGraph V)
    (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (u v : V) (huv : u ≠ v) (hnonadj : ¬G.Adj u v) :
    ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧
      (∀ x∈p.support, x∈q.support → x=u ∨ x=v) := by
  obtain ⟨X,huX,hvX,hsep,paths,hpaths,hdisjoint⟩ :=
    Menger.exists_separator_and_paths_of_not_adj G huv hnonadj
  have htwo : 2 ≤ X.card := by
    by_contra hbad
    obtain ⟨r⟩ := hconn u v
    obtain ⟨x,hx,_⟩ := hsep r
    have hpos := Finset.card_pos.mpr (show X.Nonempty from ⟨x,hx⟩)
    have hone : X.card=1 := by omega
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hone
    have hua : u≠a := by simpa only [ha,Finset.mem_singleton] using huX
    have hva : v≠a := by simpa only [ha,Finset.mem_singleton] using hvX
    have hu : u∈({a}ᶜ : Set V) := hua
    have hv : v∈({a}ᶜ : Set V) := hva
    obtain ⟨q⟩ := hrobust a ⟨u,hu⟩ ⟨v,hv⟩
    let f := (SimpleGraph.Embedding.induce (G:=G) ({a}ᶜ : Set V)).toHom
    obtain ⟨z,hz,hzq⟩ := hsep (q.map f)
    have hza : z=a := by simpa only [ha,Finset.mem_singleton] using hz
    erw [Walk.support_map] at hzq
    obtain ⟨w,_,hw⟩ := List.mem_map.mp hzq
    have hwa : w.val ≠ a := w.property
    exact hwa ((show w.val=z from hw).trans hza)
  let i : Fin X.card := ⟨0,by omega⟩
  let j : Fin X.card := ⟨1,by omega⟩
  have hij : i≠j := by intro he; have hh := congrArg Fin.val he; norm_num [i,j] at hh
  exact ⟨paths i,paths j,hpaths i,hpaths j,hdisjoint i j hij⟩

end
end Cycle12
