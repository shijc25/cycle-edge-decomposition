import Cycle12.RoutingArithmetic
import Cycle12.InducedExpansion
import Cycle12.VertexDeletion
import Cycle12.Foundations.ShortPathFan

namespace Cycle12
open SimpleGraph Finset Real Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

set_option backward.isDefEq.respectTransparency.types false in
theorem routing_short_path_avoiding {G : SimpleGraph V} {S W X : Finset V}
    {u v : V} {n h a z t R γ L : ℝ}
    (hh : 0 < h) (hr : 0 < routingRetained a R γ) (hL : 1/32 < L)
    (hcoef : 8/routingRetained a R γ < (L-1/32)^2)
    (hnh : 4096 ≤ n/h) (hn : (Fintype.card V:ℝ) ≤ n)
    (hretain : 1-z-t=1-a) (hexp : CutExpandsOn G S ((1-z)*h))
    (hu : u ∈ S) (hv : v ∈ S)
    (huW : u ∉ W) (hvW : v ∉ W) (huX : u ∉ X) (hvX : v ∉ X)
    (hW : (W.card:ℝ) ≤ (t+1/128)*h) (hX : (X.card:ℝ) ≤ h/(R*γ)) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ routingLength n h L ∧
      (∀ w ∈ p.support, w ∈ S) ∧
      Disjoint (routeInterior p) W ∧ Disjoint (routeInterior p) X := by
  have hcard : ((W∪X).card:ℝ) ≤ (W.card:ℝ)+X.card := by
    exact_mod_cast Finset.card_union_le W X
  have hdel : ((S\(S\(W∪X))).card:ℝ) ≤ (W∪X).card := by
    have hs : S\(S\(W∪X)) ⊆ W∪X := by
      intro w hw
      simp only [Finset.mem_sdiff] at hw
      by_contra hnot
      exact hw.2 ⟨hw.1,hnot⟩
    exact_mod_cast Finset.card_le_card hs
  have heq : routingRetained a R γ*h=(1-z)*h-(t+1/128)*h-h/(R*γ) := by
    unfold routingRetained
    linear_combination -h*hretain
  have hlower : routingRetained a R γ*h ≤ (1-z)*h-(S\(S\(W∪X))).card := by
    linarith only [hcard,hdel,hW,hX,heq]
  have hx := cutExpandsOn_mono_parameter
    (cutExpandsOn_delete_vertices hexp (Finset.sdiff_subset : S\(W∪X) ⊆ S)) hlower
  have hus : u ∈ S\(W∪X) := by simp [hu,huW,huX]
  have hvs : v ∈ S\(W∪X) := by simp [hv,hvW,hvX]
  obtain ⟨p,hp,hsupport,hlen⟩ := expanding_induced_short_path (mul_pos hr hh) hx u v hus hvs
  have hNV : ((S\(W∪X)).card:ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ (S\(W∪X))
  refine ⟨p,hp,routing_natural_length_bound hh hr hL hcoef (hNV.trans hn) hnh hlen,?_,?_,?_⟩
  · intro w hw
    exact (Finset.mem_sdiff.mp (hsupport w hw)).1
  · rw [Finset.disjoint_left]
    intro w hw hWw
    exact (Finset.mem_sdiff.mp (hsupport w ((mem_routeInterior_iff p w).mp hw).1)).2
      (Finset.mem_union_left _ hWw)
  · rw [Finset.disjoint_left]
    intro w hw hXw
    exact (Finset.mem_sdiff.mp (hsupport w ((mem_routeInterior_iff p w).mp hw).1)).2
      (Finset.mem_union_right _ hXw)

/-- A complete candidate construction, including an actual short path fan.
The endpoint pair may coincide; no hidden distinctness assumption is needed. -/
theorem routing_weighted_candidate {G : SimpleGraph V} {S W : Finset V}
    {u v : V} {n h a z t R γ L : ℝ}
    (hh : 0 < h) (hR : 0 < R) (hγ : 0 < γ)
    (hr : 0 < routingRetained a R γ) (hL : 1/32 < L)
    (hcoef : 8/routingRetained a R γ < (L-1/32)^2)
    (hnh : 4096 ≤ n/h) (hn : (Fintype.card V:ℝ) ≤ n)
    (hretain : 1-z-t=1-a) (hexp : CutExpandsOn G S ((1-z)*h))
    (hu : u ∈ S) (hv : v ∈ S) (huW : u ∉ W) (hvW : v ∉ W)
    (hW : (W.card:ℝ) ≤ (t+1/128)*h) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ routingLength n h L ∧
      (∀ v ∈ p.support, v ∈ S) ∧ Disjoint (routeInterior p) W ∧
      (∑ v ∈ routeInterior p, w v) ≤
        (R*γ*routingLength n h L/h)*∑ v,w v := by
  let ell := routingLength n h L
  have hell : 0 < ell := routing_length_pos hL hnh
  have hellR : (0:ℝ) < ell := by exact_mod_cast hell
  let K : ℕ := ⌊h/(R*γ*ell)⌋₊
  let Good : G.Walk u v → Prop := fun p =>
    (∀ v ∈ p.support, v ∈ S) ∧ Disjoint (routeInterior p) W
  have hfloor : (K:ℝ) ≤ h/(R*γ*ell) := Nat.floor_le (by positivity)
  have hK : (K:ℝ)*(R*γ*ell) ≤ h := (le_div_iff₀ (by positivity)).mp hfloor
  have hpath : ∀ X : Finset V, X.card ≤ K*ell → u ∉ X → v ∉ X →
      ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ ell ∧ Good p ∧
        Disjoint (routeInterior p) X := by
    intro X hX huX hvX
    have hXR : (X.card:ℝ) ≤ (K:ℝ)*ell := by exact_mod_cast hX
    have hXbound : (X.card:ℝ) ≤ h/(R*γ) := by
      apply (le_div_iff₀ (mul_pos hR hγ)).mpr
      have hm := mul_le_mul_of_nonneg_right hXR (mul_nonneg hR.le hγ.le)
      nlinarith only [hK,hm]
    obtain ⟨p,hp,hlen,hs,hW',hX'⟩ := routing_short_path_avoiding hh hr hL hcoef hnh hn
      hretain hexp hu hv huW hvW huX hvX hW hXbound
    exact ⟨p,hp,hlen,⟨hs,hW'⟩,hX'⟩
  obtain ⟨P⟩ := exists_short_path_fan Good hpath
  obtain ⟨i,hi⟩ := P.exists_weight_le_average (by omega : 0 < K+1) w hw
  have hKlt : h/(R*γ*ell) < (K:ℝ)+1 := Nat.lt_floor_add_one _
  have hKn : (0:ℝ) < (K:ℝ)+1 := by positivity
  have hpay : (1:ℝ)/((K:ℝ)+1) ≤ R*γ*ell/h := by
    apply (div_le_div_iff₀ hKn hh).mpr
    have hx := (div_lt_iff₀ (by positivity : (0:ℝ) < R*γ*ell)).mp hKlt
    nlinarith only [hx]
  have hsum : 0 ≤ ∑ v,w v := Finset.sum_nonneg (fun v _ => hw v)
  have htotal := mul_le_mul_of_nonneg_right hpay hsum
  refine ⟨P.path i,P.simple i,P.length_le i,(P.good i).1,(P.good i).2,?_⟩
  push_cast at hi
  have htotal' : (∑ v,w v)/((K:ℝ)+1) ≤ (R*γ*ell/h)*∑ v,w v := by
    convert htotal using 1 <;> ring
  exact hi.trans htotal'

end
end Cycle12
