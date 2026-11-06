import Cycle12.Foundations.ExpanderPaths
import Cycle12.Foundations.H128Arithmetic
import Cycle12.Foundations.ShortPathFan

namespace Cycle13
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem h128_short_path_avoiding {G : SimpleGraph V} {S W X : Finset V}
    {a b : V} {r h : ℝ} (hh : 0 < h) (hrh : 4 ≤ r/h)
    (hr : (Fintype.card V:ℝ) ≤ r)
    (hexp : ExpansionWithin G S ((6/11)*h)) (ha : a ∈ S) (hb : b ∈ S)
    (haW : a ∉ W) (hbW : b ∉ W) (haX : a ∉ X) (hbX : b ∉ X)
    (hW : (W.card:ℝ) ≤ (1/5+1/128)*h) (hX : (X.card:ℝ) ≤ h/16) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ h128Length r h ∧
      (∀ v ∈ p.support, v ∈ S) ∧
      Disjoint (routeInterior p) W ∧ Disjoint (routeInterior p) X := by
  have hcard : ((W∪X).card:ℝ) ≤ (W.card:ℝ)+X.card := by exact_mod_cast Finset.card_union_le W X
  have hlower : h128RetainedFraction*h ≤ (6/11)*h-(W∪X).card := by
    unfold h128RetainedFraction
    linarith
  have hx := (hexp.delete_vertices (W∪X)).mono hlower
  have has : a ∈ S\(W∪X) := by simp [ha,haW,haX]
  have hbs : b ∈ S\(W∪X) := by simp [hb,hbW,hbX]
  obtain ⟨p,hp,hsupport,hlen⟩ := hx.short_path (mul_pos h128RetainedFraction_pos hh) has hbs
  have hNV : ((S\(W∪X)).card:ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ (S\(W∪X))
  have hN : ((S\(W∪X)).card:ℝ) ≤ r := hNV.trans hr
  refine ⟨p,hp,h128_natural_length_bound hh hN hrh hlen,?_,?_,?_⟩
  · intro v hv
    exact (Finset.mem_sdiff.mp (hsupport v hv)).1
  · rw [Finset.disjoint_left]
    intro v hv hWv
    have hs := hsupport v ((mem_routeInterior_iff p v).mp hv).1
    exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_union_left _ hWv)
  · rw [Finset.disjoint_left]
    intro v hv hXv
    have hs := hsupport v ((mem_routeInterior_iff p v).mp hv).1
    exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_union_right _ hXv)

/-- Construct a candidate with the required soft-intersection payment.
The fan is built in the actual graph by repeated vertex deletions, and
the average bound counts each interior vertex at most once. -/
theorem h128_weighted_candidate {G : SimpleGraph V} {S W : Finset V}
    {a b : V} {r h : ℝ} (hh : 0 < h) (hrh : 4 ≤ r/h)
    (hr : (Fintype.card V:ℝ) ≤ r)
    (hexp : ExpansionWithin G S ((6/11)*h)) (ha : a ∈ S) (hb : b ∈ S)
    (haW : a ∉ W) (hbW : b ∉ W)
    (hW : (W.card:ℝ) ≤ (1/5+1/128)*h) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ h128Length r h ∧
      (∀ v ∈ p.support, v ∈ S) ∧ Disjoint (routeInterior p) W ∧
      (∑ v ∈ routeInterior p, w v) ≤ (16*h128Length r h/h)*∑ v,w v := by
  let ell := h128Length r h
  have hell : 0 < ell := h128_length_pos hrh
  have hellR : (0:ℝ) < ell := by exact_mod_cast hell
  let K : ℕ := ⌊h/(16*ell)⌋₊
  let Good : G.Walk a b → Prop := fun p =>
    (∀ v ∈ p.support, v ∈ S) ∧ Disjoint (routeInterior p) W
  have hfloor : (K:ℝ) ≤ h/(16*ell) := Nat.floor_le (by positivity)
  have hK : (K:ℝ)*(16*ell) ≤ h := (le_div_iff₀ (by positivity)).mp hfloor
  have hpath : ∀ X : Finset V, X.card ≤ K*ell → a ∉ X → b ∉ X →
      ∃ p : G.Walk a b, p.IsPath ∧ p.length ≤ ell ∧ Good p ∧
        Disjoint (routeInterior p) X := by
    intro X hX haX hbX
    have hXR : (X.card:ℝ) ≤ (K:ℝ)*ell := by exact_mod_cast hX
    have hXbound : (X.card:ℝ) ≤ h/16 := by nlinarith only [hK,hXR]
    obtain ⟨p,hp,hlen,hs,hW,hX⟩ := h128_short_path_avoiding hh hrh hr hexp
      ha hb haW hbW haX hbX hW hXbound
    exact ⟨p,hp,hlen,⟨hs,hW⟩,hX⟩
  obtain ⟨P⟩ := exists_short_path_fan Good hpath
  obtain ⟨i,hi⟩ := P.exists_weight_le_average (by omega : 0 < K+1) w hw
  have hKlt : h/(16*ell) < (K:ℝ)+1 := Nat.lt_floor_add_one _
  have hKn : (0:ℝ) < (K:ℝ)+1 := by positivity
  have hpay : (1:ℝ)/((K:ℝ)+1) ≤ 16*ell/h := by
    apply (div_le_div_iff₀ hKn hh).mpr
    have hx := (div_lt_iff₀ (by positivity : (0:ℝ) < 16*ell)).mp hKlt
    nlinarith only [hx]
  have hsum : 0 ≤ ∑ v,w v := Finset.sum_nonneg (fun v _ => hw v)
  have htotal := mul_le_mul_of_nonneg_right hpay hsum
  refine ⟨P.path i,P.simple i,P.length_le i,(P.good i).1,(P.good i).2,?_⟩
  push_cast at hi
  have htotal' : (∑ v,w v)/((K:ℝ)+1) ≤ (16*ell/h)*∑ v,w v := by
    convert htotal using 1 <;> ring
  exact hi.trans htotal'

end
end Cycle13
