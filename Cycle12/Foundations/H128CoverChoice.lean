import Cycle12.Foundations.RoutingLoadCounts
import Cycle12.Foundations.H128Arithmetic

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem h128_edge_cover_budget {r h B k L I f z : ℝ}
    (hh : 0 < h) (hr : 0 < r) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hk : k ≤ (5/6)*B) (hcapacity : 20*B*L ≤ h)
    (hI : 2*I ≤ k*r) (hf : f ≤ z) (hz : z < 4*L*I) :
    f < (25/297)*h*r := by
  have hscale := mul_le_mul_of_nonneg_left hI (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL)
  have h₁ := mul_le_mul_of_nonneg_right hk (mul_nonneg hL hr.le)
  have h₂ := mul_le_mul_of_nonneg_right hcapacity hr.le
  have hmain : 2*k*L*r ≤ h*r/12 := by nlinarith only [h₁,h₂]
  have hhprod := mul_pos hh hr
  nlinarith only [hscale,hmain,hf,hz,hhprod]

theorem h128_endpoint_charge {h B k f R : ℝ} (hh : 0 < h)
    (hB : 0 ≤ B) (hk₀ : 0 ≤ k) (hf : 0 ≤ f)
    (hk : k ≤ (5/6)*B) (hR : R ≤ 11*f/(5*h)) :
    k*R ≤ (5*B/h)*f := by
  have hR' := (le_div_iff₀ (by positivity : (0:ℝ) < 5*h)).mp hR
  have h₁ := mul_le_mul_of_nonneg_left hR' hk₀
  have hk' : 11*k ≤ 25*B := by nlinarith only [hk,hB]
  have h₂ := mul_le_mul_of_nonneg_right hk' hf
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hh).mpr
  nlinarith only [h₁,h₂]

variable {ι V τ : Type} [Fintype ι] [Fintype V] [Fintype τ]
  [DecidableEq ι] [DecidableEq V] [DecidableEq τ]

/-- Among a nonempty set of demands, at least one keeps both endpoints
after pruning and belongs to a team with at most h/5 forbidden markers. -/
theorem h128_exists_good_demand (source target : ι → V) (team : ι → τ)
    (I : Finset ι) (R : Finset V) (F : Finset (Sym2 V)) (Y : Finset (τ × V))
    {h B k : ℝ} {ell : ℕ} (hh : 0 < h) (hB : 0 < B) (hk₀ : 0 ≤ k)
    (hk : k ≤ (5/6)*B) (hcapacity : 20*B*ell ≤ h)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k)
    (hteam : ∀ c, (teamLoad team c:ℝ) ≤ B)
    (hR : (R.card:ℝ) ≤ 11*F.card/(5*h))
    (hZ : (F.card:ℝ)+Y.card < 4*ell*I.card) :
    ∃ i ∈ I, source i ∉ R ∧ target i ∉ R ∧
      ((teamMarkers Y (team i)).card:ℝ) ≤ h/5 := by
  let badEnds := I.filter fun i => source i ∈ R ∨ target i ∈ R
  let badTeams := I.filter fun i => h/5 < ((teamMarkers Y (team i)).card:ℝ)
  have he : (badEnds.card:ℝ) ≤ (5*B/h)*F.card :=
    (endpoint_bad_card_le source target hend I R).trans
      (h128_endpoint_charge hh hB.le hk₀ (Nat.cast_nonneg _) hk hR)
  have ht : (badTeams.card:ℝ) ≤ (5*B/h)*Y.card :=
    team_bad_card_le team hh hB.le hteam I Y
  have hboth : ((badEnds∪badTeams).card:ℝ) ≤ (badEnds.card:ℝ)+badTeams.card := by
    exact_mod_cast Finset.card_union_le badEnds badTeams
  have hcoef : 0 < 5*B/h := by positivity
  have hstrict := mul_lt_mul_of_pos_left hZ hcoef
  have hcap : (5*B/h)*(4*(ell:ℝ)) ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_one hh).mpr
    nlinarith only [hcapacity]
  have hcount := mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg (α:=ℝ) I.card)
  have hless : ((badEnds∪badTeams).card:ℝ) < I.card := by
    nlinarith only [he,ht,hboth,hstrict,hcount]
  have hlessN : (badEnds∪badTeams).card < I.card := by exact_mod_cast hless
  have hnot : ¬I ⊆ badEnds∪badTeams := fun hs =>
    (Nat.not_le_of_lt hlessN) (Finset.card_le_card hs)
  obtain ⟨i,hi,hgood⟩ := Finset.not_subset.mp hnot
  have hnotEnds : i ∉ badEnds := fun hh => hgood (Finset.mem_union_left _ hh)
  have hnotTeams : i ∉ badTeams := fun hh => hgood (Finset.mem_union_right _ hh)
  refine ⟨i,hi,?_,?_,?_⟩
  · intro hs
    exact hnotEnds (Finset.mem_filter.mpr ⟨hi,Or.inl hs⟩)
  · intro hs
    exact hnotEnds (Finset.mem_filter.mpr ⟨hi,Or.inr hs⟩)
  · by_contra! hs
    exact hnotTeams (Finset.mem_filter.mpr ⟨hi,hs⟩)

end
end Cycle13
