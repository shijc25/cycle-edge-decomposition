import Cycle12.Foundations.RoutingLoadCounts

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

theorem routing_charge_bound {h B k q a z τ x f y D I : ℝ}
    (hh : 0 < h) (hB : 0 < B) (ha : 0 < a) (hz : 0 < z) (hτ : 0 < τ)
    (hf : 0 ≤ f) (hk : k ≤ q*B) (hF : f=x*D) (hZ : f+y<D)
    (hcharge : q*x/z+(1-x)/τ=(1+q)/a)
    (hcap : B*D*(1+q) ≤ a*h*I) : k*f/(z*h)+B*y/(τ*h) < I := by
  have he : k*f/(z*h) ≤ (B/h)*(q*f/z) := by
    have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk hf)
      (mul_nonneg hz.le hh.le)
    convert hb using 1 <;> ring
  have hy : y < (1-x)*D := by nlinarith only [hF,hZ]
  have hs : q*f/z+y/τ < D*(q*x/z+(1-x)/τ) := by
    have hy' := div_lt_div_of_pos_right hy hτ
    rw [hF]
    calc
      _ < q*(x*D)/z+((1-x)*D)/τ := by linarith only [hy']
      _ = _ := by ring
  have hstrict := mul_lt_mul_of_pos_left hs (div_pos hB hh)
  have hb : (B/h)*D*((1+q)/a) ≤ I := by
    have heq : (B/h)*D*((1+q)/a)=(B*D*(1+q))/(a*h) := by ring
    rw [heq]
    exact (div_le_iff₀ (mul_pos ha hh)).mpr (by nlinarith only [hcap])
  rw [hcharge] at hstrict
  have heq : B*y/(τ*h)=(B/h)*(y/τ) := by ring
  rw [heq]
  nlinarith only [he,hstrict,hb]

variable {ι V τ : Type} [Fintype ι] [Fintype V] [Fintype τ]
  [DecidableEq ι] [DecidableEq V] [DecidableEq τ]

theorem team_bad_card_le_threshold (team : ι → τ) {B t : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B)
    (hload : ∀ c, (teamLoad team c:ℝ) ≤ B) (I : Finset ι) (Y : Finset (τ × V)) :
    ((I.filter fun i => t < ((teamMarkers Y (team i)).card:ℝ)).card:ℝ) ≤
      (B/t)*Y.card := by
  have hb := team_bad_card_le (h:=5*t) team (by positivity) hB hload I Y
  have ht' : 5*t/5=t := by ring
  have hc : 5*B/(5*t)=B/t := by ring
  rwa [ht',hc] at hb

theorem routing_exists_good_demand (source target : ι → V) (team : ι → τ)
    (I : Finset ι) (S : Finset V) (F : Finset (Sym2 V)) (Y : Finset (τ × V))
    {h B k z t : ℝ} (hh : 0 < h) (hz : 0 < z) (ht : 0 < t)
    (hB : 0 ≤ B) (hk : 0 ≤ k)
    (hend : ∀ v, (endpointLoad source target v:ℝ) ≤ k)
    (hteam : ∀ c, (teamLoad team c:ℝ) ≤ B)
    (hS : (S.card:ℝ) ≤ F.card/(z*h))
    (hcharge : k*F.card/(z*h)+B*Y.card/(t*h) < I.card) :
    ∃ i ∈ I, source i ∉ S ∧ target i ∉ S ∧
      ((teamMarkers Y (team i)).card:ℝ) ≤ t*h := by
  let badEnds := I.filter fun i => source i ∈ S ∨ target i ∈ S
  let badTeams := I.filter fun i => t*h < ((teamMarkers Y (team i)).card:ℝ)
  have he : (badEnds.card:ℝ) ≤ k*F.card/(z*h) := by
    have hb := (endpoint_bad_card_le source target hend I S).trans
      (mul_le_mul_of_nonneg_left hS hk)
    simpa only [mul_div_assoc] using hb
  have ht' : (badTeams.card:ℝ) ≤ B*Y.card/(t*h) := by
    have hb := team_bad_card_le_threshold team (mul_pos ht hh) hB hteam I Y
    simpa only [div_mul_eq_mul_div] using hb
  have hboth : ((badEnds∪badTeams).card:ℝ) ≤ (badEnds.card:ℝ)+badTeams.card := by
    exact_mod_cast Finset.card_union_le badEnds badTeams
  have hless : ((badEnds∪badTeams).card:ℝ) < I.card := by linarith
  have hlessN : (badEnds∪badTeams).card < I.card := by exact_mod_cast hless
  have hnot : ¬I ⊆ badEnds∪badTeams := fun hs =>
    (Nat.not_le_of_lt hlessN) (Finset.card_le_card hs)
  obtain ⟨i,hi,hgood⟩ := Finset.not_subset.mp hnot
  have hnotEnds : i ∉ badEnds := fun h => hgood (Finset.mem_union_left _ h)
  have hnotTeams : i ∉ badTeams := fun h => hgood (Finset.mem_union_right _ h)
  refine ⟨i,hi,?_,?_,?_⟩
  · intro hs
    exact hnotEnds (Finset.mem_filter.mpr ⟨hi,Or.inl hs⟩)
  · intro hs
    exact hnotEnds (Finset.mem_filter.mpr ⟨hi,Or.inr hs⟩)
  · by_contra! hs
    exact hnotTeams (Finset.mem_filter.mpr ⟨hi,hs⟩)

end
end Cycle12
