import Mathlib

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι V τ : Type} [Fintype ι] [Fintype V] [Fintype τ]
  [DecidableEq ι] [DecidableEq V] [DecidableEq τ]

def endpointLoad (source target : ι → V) (v : V) : ℕ :=
  (Finset.univ.filter fun i => source i=v).card+
  (Finset.univ.filter fun i => target i=v).card

def teamLoad (team : ι → τ) (c : τ) : ℕ :=
  (Finset.univ.filter fun i => team i=c).card

theorem sum_endpointLoad (source target : ι → V) :
    (∑ v, endpointLoad source target v)=2*Fintype.card ι := by
  unfold endpointLoad
  rw [Finset.sum_add_distrib,Finset.sum_card_fiberwise_eq_card_filter,
    Finset.sum_card_fiberwise_eq_card_filter]
  simp
  omega

theorem total_demands_le (source target : ι → V) {k : ℝ}
    (hload : ∀ v, (endpointLoad source target v:ℝ) ≤ k) :
    2*(Fintype.card ι:ℝ) ≤ k*Fintype.card V := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => hload v)
  rw [← Nat.cast_sum,sum_endpointLoad] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

theorem endpoint_bad_card_le (source target : ι → V) {k : ℝ}
    (hload : ∀ v, (endpointLoad source target v:ℝ) ≤ k) (I : Finset ι) (R : Finset V) :
    ((I.filter fun i => source i ∈ R ∨ target i ∈ R).card:ℝ) ≤ k*R.card := by
  have hcover : (I.filter fun i => source i ∈ R ∨ target i ∈ R) ⊆
      (Finset.univ.filter fun i => source i ∈ R) ∪ (Finset.univ.filter fun i => target i ∈ R) := by
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at *
    exact hi.2
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [← Finset.sum_card_fiberwise_eq_card_filter,
    ← Finset.sum_card_fiberwise_eq_card_filter,← Finset.sum_add_distrib] at hc
  have hcR : ((I.filter fun i => source i ∈ R ∨ target i ∈ R).card:ℝ) ≤
      ∑ v ∈ R, (endpointLoad source target v:ℝ) := by exact_mod_cast hc
  have hs := Finset.sum_le_sum (s:=R) (fun v _ => hload v)
  have hs' : (∑ v ∈ R, (endpointLoad source target v:ℝ)) ≤ k*R.card := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hs
  exact hcR.trans hs'

def teamMarkers (Y : Finset (τ × V)) (c : τ) : Finset V :=
  Finset.univ.filter fun v => (c,v) ∈ Y

theorem sum_teamMarkers_card (Y : Finset (τ × V)) :
    (∑ c, (teamMarkers Y c).card)=Y.card := by
  have hcard : ∀ c, (teamMarkers Y c).card=(Y.filter fun p => p.1=c).card := by
    intro c
    apply Finset.card_bij (fun v _ => (c,v))
    · intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,rfl⟩
    · intro x hx y hy hxy
      exact congrArg Prod.snd hxy
    · rintro ⟨d,v⟩ hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      dsimp only at he
      subst d
      exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩
  simp_rw [hcard]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

/-- Count all demands in teams whose marker set is larger than h/5,
charging each such team to its own marker vertices. -/
theorem team_bad_card_le (team : ι → τ) {B h : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    (hload : ∀ c, (teamLoad team c:ℝ) ≤ B) (I : Finset ι) (Y : Finset (τ × V)) :
    ((I.filter fun i => h/5 < ((teamMarkers Y (team i)).card:ℝ)).card:ℝ) ≤
      (5*B/h)*Y.card := by
  let bad : Finset τ := Finset.univ.filter fun c => h/5 < ((teamMarkers Y c).card:ℝ)
  have hsubset : (I.filter fun i => h/5 < ((teamMarkers Y (team i)).card:ℝ)) ⊆
      Finset.univ.filter fun i => team i ∈ bad := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩⟩
  have hcount := Finset.card_le_card hsubset
  rw [← Finset.sum_card_fiberwise_eq_card_filter] at hcount
  have hcountR : ((I.filter fun i => h/5 < ((teamMarkers Y (team i)).card:ℝ)).card:ℝ) ≤
      ∑ c ∈ bad, (teamLoad team c:ℝ) := by exact_mod_cast hcount
  have hpoint : ∀ c ∈ bad, (teamLoad team c:ℝ) ≤ (5*B/h)*(teamMarkers Y c).card := by
    intro c hc
    have hx := (Finset.mem_filter.mp hc).2
    have hm := mul_le_mul_of_nonneg_left hx.le hB
    apply (hload c).trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hh).mpr
    nlinarith only [hm]
  have hsum := Finset.sum_le_sum hpoint
  have hcoef : 0 ≤ 5*B/h := by positivity
  have hsumall : (∑ c ∈ bad, ((teamMarkers Y c).card:ℝ)) ≤ ∑ c, ((teamMarkers Y c).card:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => Nat.cast_nonneg _)
  have hsumid : (∑ c, ((teamMarkers Y c).card:ℝ))=Y.card := by exact_mod_cast sum_teamMarkers_card Y
  rw [hsumid] at hsumall
  rw [← Finset.mul_sum] at hsum
  exact hcountR.trans (hsum.trans (mul_le_mul_of_nonneg_left hsumall hcoef))

end
end Cycle13
