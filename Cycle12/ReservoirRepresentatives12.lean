import Cycle12.RepresentativeChoice

namespace Cycle12
open SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty V]

/-- The exact representative capacity follows from the quadratic router row;
no separate exponential endpoint-representative assumption is used. -/
theorem representative_capacity_bounds {r z : ℝ} (hz : 8192 ≤ z) (hzr : z ≤ r)
    (hsquare : 2112*r ≤ z^2) :
    0 < ⌈8*r/z⌉₊ ∧ (⌈8*r/z⌉₊:ℝ) ≤ 9*r/z ∧ (⌈8*r/z⌉₊:ℝ) < z/64 := by
  have hz0 : 0 < z := by linarith only [hz]
  have hr0 : 0 < r := hz0.trans_le hzr
  have hpos : 0 < 8*r/z := by positivity
  have hceil := Nat.ceil_lt_add_one hpos.le
  have hratio : 1 ≤ r/z := (le_div_iff₀ hz0).mpr (by linarith only [hzr])
  have hupper : (⌈8*r/z⌉₊:ℝ) ≤ 9*r/z := by
    simp only [mul_div_assoc] at hceil ⊢
    linarith only [hceil,hratio]
  refine ⟨Nat.ceil_pos.mpr hpos,hupper,hupper.trans_lt ?_⟩
  apply (div_lt_iff₀ hz0).mpr
  nlinarith only [hsquare,hr0]

theorem reservoir_conflict_representatives (A : Finset I) (K : SimpleGraph I)
    (N : I → Finset V) {r z : ℝ} (hz : 8192 ≤ z) (hzr : z ≤ r)
    (hcard : (A.card:ℝ) ≤ 2*r) (hdeg : ∀ i, K.degree i ≤ 4)
    (hN : ∀ i∈A, (15/16)*z ≤ ((N i).card:ℝ)) :
    ∃ f : I → V, (∀ i∈A, f i∈N i) ∧
      (∀ i∈A, ∀ j∈A, K.Adj i j → f i≠f j) ∧
      (∀ v, (A.filter (fun i => f i=v)).card ≤ ⌈8*r/z⌉₊) := by
  apply choose_representatives_with_conflicts A K N ⌈8*r/z⌉₊ 4 hdeg
  intro i hi
  have hz0 : 0 < z := by linarith only [hz]
  have hn := hN i hi
  have hfour : 4 ≤ (N i).card := by
    have hh : (4:ℝ) ≤ (N i).card := by linarith only [hn,hz]
    exact_mod_cast hh
  have hleft : z/4 ≤ (((N i).card-4:ℕ):ℝ) := by
    rw [Nat.cast_sub hfour]
    push_cast
    linarith only [hz,hn]
  have hceil : 8*r/z ≤ (⌈8*r/z⌉₊:ℝ) := Nat.le_ceil _
  have hprod : (A.card:ℝ) ≤ (((N i).card-4:ℕ):ℝ)*(⌈8*r/z⌉₊:ℝ) := by
    calc
      _ ≤ 2*r := hcard
      _ = (z/4)*(8*r/z) := by field_simp; ring
      _ ≤ (z/4)*(⌈8*r/z⌉₊:ℝ) := mul_le_mul_of_nonneg_left hceil (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hleft (Nat.cast_nonneg _)
  exact_mod_cast hprod

/-- Actual connector edges are injective, also when distinct demands have
repeated roots. The conflict graph can simultaneously separate mates. -/
theorem choose_reservoir_connectors (G : SimpleGraph V) (U : Finset V)
    (source : I → V) (K : SimpleGraph I) {r z : ℝ}
    (hz : 8192 ≤ z) (hzr : z ≤ r) (hsquare : 2112*r ≤ z^2)
    (hcard : (Fintype.card I:ℝ) ≤ 2*r) (hdeg : ∀ i, K.degree i ≤ 4)
    (hroot : ∀ i j, i≠j → source i=source j → K.Adj i j)
    (hout : ∀ i, source i∉U)
    (hN : ∀ i, (15/16)*z ≤ ((U.filter (G.Adj (source i))).card:ℝ)) :
    ∃ f : I → V, (∀ i, f i∈U ∧ G.Adj (source i) (f i)) ∧
      (∀ i j, K.Adj i j → f i≠f j) ∧
      Function.Injective (fun i => s(source i,f i)) ∧
      (∀ v, (univ.filter (fun i => f i=v)).card ≤ ⌈8*r/z⌉₊) ∧
      (⌈8*r/z⌉₊:ℝ) < z/64 := by
  obtain ⟨f,hf,hsep,hcap⟩ := reservoir_conflict_representatives univ K
    (fun i => U.filter (G.Adj (source i))) hz hzr (by simpa only [card_univ] using hcard)
    hdeg (fun i _ => hN i)
  have hgood : ∀ i, f i∈U ∧ G.Adj (source i) (f i) := fun i => mem_filter.mp (hf i (mem_univ _))
  have hseparate : ∀ i j, K.Adj i j → f i≠f j := fun i j => hsep i (mem_univ _) j (mem_univ _)
  refine ⟨f,hgood,hseparate,?_,hcap,(representative_capacity_bounds hz hzr hsquare).2.2⟩
  intro i j he
  rcases Sym2.eq_iff.mp he with he | he
  · by_contra hij
    exact hseparate i j (hroot i j hij he.1) he.2
  · exact False.elim (hout i (he.1.symm ▸ (hgood j).1))

end
end Cycle12
