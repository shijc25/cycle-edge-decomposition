import Cycle12.Foundations.SoftTrailClosure
import Cycle12.Foundations.H128Arithmetic

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Shared vertices in different batches do not invalidate the fee bound:
each path occurrence is paid by its own original edges. -/
theorem path_family_interior_budget (G : SimpleGraph V) (a b : I → V)
    (p : ∀ i,G.Walk (a i) (b i)) (hp : ∀ i,(p i).IsPath)
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet)) :
    (∑ i,(routeInterior (p i)).card) ≤ (⋃ i,(p i).edgeSet).ncard := by
  rw [ncard_iUnion_disjoint _ hd]
  apply Finset.sum_le_sum
  intro i hi
  rw [trail_edgeSet_ncard (p i) (hp i).isTrail]
  exact routeInterior_card_le (p i)

/-- Sum the integer intersection fees without any additive rounding
loss. The endpoint allowance, rather than the number of demands, pays
the coefficient 4/(5a). -/
theorem summed_soft_fee_le {ell : ℕ} {h B a : ℝ}
    (hh : 0 < h) (ha : 0 < a) (haB : a ≤ B) (hcap : 20*B*ell ≤ h)
    (Z : I → Finset V) :
    ((∑ i,⌊16*(ell:ℝ)*(Z i).card/h⌋₊):ℝ) ≤
      (4/(5*a))*(∑ i,((Z i).card:ℝ)) := by
  have hsmall : 20*a*ell ≤ h := by
    have hh' := mul_le_mul_of_nonneg_right haB (by positivity : (0:ℝ) ≤ 20*ell)
    nlinarith only [hh',hcap]
  have hcoeff : 16*(ell:ℝ)/h ≤ 4/(5*a) := by
    apply (div_le_div_iff₀ hh (by positivity)).mpr
    nlinarith only [hsmall]
  have hf : ∀ i,(⌊16*(ell:ℝ)*(Z i).card/h⌋₊:ℝ) ≤
      (16*(ell:ℝ)/h)*((Z i).card:ℝ) := by
    intro i
    convert Nat.floor_le (by positivity : (0:ℝ) ≤ 16*(ell:ℝ)*(Z i).card/h) using 1 <;> ring
  calc
    _ ≤ ∑ i,(16*(ell:ℝ)/h)*((Z i).card:ℝ) := Finset.sum_le_sum (fun i _ => hf i)
    _ = (16*(ell:ℝ)/h)*(∑ i,((Z i).card:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem h128_original_edge_soft_budget (G : SimpleGraph V) (source target : I → V)
    (p : ∀ i,G.Walk (source i) (target i)) (hp : ∀ i,(p i).IsPath)
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet))
    {h B a : ℝ} (hh : 0 < h) (ha : 0 < a) (haB : a ≤ B)
    (hcube : 16384*B^2*Fintype.card V ≤ h^3) :
    ((∑ i,⌊16*(h128Length (Fintype.card V) h:ℝ)*(routeInterior (p i)).card/h⌋₊):ℝ) ≤
      (4/(5*a))*((⋃ i,(p i).edgeSet).ncard:ℝ) := by
  have hcap := h128_capacity hh (ha.le.trans haB) (Nat.cast_nonneg _) hcube
  have hf := summed_soft_fee_le hh ha haB hcap (fun i => routeInterior (p i))
  have hsum : (∑ i,((routeInterior (p i)).card:ℝ)) ≤ ((⋃ i,(p i).edgeSet).ncard:ℝ) := by
    exact_mod_cast path_family_interior_budget G source target p hp hd
  exact hf.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

end
end Cycle13
