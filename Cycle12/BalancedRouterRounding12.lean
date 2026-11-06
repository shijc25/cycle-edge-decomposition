import Cycle12.Foundations.DenseStrong

namespace Cycle12
open Real
noncomputable section

def balancedBranchCount (z : ℝ) : ℕ := 2*⌊z/32⌋₊
def balancedBranchCapacity (z : ℝ) : ℕ := ⌊z/64⌋₊

/-- All integer losses for the all-branch router, including the branch
capacity and the terminal-pairability floor, with the exact constant 2112. -/
theorem balanced_router_rounding {z : ℝ} {N : ℕ} (hz : 8192 ≤ z)
    (hsquare : 2112*(N:ℝ) ≤ z^2) :
    4 ≤ balancedBranchCount z ∧ Even (balancedBranchCount z) ∧
    (7*balancedBranchCount z+5:ℕ) ≤ (225/512:ℝ)*z ∧
    (balancedBranchCapacity z:ℝ) ≤ z/64 ∧
    2*N ≤ balancedBranchCapacity z*balancedBranchCount z ∧
    balancedBranchCapacity z ≤ 2*(balancedBranchCount z/6-2) := by
  have hz0 : 0 ≤ z := by linarith only [hz]
  have htlo0 := Nat.lt_floor_add_one (z/32)
  have hthi0 := Nat.floor_le (show 0 ≤ z/32 by positivity)
  have hclo0 := Nat.lt_floor_add_one (z/64)
  have hchi := Nat.floor_le (show 0 ≤ z/64 by positivity)
  have htlo : z/16-2 ≤ (balancedBranchCount z:ℝ) := by
    unfold balancedBranchCount
    push_cast
    linarith only [htlo0]
  have hthi : (balancedBranchCount z:ℝ) ≤ z/16 := by
    unfold balancedBranchCount
    push_cast
    linarith only [hthi0]
  have hclo : z/64-1 ≤ (balancedBranchCapacity z:ℝ) := by
    change z/64-1 ≤ (⌊z/64⌋₊:ℝ)
    linarith only [hclo0]
  have hsmall : 4 ≤ balancedBranchCount z := by
    have hh : (4:ℝ) ≤ balancedBranchCount z := by linarith only [htlo,hz]
    exact_mod_cast hh
  have hlarge : 128 ≤ balancedBranchCapacity z :=
    Nat.le_floor (by linarith only [hz] : (128:ℝ) ≤ z/64)
  have hratio : 4*balancedBranchCapacity z ≤ balancedBranchCount z+2 := by
    have hh : (4:ℝ)*(balancedBranchCapacity z:ℝ) ≤ balancedBranchCount z+2 := by
      change _ ≤ _ at hchi
      dsimp only [balancedBranchCapacity]
      linarith only [hchi,htlo]
    exact_mod_cast hh
  refine ⟨hsmall, ⟨⌊z/32⌋₊, by dsimp [balancedBranchCount]; omega⟩, ?_, hchi, ?_, ?_⟩
  · push_cast
    linarith only [hthi,hz]
  · have hprod : (z/16-2)*(z/64-1) ≤
        (balancedBranchCount z:ℝ)*(balancedBranchCapacity z:ℝ) :=
      mul_le_mul htlo hclo (by linarith only [hz]) (Nat.cast_nonneg _)
    have hzsq : 8192*z ≤ z^2 := by nlinarith only [mul_nonneg (by linarith only [hz] : 0 ≤ z-8192) hz0]
    have hc : (2:ℝ)*(N:ℝ) ≤ (balancedBranchCapacity z:ℝ)*(balancedBranchCount z:ℝ) := by
      nlinarith only [hprod,hsquare,hzsq]
    exact_mod_cast hc
  · omega

end
end Cycle12
