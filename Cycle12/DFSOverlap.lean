import Cycle12.Foundations.DFSPartition

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem dfs_block_order_ratio {G : SimpleGraph V} {k T : ℕ}
    (hk : 0 < k) (B : DFSBlock G k T) :
    (B.vertices.card:ℝ) ≤ (1+(T:ℝ)/k)*B.core.card := by
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  rw [B.vertices_card,Nat.cast_add]
  rcases B.size with h | h
  · simp only [h.2,Finset.card_empty,Nat.cast_zero,add_zero]
    have hnon : (0:ℝ) ≤ (T:ℝ)/k*B.core.card := by positivity
    nlinarith only [hnon]
  · have hb : (B.boundary.card:ℝ) ≤ T := by exact_mod_cast h.2.2
    have hc : (k:ℝ) ≤ B.core.card := by exact_mod_cast h.1
    have hmul := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ (T:ℝ)/k)
    have he : (T:ℝ)/k*k=T := div_mul_cancel₀ _ (ne_of_gt hk')
    rw [he] at hmul
    nlinarith only [hb,hmul]

theorem dfs_partition_mass_bound {G : SimpleGraph V} {S : Finset V} {k T : ℕ}
    (hk : 0 < k) (P : DFSPartition G S k T) :
    (∑ i, ((P.block i).vertices.card:ℝ)) ≤ (1+(T:ℝ)/k)*S.card := by
  calc
    _ ≤ ∑ i, (1+(T:ℝ)/k)*((P.block i).core.card:ℝ) :=
      Finset.sum_le_sum (fun i _ => dfs_block_order_ratio hk (P.block i))
    _ = _ := by rw [← Finset.mul_sum,← Nat.cast_sum,P.sum_core_card]

theorem dfs_block_order_bound {G : SimpleGraph V} {k T : ℕ}
    (B : DFSBlock G k T) : B.vertices.card ≤ 2*k+T := by
  rw [B.vertices_card]
  rcases B.size with h | h
  · simp only [h.2,Finset.card_empty,add_zero]
    omega
  · omega

/-- The floor errors are retained in the denominator. -/
theorem dfs_floor_overlap {L ell : ℝ} (hell : 1 ≤ ell) (hL : ell+2<L) :
    let T := ⌊ell⌋₊
    let k := ⌊(L-(T:ℝ))/2⌋₊
    0 < k ∧ 1 ≤ T ∧ (2*k+T:ℕ) ≤ L ∧
      (T:ℝ)/k ≤ 2*ell/(L-ell-2) := by
  dsimp
  let T := ⌊ell⌋₊
  let k := ⌊(L-(T:ℝ))/2⌋₊
  have hT : (T:ℝ) ≤ ell := Nat.floor_le (by linarith : 0 ≤ ell)
  have hTpos : 1 ≤ T := Nat.le_floor (by simpa only [Nat.cast_one] using hell)
  have hx : 1 < (L-(T:ℝ))/2 := by linarith
  have hkpos : 0 < k := by
    have hh : 1 ≤ k := Nat.le_floor (by simpa only [Nat.cast_one] using hx.le)
    omega
  have hklo := Nat.lt_floor_add_one ((L-(T:ℝ))/2)
  have hkhi := Nat.floor_le (by linarith : 0 ≤ (L-(T:ℝ))/2)
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hkpos
  have hden : 0 < L-ell-2 := by linarith
  refine ⟨hkpos,hTpos,?_,?_⟩
  · change ((2*k+T:ℕ):ℝ) ≤ L
    push_cast
    change 2*(k:ℝ)+(T:ℝ) ≤ L
    change (k:ℝ) ≤ (L-(T:ℝ))/2 at hkhi
    linarith only [hkhi]
  · change (T:ℝ)/k ≤ 2*ell/(L-ell-2)
    apply (div_le_div_iff₀ hk' hden).mpr
    have hklt : L-ell-2 < 2*(k:ℝ) := by
      change (L-(T:ℝ))/2 < (k:ℝ)+1 at hklo
      linarith only [hklo,hT]
    have hmul1 := mul_le_mul_of_nonneg_right hT hden.le
    have hmul2 := mul_le_mul_of_nonneg_left hklt.le (by linarith : 0 ≤ ell)
    nlinarith only [hmul1,hmul2]

end
end Cycle12
