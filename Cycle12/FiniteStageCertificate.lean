import Cycle12.FiniteTangentCertificate

namespace Cycle12
open Cycle13

structure FiniteStageCertificate (T t : ℕ) (K : ℚ) where
  b : ℚ
  b_pos : 0 < b
  T_large : 2^20 ≤ T
  small : (1+1/b)/2 ≤ K
  left : FiniteCoreCertificate T t (1/(2*b+1/1048576)) K
  right : FiniteCoreCertificate T t (1/b) K
  component : FiniteComponentCertificate (b*T+1) T t K

/-- Every premise here is a finite rational certificate or the two
explicit graph-theoretic inputs. There are no unverified density bounds. -/
theorem FiniteStageCertificate.step {T t : ℕ} {K : ℚ} (E : FiniteStageCertificate T t K)
    {C : ℝ}
    (hcover : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      FineCover H 2 ∧ CoarseCover H 1)
    (hsuffix : WeightedAffineBound C t) : WeightedAffineBound (C+(K:ℝ)) T := by
  have ht : (0:ℝ) < t := by
    have hh := E.component.t_pos
    exact_mod_cast hh
  apply weightedAffine_mixed_dfs_step (b := (E.b:ℝ))
    (by exact_mod_cast E.b_pos) E.T_large ht hcover hsuffix
    (by exact_mod_cast E.small)
  · intro d hd
    have hh := E.left.bound (d := d) (by exact_mod_cast hd.le)
    simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_one,
      Rat.cast_ofNat,Rat.cast_natCast] using hh
  · intro d hd
    have hh := E.right.bound (d := d) (by exact_mod_cast hd.le)
    simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_one,
      Rat.cast_ofNat,Rat.cast_natCast] using hh
  · intro s m hs hsm hm
    have hh := E.component.bound hs (by exact_mod_cast hsm) hm
    simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_one,
      Rat.cast_ofNat,Rat.cast_natCast] using hh

end Cycle12
