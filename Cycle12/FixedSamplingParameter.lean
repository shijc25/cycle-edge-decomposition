import Cycle12.FixedSizeFactorTwo

namespace Cycle12
open Finset Cycle13
noncomputable section

def fixedSamplingParameter (n k : ℕ) (hk : k≤n) : unitInterval :=
  ⟨(k:ℝ)/(n:ℝ),div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),by
    by_cases hn : n=0
    · subst n
      simp
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
      exact_mod_cast hk⟩

theorem fixed_sampling_parameter_mean (n k : ℕ) (hk : k≤n) :
    (n:ℝ)*(fixedSamplingParameter n k hk:ℝ)=(k:ℝ) := by
  by_cases hn : n=0
  · have hk0 : k=0 := by omega
    subst n
    subst k
    norm_num [fixedSamplingParameter]
  · change (n:ℝ)*((k:ℝ)/(n:ℝ))=(k:ℝ)
    field_simp

theorem fixed_sampling_parameter_half (n k : ℕ) (hk : k≤n) (hhalf : 2*k≤n) :
    (fixedSamplingParameter n k hk:ℝ)≤1/2 := by
  by_cases hn : n=0
  · subst n
    simp [fixedSamplingParameter]
  · change (k:ℝ)/(n:ℝ)≤1/2
    apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
    have hh : 2*(k:ℝ)≤n := by exact_mod_cast hhalf
    linarith

theorem fixed_sampling_residual_half (r N t : ℕ) (ht : t≤N) (hN : 2*N≤r) :
    2*(N-t)≤r-t := by omega

variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_size_canonical_factor_two (D : Finset V) {k : ℕ}
    (hk : k≤D.card) (hhalf : 2*k≤D.card) (E : Finset V → Prop)
    (hE : ∀ S T, S⊆T → E T → E S) :
    (fixedSizeLaw D k).prob E ≤
      2*(subsetBernoulli D (fixedSamplingParameter D.card k hk)).prob E :=
  fixed_size_decreasing_factor_two D _ hk (fixed_sampling_parameter_mean D.card k hk)
    (fixed_sampling_parameter_half D.card k hk hhalf) E hE

end
end Cycle12
