import Cycle12.MinorityLabelEntropy

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

theorem fixed_marked_restricted_label_bound (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (L : Finset V → Ξ → Finset (Finset V))
    (E : Finset V → Finset V → Ξ → Finset V → Prop) {count eta : ℝ} (heta : 0 ≤ eta)
    (hcount : ∀ T⊆D, T.card=t → ∀ xi, ((L T xi).card:ℝ) ≤ count)
    (hpoint : ∀ T⊆D, T.card=t → ∀ xi A, A∈L T xi →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => E (T∪R) T xi A) ≤ eta) :
    (fixedMarkedExperiment D N t kap).prob
      (fun x => ∃ A∈L x.2.1 x.2.2, E x.1 x.2.1 x.2.2 A) ≤ count*eta := by
  rw [fixed_marked_experiment_prob D N t kap
    (fun U T xi => ∃ A∈L T xi, E U T xi A),fixed_marked_sampling_order_reversal D hN ht]
  rw [← (fixedSizeLaw D t).expect_const (count*eta)]
  apply FiniteLaw.expect_mono_support
  intro T hT
  obtain ⟨hTD,hcard⟩ := fixed_size_support D T (ht.trans hN) hT
  unfold FiniteLaw.prob
  rw [FiniteLaw.expect_comm]
  change (kap T).expect (fun xi => (fixedSizeLaw (D\T) (N-t)).prob
    (fun R => ∃ A∈L T xi, E (T∪R) T xi A)) ≤ _
  have hp (xi : Ξ) : (fixedSizeLaw (D\T) (N-t)).prob
      (fun R => ∃ A∈L T xi, E (T∪R) T xi A) ≤ count*eta := by
    apply (prob_exists_finset_le_sum (fixedSizeLaw (D\T) (N-t)) (L T xi)
      (fun A R => E (T∪R) T xi A)).trans
    calc
      _ ≤ ∑ _A∈L T xi, eta := sum_le_sum (fun A hA => hpoint T hTD hcard xi A hA)
      _ = ((L T xi).card:ℝ)*eta := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ count*eta := mul_le_mul_of_nonneg_right (hcount T hTD hcard xi) heta
  simpa only [FiniteLaw.expect_const] using (kap T).expect_mono hp

theorem fixed_marked_minority_label_bound (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (E : Finset V → Finset V → Ξ → Finset V → Prop) {rho eta : ℝ}
    (hr : 0 < rho) (hrhalf : rho ≤ 1/2) (heta : 0 ≤ eta)
    (hpoint : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T → (A.card:ℝ) ≤ rho*t →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => E (T∪R) T xi A) ≤ eta) :
    (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
      (A.card:ℝ) ≤ rho*t ∧ E x.1 x.2.1 x.2.2 A) ≤ exp ((t:ℝ)*binEntropy rho)*eta := by
  let L := fun (T : Finset V) (_xi : Ξ) => T.powerset.filter (fun A => (A.card:ℝ) ≤ rho*t)
  have hh := fixed_marked_restricted_label_bound D hN ht kap L E heta
    (fun T _ hT _ => by simpa only [L,hT] using minority_labels_entropy_bound T hr hrhalf)
    (fun T hTD hT xi A hA =>
      hpoint T hTD hT xi A (mem_powerset.mp (mem_filter.mp hA).1) (mem_filter.mp hA).2)
  have he : (fun x : Finset V×(Finset V×Ξ) => ∃ A⊆x.2.1,
      (A.card:ℝ) ≤ rho*t ∧ E x.1 x.2.1 x.2.2 A)=
      (fun x => ∃ A∈L x.2.1 x.2.2, E x.1 x.2.1 x.2.2 A) := by
    funext x
    apply propext
    simp only [L,mem_filter,mem_powerset,exists_prop,and_assoc]
  rwa [he]

theorem fixed_marked_two_label_regimes (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (Esmall Elarge : Finset V → Finset V → Ξ → Finset V → Prop) {rho etaSmall etaLarge : ℝ}
    (hr : 0 < rho) (hrhalf : rho ≤ 1/2) (hetaSmall : 0 ≤ etaSmall)
    (hsmall : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T → (A.card:ℝ) ≤ rho*t →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => Esmall (T∪R) T xi A) ≤ etaSmall)
    (hlarge : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => Elarge (T∪R) T xi A) ≤ etaLarge) :
    (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
      ((A.card:ℝ) ≤ rho*t ∧ Esmall x.1 x.2.1 x.2.2 A) ∨ Elarge x.1 x.2.1 x.2.2 A) ≤
      exp ((t:ℝ)*binEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge := by
  let Fsmall := fun x : Finset V×(Finset V×Ξ) =>
    ∃ A⊆x.2.1, (A.card:ℝ) ≤ rho*t ∧ Esmall x.1 x.2.1 x.2.2 A
  let Flarge := fun x : Finset V×(Finset V×Ξ) => ∃ A⊆x.2.1, Elarge x.1 x.2.1 x.2.2 A
  have hs := fixed_marked_minority_label_bound D hN ht kap Esmall hr hrhalf hetaSmall hsmall
  have hl := fixed_marked_uniform_label_bound D hN ht kap Elarge hlarge
  have hincl : (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
      ((A.card:ℝ) ≤ rho*t ∧ Esmall x.1 x.2.1 x.2.2 A) ∨ Elarge x.1 x.2.1 x.2.2 A) ≤
      (fixedMarkedExperiment D N t kap).prob (fun x => Fsmall x ∨ Flarge x) := by
    apply FiniteLaw.prob_mono
    rintro x ⟨A,hA,h | h⟩
    · exact Or.inl ⟨A,hA,h⟩
    · exact Or.inr ⟨A,hA,h⟩
  exact hincl.trans (((fixedMarkedExperiment D N t kap).prob_union_le Fsmall Flarge).trans
    (add_le_add hs hl))

end
end Cycle12
