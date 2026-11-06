import Cycle12.FixedMarkedCounting
import Cycle12.Foundations.FiniteJointLaw

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

def fixedMarkedExperiment (D : Finset V) (N t : ℕ) (kap : Finset V → FiniteLaw Ξ) :
    FiniteLaw (Finset V×(Finset V×Ξ)) :=
  (fixedSizeLaw D N).joint (fun U => (fixedSizeLaw U t).joint kap)

theorem fixed_marked_experiment_prob (D : Finset V) (N t : ℕ)
    (kap : Finset V → FiniteLaw Ξ) (E : Finset V → Finset V → Ξ → Prop) :
    (fixedMarkedExperiment D N t kap).prob (fun x => E x.1 x.2.1 x.2.2)=
      (fixedSizeLaw D N).expect (fun U => (fixedSizeLaw U t).expect
        (fun T => (kap T).prob (E U T))) := by
  rw [fixedMarkedExperiment,FiniteLaw.prob_joint]
  simp_rw [FiniteLaw.prob_joint]

/-- All labels and auxiliary classifier randomness are included in the
original sample/mark experiment. The classifier may inspect T and its label,
but the auxiliary law kap depends only on the unlabelled marked set. -/
theorem fixed_marked_counting_failure (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (htD : t<D.card)
    (kap : Finset V → FiniteLaw Ξ) (S : Finset V → Finset V → Ξ → Finset V)
    (hS : ∀ T⊆D, T.card=t → ∀ A⊆T, ∀ xi, S T A xi⊆D)
    (hlabel : ∀ T⊆D, T.card=t → ∀ A⊆T, ∀ xi, S T A xi∩T=A)
    {theta lam err : ℝ} (htheta : 0<theta)
    (hbase : 1-((N-t:ℕ):ℝ)/(D.card-t)+
      ((N-t:ℕ):ℝ)/(D.card-t)*exp theta ≤ exp lam) :
    (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
        (lam/theta)*(S x.2.1 A x.2.2).card+err < ((x.1∩S x.2.1 A x.2.2).card:ℝ)) ≤
      exp (-theta*err)*(1+exp (theta-lam))^t := by
  rw [fixed_marked_experiment_prob D N t kap
    (fun U T xi => ∃ A⊆T, (lam/theta)*(S T A xi).card+err < ((U∩S T A xi).card:ℝ)),
    fixed_marked_sampling_order_reversal D hN ht]
  rw [← (fixedSizeLaw D t).expect_const (exp (-theta*err)*(1+exp (theta-lam))^t)]
  apply FiniteLaw.expect_mono_support
  intro T hT
  obtain ⟨hTD,hTt⟩ := fixed_size_support D T (ht.trans hN) hT
  unfold FiniteLaw.prob
  rw [FiniteLaw.expect_comm]
  change (kap T).expect (fun xi => (fixedSizeLaw (D\T) (N-t)).prob
    (fun R => ∃ A⊆T, (lam/theta)*(S T A xi).card+err < (((T∪R)∩S T A xi).card:ℝ))) ≤ _
  have hpoint (xi : Ξ) := fixed_marked_all_labels_tail D T (fun A => S T A xi) hTD
    hN (by omega : T.card ≤ N) (by omega : T.card<D.card)
    (fun A hA => hS T hTD hTt A hA xi) (fun A hA => hlabel T hTD hTt A hA xi)
    htheta (by simpa only [hTt] using hbase) (err:=err)
  simp only [hTt] at hpoint
  have hh := (kap T).expect_mono hpoint
  simpa only [FiniteLaw.expect_const] using hh

end
end Cycle12
