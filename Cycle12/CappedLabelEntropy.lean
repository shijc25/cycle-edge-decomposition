import Cycle12.FixedMinorityUnion

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

/-- Above half the marks every label is charged. Binary entropy alone
would be an invalid upper bound in that range. -/
def cappedLabelEntropy (rho : ℝ) : ℝ :=
  if rho ≤ 1/2 then binEntropy rho else log 2

theorem exp_nat_log_two (t : ℕ) : exp ((t:ℝ)*log 2)=(2:ℝ)^t := by
  rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ) < 2)]

theorem minority_labels_capped_entropy_bound (T : Finset V) {rho : ℝ}
    (hr : 0 < rho) :
    (((T.powerset.filter (fun A => (A.card:ℝ) ≤ rho*T.card)).card):ℝ) ≤
      exp ((T.card:ℝ)*cappedLabelEntropy rho) := by
  by_cases hh : rho ≤ 1/2
  · simpa only [cappedLabelEntropy,if_pos hh] using minority_labels_entropy_bound T hr hh
  · rw [cappedLabelEntropy,if_neg hh,exp_nat_log_two]
    have hcard := card_le_card (filter_subset (fun A : Finset V => (A.card:ℝ) ≤ rho*T.card) T.powerset)
    rw [card_powerset] at hcard
    exact_mod_cast hcard

theorem fixed_marked_capped_minority_bound (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (kap : Finset V → FiniteLaw Ξ)
    (E : Finset V → Finset V → Ξ → Finset V → Prop) {rho eta : ℝ}
    (hr : 0 < rho) (heta : 0 ≤ eta)
    (hpoint : ∀ T⊆D, T.card=t → ∀ xi A, A⊆T → (A.card:ℝ) ≤ rho*t →
      (fixedSizeLaw (D\T) (N-t)).prob (fun R => E (T∪R) T xi A) ≤ eta) :
    (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
      (A.card:ℝ) ≤ rho*t ∧ E x.1 x.2.1 x.2.2 A) ≤
        exp ((t:ℝ)*cappedLabelEntropy rho)*eta := by
  let L := fun (T : Finset V) (_xi : Ξ) => T.powerset.filter (fun A => (A.card:ℝ) ≤ rho*t)
  have hh := fixed_marked_restricted_label_bound D hN ht kap L E heta
    (fun T _ hT _ => by simpa only [L,hT] using minority_labels_capped_entropy_bound T hr)
    (fun T hTD hT xi A hA =>
      hpoint T hTD hT xi A (mem_powerset.mp (mem_filter.mp hA).1) (mem_filter.mp hA).2)
  have he : (fun x : Finset V×(Finset V×Ξ) => ∃ A⊆x.2.1,
      (A.card:ℝ) ≤ rho*t ∧ E x.1 x.2.1 x.2.2 A)=
      (fun x => ∃ A∈L x.2.1 x.2.2, E x.1 x.2.1 x.2.2 A) := by
    funext x
    apply propext
    simp only [L,mem_filter,mem_powerset,exists_prop,and_assoc]
  rwa [he]

end
end Cycle12
