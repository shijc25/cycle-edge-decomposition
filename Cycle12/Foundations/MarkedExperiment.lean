import Cycle12.Foundations.FiniteJointLaw
import Cycle12.Foundations.MarkedSamplingCoupling

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type*} [Fintype V] [DecidableEq V] [Fintype Ξ]

def markedExperiment (p q : unitInterval) (κ : Finset V→FiniteLaw Ξ) :
    FiniteLaw (Finset V×(Finset V×Ξ)) :=
  (bernoulliSubset p).joint (fun U => (subsetBernoulli U q).joint κ)

theorem markedExperiment_prob (p q : unitInterval) (κ : Finset V→FiniteLaw Ξ)
    (E : Finset V→Finset V→Ξ→Prop) :
    (markedExperiment p q κ).prob (fun x => E x.1 x.2.1 x.2.2)=
      (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
        (κ T).prob (E U T))) := by
  rw [markedExperiment,FiniteLaw.prob_joint]
  simp_rw [FiniteLaw.prob_joint]

theorem marked_three_event_bound (p q : unitInterval) (κ : Finset V→FiniteLaw Ξ)
    (W E₁ E₂ E₃ : Finset V→Finset V→Ξ→Prop) {b₁ b₂ b₃ : ℝ}
    (hW : ∀ U T ξ, W U T ξ → E₁ U T ξ ∨ E₂ U T ξ ∨ E₃ U T ξ)
    (h₁ : (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (E₁ U T))) ≤ b₁)
    (h₂ : (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (E₂ U T))) ≤ b₂)
    (h₃ : (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (E₃ U T))) ≤ b₃) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (W U T))) ≤ b₁+b₂+b₃ := by
  rw [← markedExperiment_prob] at h₁ h₂ h₃ ⊢
  let μ := markedExperiment p q κ
  have hmono := μ.prob_mono (E:=fun x => W x.1 x.2.1 x.2.2)
    (F:=fun x => E₁ x.1 x.2.1 x.2.2 ∨ E₂ x.1 x.2.1 x.2.2 ∨ E₃ x.1 x.2.1 x.2.2)
    (fun x hx => hW x.1 x.2.1 x.2.2 hx)
  have hu₁ := μ.prob_union_le (fun x => E₁ x.1 x.2.1 x.2.2)
    (fun x => E₂ x.1 x.2.1 x.2.2 ∨ E₃ x.1 x.2.1 x.2.2)
  have hu₂ := μ.prob_union_le (fun x => E₂ x.1 x.2.1 x.2.2)
    (fun x => E₃ x.1 x.2.1 x.2.2)
  change μ.prob _ ≤ b₁ at h₁
  change μ.prob _ ≤ b₂ at h₂
  change μ.prob _ ≤ b₃ at h₃
  change μ.prob _ ≤ _
  linarith

theorem marked_two_event_bound (p q : unitInterval) (κ : Finset V→FiniteLaw Ξ)
    (W E₁ E₂ : Finset V→Finset V→Ξ→Prop) {b₁ b₂ : ℝ}
    (hW : ∀ U T ξ, W U T ξ → E₁ U T ξ ∨ E₂ U T ξ)
    (h₁ : (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (E₁ U T))) ≤ b₁)
    (h₂ : (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (E₂ U T))) ≤ b₂) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (κ T).prob (W U T))) ≤ b₁+b₂ := by
  have hh := marked_three_event_bound p q κ W E₁ E₂ (fun _ _ _ => False) (b₃:=0)
    (fun U T ξ h => by rcases hW U T ξ h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
    h₁ h₂ (by simp only [FiniteLaw.prob,ite_false,FiniteLaw.expect_const,le_refl])
  simpa only [add_zero] using hh

end
end Cycle13
