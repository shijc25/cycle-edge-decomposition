import Cycle12.Foundations.MarkedLabelOriginal

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def complementaryLabels (T : Finset V) (A : {A : Finset V // A⊆T}) :
    {A : Finset V // A⊆T} := ⟨T\A.val,sdiff_subset⟩

theorem complementaryLabels_involutive (T : Finset V) (A : {A : Finset V // A⊆T}) :
    complementaryLabels T (complementaryLabels T A)=A := by
  apply Subtype.ext
  exact Finset.sdiff_sdiff_eq_self A.property

def partitionSide {Ξ : Type*}
    (side : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→Finset V)
    (i : Bool) (T : Finset V) (ξ : Ξ) (A : {A : Finset V // A⊆T}) : Finset V :=
  if i then side T ξ A else (side T ξ (complementaryLabels T A))ᶜ

theorem partitionSide_marked {Ξ : Type*}
    (side : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→Finset V)
    (hmark : ∀ T ξ A, side T ξ A∩T=A.val) :
    ∀ i T ξ A, partitionSide side i T ξ A∩T=A.val := by
  intro i T ξ A
  cases i
  · simp only [partitionSide,Bool.false_eq_true,ite_false]
    have hh := hmark T ξ (complementaryLabels T A)
    ext v
    have hv := Finset.ext_iff.mp hh v
    simp only [mem_inter,complementaryLabels,mem_sdiff] at hv
    simp only [mem_inter,mem_compl]
    have ha := @A.property v
    tauto
  · exact hmark T ξ A

theorem marked_partition_mgf (p q : unitInterval) (hpq : (p:ℝ)*(q:ℝ) < 1)
    {Ξ : Type*} [Fintype Ξ] (κ : Finset V→FiniteLaw Ξ)
    (side : ∀ T : Finset V, Ξ→{A : Finset V // A⊆T}→Finset V)
    (hmark : ∀ T ξ A, side T ξ A∩T=A.val)
    (a b θ : ℝ) (hθ : 0 < θ) (hslope : exp θ-1 ≤ θ*a) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T => (κ T).prob
      (fun ξ => ∃ A, a*(p:ℝ)*(side T ξ A).card+b < ((U∩side T ξ A).card:ℝ) ∨
        a*(p:ℝ)*(side T ξ A)ᶜ.card+b < ((U\side T ξ A).card:ℝ)))) ≤
      2*exp (-θ*b+(p:ℝ)*(q:ℝ)*exp (θ*(1-a*(p:ℝ)))*Fintype.card V) := by
  apply le_trans _ (label_aware_mgf_two_families p q hpq κ (partitionSide side)
    (partitionSide_marked side hmark) a b θ hθ hslope)
  apply FiniteLaw.expect_mono
  intro U
  apply FiniteLaw.expect_mono
  intro T
  apply FiniteLaw.prob_mono
  rintro ξ ⟨A,hA | hA⟩
  · exact ⟨true,A,hA⟩
  · refine ⟨false,complementaryLabels T A,?_⟩
    have he : U∩(side T ξ A)ᶜ=U\side T ξ A := by ext v; simp
    simpa only [partitionSide,Bool.false_eq_true,ite_false,
      complementaryLabels_involutive,he] using hA

end
end Cycle13
