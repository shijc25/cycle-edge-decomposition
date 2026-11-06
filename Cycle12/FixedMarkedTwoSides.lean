import Cycle12.FixedMarkedExperiment

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V Ξ : Type} [Fintype V] [DecidableEq V] [Fintype Ξ]

/-- Both colors are included in the same fixed sample/mark experiment.
Reindexing the second color's label by its complement pays exactly a factor two. -/
theorem fixed_marked_two_sides_counting_failure (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (htD : t<D.card)
    (kap : Finset V → FiniteLaw Ξ) (S : Finset V → Finset V → Ξ → Finset V)
    (hS : ∀ T⊆D, T.card=t → ∀ A⊆T, ∀ xi, S T A xi⊆D)
    (hlabel : ∀ T⊆D, T.card=t → ∀ A⊆T, ∀ xi, S T A xi∩T=A)
    {theta lam err : ℝ} (htheta : 0<theta)
    (hbase : 1-((N-t:ℕ):ℝ)/(D.card-t)+
      ((N-t:ℕ):ℝ)/(D.card-t)*exp theta ≤ exp lam) :
    (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
        (lam/theta)*(S x.2.1 A x.2.2).card+err < ((x.1∩S x.2.1 A x.2.2).card:ℝ) ∨
        (lam/theta)*(D\S x.2.1 A x.2.2).card+err < ((x.1∩(D\S x.2.1 A x.2.2)).card:ℝ)) ≤
      2*exp (-theta*err)*(1+exp (theta-lam))^t := by
  let C := fun T A xi => D\S T (T\A) xi
  have hC : ∀ T⊆D, T.card=t → ∀ A⊆T, ∀ xi, C T A xi⊆D := by
    intro T hT hcard A hA xi
    exact sdiff_subset
  have hClabel : ∀ T⊆D, T.card=t → ∀ A⊆T, ∀ xi, C T A xi∩T=A := by
    intro T hT hcard A hA xi
    have hh := hlabel T hT hcard (T\A) sdiff_subset xi
    change (D\S T (T\A) xi)∩T=A
    ext v
    have hvh : v∈S T (T\A) xi ∧ v∈T ↔ v∈T ∧ v∉A := by
      simpa only [mem_inter,mem_sdiff] using (Finset.ext_iff.mp hh v)
    simp only [mem_inter,mem_sdiff]
    constructor
    · intro hv
      by_contra hvA
      exact hv.1.2 ((hvh.mpr ⟨hv.2,hvA⟩).1)
    · intro hvA
      refine ⟨⟨hT (hA hvA),?_⟩,hA hvA⟩
      intro hvS
      exact (hvh.mp ⟨hvS,hA hvA⟩).2 hvA
  have h₁ := fixed_marked_counting_failure D hN ht htD kap S hS hlabel htheta hbase (err:=err)
  have h₂ := fixed_marked_counting_failure D hN ht htD kap C hC hClabel htheta hbase (err:=err)
  let E₁ := fun x : Finset V×(Finset V×Ξ) => ∃ A⊆x.2.1,
    (lam/theta)*(S x.2.1 A x.2.2).card+err < ((x.1∩S x.2.1 A x.2.2).card:ℝ)
  let E₂ := fun x : Finset V×(Finset V×Ξ) => ∃ A⊆x.2.1,
    (lam/theta)*(C x.2.1 A x.2.2).card+err < ((x.1∩C x.2.1 A x.2.2).card:ℝ)
  have hm : (fixedMarkedExperiment D N t kap).prob (fun x => ∃ A⊆x.2.1,
        (lam/theta)*(S x.2.1 A x.2.2).card+err < ((x.1∩S x.2.1 A x.2.2).card:ℝ) ∨
        (lam/theta)*(D\S x.2.1 A x.2.2).card+err < ((x.1∩(D\S x.2.1 A x.2.2)).card:ℝ)) ≤
      (fixedMarkedExperiment D N t kap).prob (fun x => E₁ x ∨ E₂ x) := by
    apply FiniteLaw.prob_mono
    rintro x ⟨A,hA,hbad | hbad⟩
    · exact Or.inl ⟨A,hA,hbad⟩
    · apply Or.inr
      refine ⟨x.2.1\A,sdiff_subset,?_⟩
      simpa only [C,Finset.sdiff_sdiff_eq_self hA] using hbad
  have hu := (fixedMarkedExperiment D N t kap).prob_union_le E₁ E₂
  change (fixedMarkedExperiment D N t kap).prob E₁ ≤ _ at h₁
  change (fixedMarkedExperiment D N t kap).prob E₂ ≤ _ at h₂
  nlinarith only [hm,hu,h₁,h₂]

end
end Cycle12
