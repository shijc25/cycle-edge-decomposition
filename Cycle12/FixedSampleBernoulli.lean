import Cycle12.RealRootBernoulliFactors
import Cycle12.FiniteCountPolynomial
import Cycle12.FixedSampleMean

namespace Cycle12
open Polynomial Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

theorem bernoulli_polynomial_map (p : ℝ) :
    (realBernoulliPolynomial p).map Complex.ofRealHom=bernoulliPolynomial p := by
  simp [realBernoulliPolynomial,bernoulliPolynomial]

theorem bernoulli_list_map (l : List ℝ) :
    (bernoulliListPGF l).map Complex.ofRealHom=(l.map bernoulliPolynomial).prod := by
  induction l with
  | nil => simp
  | cons p l ih => simp [bernoulli_polynomial_map,ih]

theorem hypergeom_exists_bernoulli_list (d b t : ℕ) (ht : t ≤ d+b) :
    ∃ l : List ℝ, (∀ p∈l, 0 ≤ p ∧ p ≤ 1) ∧
      normalizedHypergeom d b t=(bernoulliListPGF l).map Complex.ofRealHom := by
  let P := normalizedHypergeom d b t
  let l := P.roots.toList.map rootBernoulliParameter
  obtain ⟨hf,hb⟩ := hypergeom_bernoulli_factorization d b t ht
  refine ⟨l,?_,?_⟩
  · intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    exact ⟨(hb r (Multiset.mem_toList.mp hr)).1.le,(hb r (Multiset.mem_toList.mp hr)).2⟩
  · rw [bernoulli_list_map]
    change P=(List.map bernoulliPolynomial (P.roots.toList.map rootBernoulliParameter)).prod
    rw [List.map_map,Multiset.prod_map_toList]
    exact hf

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Bernoulli representation of the actual intersection distribution, with
its total parameter exactly identified with the fixed-sample mean. -/
theorem fixed_sample_exists_bernoulli_list (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) :
    ∃ l : List ℝ, (∀ p∈l, 0 ≤ p ∧ p ≤ 1) ∧
      finiteCountPGF (fixedSizeLaw D k) (fun A => (A∩B).card)=bernoulliListPGF l ∧
      l.sum=(k:ℝ)*B.card/D.card := by
  have hn : B.card+(D.card-B.card)=D.card := Nat.add_sub_of_le (card_le_card hB)
  obtain ⟨l,hl,hpoly⟩ := hypergeom_exists_bernoulli_list B.card (D.card-B.card) k (by rwa [hn])
  have heq : finiteCountPGF (fixedSizeLaw D k) (fun A => (A∩B).card)=bernoulliListPGF l := by
    ext j
    have hh := congrArg (fun P : Polynomial ℂ => P.coeff j) hpoly
    rw [fixed_size_hypergeom_coeff D B hB hk j,coeff_map] at hh
    rw [finite_count_coeff]
    simpa using congrArg Complex.re hh
  refine ⟨l,hl,heq,?_⟩
  have hm := congrArg (fun P : Polynomial ℝ => P.derivative.eval 1) heq
  rw [finite_count_derivative_mean,bernoulli_list_derivative_mean,
    fixed_sample_count_mean D B hB hk] at hm
  exact hm.symm

end
end Cycle12
