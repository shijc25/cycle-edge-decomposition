import Cycle12.FixedMarkedCoupling

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weighted fiber counting, retaining the actual chosen intersection.
It proves conditional uniformity without conditioning on a successful cut. -/
theorem fixed_intersection_fiber_sum (D B : Finset V) (hB : B⊆D)
    {k j : ℕ} (hjk : j ≤ k) (f : Finset V → ℝ) :
    (∑ T∈(D.powersetCard k).filter (fun T => (T∩B).card=j), f (T∩B))=
      ((D.card-B.card).choose (k-j):ℝ)*(∑ S∈B.powersetCard j, f S) := by
  have he : (∑ T∈(D.powersetCard k).filter (fun T => (T∩B).card=j), f (T∩B))=
      ∑ P∈B.powersetCard j×ˢ(D\B).powersetCard (k-j), f P.1 := by
    apply sum_bij (fun T _ => (T∩B,T\B))
    · intro T hT
      obtain ⟨⟨hTD,hTk⟩,hTj⟩ := (mem_filter.mp hT).imp_left mem_powersetCard.mp
      apply mem_product.mpr
      refine ⟨mem_powersetCard.mpr ⟨inter_subset_right,hTj⟩,
        mem_powersetCard.mpr ⟨sdiff_subset_sdiff_left B hTD,?_⟩⟩
      rw [card_sdiff,inter_comm B T,hTk,hTj]
    · intro T hT R hR hTR
      have hi := congrArg Prod.fst hTR
      have hs := congrArg Prod.snd hTR
      dsimp only at hi hs
      calc
        T = T\B∪T∩B := (sdiff_union_inter T B).symm
        _ = R\B∪R∩B := by rw [hi,hs]
        _ = R := sdiff_union_inter R B
    · rintro ⟨S,R⟩ hSR
      obtain ⟨⟨hSB,hSj⟩,hRD,hRk⟩ :=
        (mem_product.mp hSR).imp mem_powersetCard.mp mem_powersetCard.mp
      have hdisj : Disjoint S R := by
        apply disjoint_left.mpr
        intro v hvS hvR
        exact (mem_sdiff.mp (hRD hvR)).2 (hSB hvS)
      have hi : (S∪R)∩B=S := by
        ext v
        simp only [mem_inter,mem_union]
        constructor
        · rintro ⟨hvS | hvR,hvB⟩
          · exact hvS
          · exact ((mem_sdiff.mp (hRD hvR)).2 hvB).elim
        · intro hvS
          exact ⟨Or.inl hvS,hSB hvS⟩
      have hs : (S∪R)\B=R := by
        ext v
        simp only [mem_sdiff,mem_union]
        constructor
        · rintro ⟨hvS | hvR,hvB⟩
          · exact (hvB (hSB hvS)).elim
          · exact hvR
        · intro hvR
          exact ⟨Or.inr hvR,(mem_sdiff.mp (hRD hvR)).2⟩
      refine ⟨S∪R,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,?_⟩,?_⟩,?_⟩
      · exact union_subset (hSB.trans hB) (hRD.trans sdiff_subset)
      · rw [card_union_of_disjoint hdisj,hSj,hRk]
        omega
      · rw [hi,hSj]
      · simp only [hi,hs]
    · intro T _
      rfl
  rw [he,sum_product]
  simp only [sum_const,nsmul_eq_mul,card_powersetCard,card_sdiff_of_subset hB,← mul_sum]

theorem fixed_intersection_conditioned_expect (D B : Finset V) (hB : B⊆D)
    {k j : ℕ} (hk : k ≤ D.card) (hjk : j ≤ k) (hjB : j ≤ B.card)
    (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect (fun T => if (T∩B).card=j then f (T∩B) else 0)=
      (fixedSizeLaw D k).prob (fun T => (T∩B).card=j)*(fixedSizeLaw B j).expect f := by
  rw [fixed_size_expect D hk,← sum_filter,
    fixed_intersection_fiber_sum D B hB hjk f,
    fixed_size_intersection_probability D B hB hk hjk,fixed_size_expect B hjB]
  have hchoose : (B.card.choose j:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hjB).ne'
  field_simp

/-- Uniform subsampling followed by another uniform subsampling has the
same marginal as sampling the final size directly. -/
theorem fixed_subsample_expect (D : Finset V) {k j : ℕ}
    (hk : k ≤ D.card) (hj : j ≤ k) (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect (fun T => (fixedSizeLaw T j).expect f)=
      (fixedSizeLaw D j).expect f := by
  have hh := fixed_marked_sampling_order_reversal D hk hj (fun _ S => f S)
  simpa only [FiniteLaw.expect_const] using hh

/-- Conditional on the number of marked neighbors, a uniformly selected
subsample is uniform in the original neighbor set. The event is only J=j. -/
theorem fixed_intersection_subsample_expect (D B : Finset V) (hB : B⊆D)
    {k j r : ℕ} (hk : k ≤ D.card) (hjk : j ≤ k) (hjB : j ≤ B.card)
    (hrj : r ≤ j) (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect (fun T => if (T∩B).card=j then
        (fixedSizeLaw (T∩B) r).expect f else 0)=
      (fixedSizeLaw D k).prob (fun T => (T∩B).card=j)*(fixedSizeLaw B r).expect f := by
  rw [fixed_intersection_conditioned_expect D B hB hk hjk hjB (fun S => (fixedSizeLaw S r).expect f),
    fixed_subsample_expect B hjB hrj f]

end
end Cycle12
