import Cycle12.Foundations.FiniteProductLaw
import Cycle12.Foundations.FiniteSupport

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Uniform fixed-cardinality sampling. Capping makes the law total;
every exact-size application below proves k ≤ D.card explicitly. -/
def fixedSizeLaw (D : Finset V) (k : ℕ) : FiniteLaw (Finset V) :=
  FiniteLaw.uniformOn (D.powersetCard (min k D.card))
    (powersetCard_nonempty.mpr (min_le_right _ _))

theorem fixed_size_mass (D A : Finset V) {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).mass A =
      if A⊆D ∧ A.card=k then 1/(D.card.choose k:ℝ) else 0 := by
  simp only [fixedSizeLaw,FiniteLaw.uniformOn,min_eq_left hk,mem_powersetCard,
    card_powersetCard]

theorem fixed_size_support (D A : Finset V) {k : ℕ} (hk : k ≤ D.card)
    (hmass : 0<(fixedSizeLaw D k).mass A) : A⊆D ∧ A.card=k := by
  rw [fixed_size_mass D A hk] at hmass
  by_contra h
  simp only [if_neg h] at hmass
  exact lt_irrefl _ hmass

theorem fixed_size_expect (D : Finset V) {k : ℕ} (hk : k ≤ D.card)
    (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect f=(∑ A∈D.powersetCard k, f A)/(D.card.choose k:ℝ) := by
  unfold fixedSizeLaw
  rw [FiniteLaw.uniformOn_expect]
  simp only [min_eq_left hk,card_powersetCard]

theorem fixed_size_probability (D : Finset V) {k : ℕ} (hk : k ≤ D.card)
    (P : Finset V → Prop) :
    (fixedSizeLaw D k).prob P=
      (((D.powersetCard k).filter P).card:ℝ)/(D.card.choose k:ℝ) := by
  unfold FiniteLaw.prob
  rw [fixed_size_expect D hk]
  simp only [sum_boole]

theorem fixed_size_contains_probability (D S : Finset V) {k : ℕ}
    (hk : k ≤ D.card) (hS : S⊆D) (hSk : S.card ≤ k) :
    (fixedSizeLaw D k).prob (fun A => S⊆A)=
      ((D.card-S.card).choose (k-S.card):ℝ)/(D.card.choose k:ℝ) := by
  rw [fixed_size_probability D hk]
  have hh := congrArg (fun n : ℕ => (n:ℝ)/(D.card.choose k:ℝ))
    (card_filter_powersetCard_subset S D k hS hSk)
  convert hh using 1
  congr 2
  apply congrArg Finset.card
  ext A
  simp

/-- Exact count of an intersection level in a uniform fixed-size sample. -/
theorem fixed_size_intersection_count (D B : Finset V) (hB : B⊆D)
    {k j : ℕ} (hjk : j ≤ k) :
    ((D.powersetCard k).filter (fun A => (A∩B).card=j)).card=
      B.card.choose j*(D.card-B.card).choose (k-j) := by
  have he : ((D.powersetCard k).filter (fun A => (A∩B).card=j)).card=
      (B.powersetCard j×ˢ(D\B).powersetCard (k-j)).card := by
    apply card_bij (fun A _ => (A∩B,A\B))
    · intro A hA
      obtain ⟨⟨hAD,hAk⟩,hAj⟩ := (mem_filter.mp hA).imp_left mem_powersetCard.mp
      apply mem_product.mpr
      refine ⟨mem_powersetCard.mpr ⟨inter_subset_right,hAj⟩,
        mem_powersetCard.mpr ⟨sdiff_subset_sdiff_left B hAD,?_⟩⟩
      rw [card_sdiff,inter_comm B A,hAk,hAj]
    · intro A hA C hC hAC
      have hi := congrArg Prod.fst hAC
      have hs := congrArg Prod.snd hAC
      dsimp only at hi hs
      calc
        A = A\B∪A∩B := (sdiff_union_inter A B).symm
        _ = C\B∪C∩B := by rw [hi,hs]
        _ = C := sdiff_union_inter C B
    · rintro ⟨S,T⟩ hST
      obtain ⟨⟨hSB,hSj⟩,hTD,hTk⟩ := (mem_product.mp hST).imp mem_powersetCard.mp mem_powersetCard.mp
      have hdisj : Disjoint S T := by
        apply disjoint_left.mpr
        intro v hvS hvT
        exact (mem_sdiff.mp (hTD hvT)).2 (hSB hvS)
      have hi : (S∪T)∩B=S := by
        ext v
        simp only [mem_inter,mem_union]
        constructor
        · rintro ⟨hvS | hvT,hvB⟩
          · exact hvS
          · exact ((mem_sdiff.mp (hTD hvT)).2 hvB).elim
        · intro hvS
          exact ⟨Or.inl hvS,hSB hvS⟩
      have hs : (S∪T)\B=T := by
        ext v
        simp only [mem_sdiff,mem_union]
        constructor
        · rintro ⟨hvS | hvT,hvB⟩
          · exact (hvB (hSB hvS)).elim
          · exact hvT
        · intro hvT
          exact ⟨Or.inr hvT,(mem_sdiff.mp (hTD hvT)).2⟩
      refine ⟨S∪T,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,?_⟩,?_⟩,?_⟩
      · exact union_subset (hSB.trans hB) (hTD.trans sdiff_subset)
      · rw [card_union_of_disjoint hdisj,hSj,hTk]
        omega
      · rw [hi,hSj]
      · simp only [hi,hs]
  rw [he,card_product,card_powersetCard,card_powersetCard,card_sdiff_of_subset hB]

theorem fixed_size_intersection_probability (D B : Finset V) (hB : B⊆D)
    {k j : ℕ} (hk : k ≤ D.card) (hjk : j ≤ k) :
    (fixedSizeLaw D k).prob (fun A => (A∩B).card=j)=
      (B.card.choose j:ℝ)*((D.card-B.card).choose (k-j):ℝ)/(D.card.choose k:ℝ) := by
  rw [fixed_size_probability D hk]
  have hh := congrArg (fun n : ℕ => (n:ℝ)/(D.card.choose k:ℝ))
    (fixed_size_intersection_count D B hB hjk)
  simp only [Nat.cast_mul] at hh
  convert hh using 1
  congr 2
  apply congrArg Finset.card
  ext A
  simp

end
end Cycle12
