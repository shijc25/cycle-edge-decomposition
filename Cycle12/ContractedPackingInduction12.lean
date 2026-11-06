import Cycle12.CompletionInduction12
import Cycle12.Foundations.DisjointBlockContraction

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Full-block contraction saves all but one vertex per active block.
The packing comes from an explicitly smaller-order induction call. -/
theorem contracted_packing_induction (H : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    {n : ℕ} {L K : ℝ} (hn : Fintype.card V<n) (hL : 1≤L) (hK : 0≤K)
    (hsize : ∀ i, L≤((A i).card:ℝ))
    (ih : ∀ m, m<n → ∀ G : SimpleGraph (Fin m),
      ∃ P : CyclePacking G, P.weight≤K*m) :
    ∃ P : CyclePacking (H.map (contractVertex A)),
      P.weight≤K*((Fintype.card V:ℝ)-(1-1/L)*(∑ i,((A i).card:ℝ))) := by
  have hL0 : 0<L := by linarith only [hL]
  have hs := contracted_order_saving A hd hL0 hsize
  have hcoef : 0≤1-1/L := by
    have hh : 1/L≤(1:ℝ) := (div_le_iff₀ hL0).mpr (by simpa using hL)
    linarith only [hh]
  have horderR : (Fintype.card (ContractedVertices A):ℝ)≤Fintype.card V := by
    have hp : 0≤(1-1/L)*(∑ i,((A i).card:ℝ)) :=
      mul_nonneg hcoef (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (α:=ℝ) (A i).card))
    linarith only [hs,hp]
  have horder : Fintype.card (ContractedVertices A)≤Fintype.card V := by exact_mod_cast horderR
  obtain ⟨P,hP⟩ := packing_weight_of_fin_bound (H.map (contractVertex A))
    (ih _ (horder.trans_lt hn))
  exact ⟨P,hP.trans (mul_le_mul_of_nonneg_left hs hK)⟩

/-- The exact one-vertex cost per block can also be kept, instead of
replacing it by a uniform reciprocal loss. -/
theorem contracted_packing_exact_order (H : SimpleGraph V) (A : I → Finset V)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hne : ∀ i, (A i).Nonempty) {n : ℕ} {K : ℝ} (hn : Fintype.card V<n)
    (ih : ∀ m, m<n → ∀ G : SimpleGraph (Fin m),
      ∃ P : CyclePacking G, P.weight≤K*m) :
    ∃ P : CyclePacking (H.map (contractVertex A)),
      P.weight≤K*((Fintype.card V:ℝ)-(∑ i,((A i).card:ℝ))+Fintype.card I) := by
  have hc := Fintype.card_le_of_surjective (contractVertex A) (contractVertex_surjective A hd hne)
  obtain ⟨P,hP⟩ := packing_weight_of_fin_bound (H.map (contractVertex A))
    (ih _ (hc.trans_lt hn))
  have he : (Fintype.card (ContractedVertices A):ℝ)+(∑ i,((A i).card:ℝ))=
      Fintype.card V+Fintype.card I := by exact_mod_cast contracted_order_identity A hd
  have he' : (Fintype.card (ContractedVertices A):ℝ)=
      (Fintype.card V:ℝ)-(∑ i,((A i).card:ℝ))+Fintype.card I := by linarith only [he]
  exact ⟨P,he' ▸ hP⟩

end
end Cycle12
