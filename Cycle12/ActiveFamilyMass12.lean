import Cycle12.InjectiveActiveFamily12

namespace Cycle12
open OAI.ErdosGallai.Indexing
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V R B : Type} [Fintype V] [Fintype R] [Fintype B] [DecidableEq V]
  {F : SimpleGraph V} {Y : Finset V} {W : B → Finset V} {U : R → Finset V} {a L : ℝ}

theorem active_batch_mass_le (A : ActiveFamily F Y W U a L) (b : B) :
    (∑ i,((A.vertices b i).card:ℝ)) ≤ (W b).card := by
  have hc : (univ.biUnion (A.vertices b)).card=∑ i,(A.vertices b i).card :=
    Finset.card_biUnion (fun i _ j _ hij => A.disjoint b hij)
  have hs : univ.biUnion (A.vertices b) ⊆ W b := by
    intro v hv
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv
    exact A.subset_batch b i hi
  have hh := card_le_card hs
  rw [hc] at hh
  exact_mod_cast hh

theorem active_batch_count_bound (A : ActiveFamily F Y W U a L) (b : B) :
    L*Fintype.card (A.Index b) ≤ (W b).card := by
  have hl := Finset.sum_le_sum (fun i (_ : i∈(univ:Finset (A.Index b))) => A.large b i)
  have hh := hl.trans (active_batch_mass_le A b)
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_comm] using hh

theorem active_router_count_bound (A : ActiveFamily F Y W U a L)
    (hinj : ∀ b,Function.Injective (A.router b)) (b : B) :
    Fintype.card (A.Index b) ≤ Fintype.card R :=
  Fintype.card_le_of_injective (A.router b) (hinj b)

/-- The deficit is paid by the degree of the whole descendant graph,
not by separate degrees within batches. -/
theorem active_mass_deficit (A : ActiveFamily F Y W U a L) (ha : 0<a) :
    (∑ r,((U r).card:ℝ))-2*(F.edgeFinset.card:ℝ)/a-
      L*Fintype.card B*Fintype.card R ≤ ∑ b,∑ i,((A.vertices b i).card:ℝ) := by
  letI : DecidableEq V := fun x y => Classical.propDecidable (x=y)
  have hb := bad_vertices_degree_bound F Y a
  have hbad : ((Y\goodVertices F Y a).card:ℝ) ≤ 2*(F.edgeFinset.card:ℝ)/a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [mul_comm] using hb
  have hl := A.lower
  linarith

theorem core_count_from_mass {r : ℝ} (hr : 0<r)
    (hlarge : ∀ i,r ≤ ((U i).card:ℝ)) :
    (Fintype.card R:ℝ) ≤ (∑ i,((U i).card:ℝ))/r := by
  apply (le_div_iff₀ hr).mpr
  simpa only [sum_const,card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i∈(univ:Finset R)) => hlarge i)

/-- The two actual finite counts control the discarded small active
sets; no ceiling is charged separately to each retained vertex. -/
theorem active_mass_deficit_with_counts (A : ActiveFamily F Y W U a L)
    (ha : 0<a) (hL : 0 ≤ L) {bCount rCount : ℝ}
    (hb : (Fintype.card B:ℝ) ≤ bCount) (hr : (Fintype.card R:ℝ) ≤ rCount) :
    (∑ r,((U r).card:ℝ))-2*(F.edgeFinset.card:ℝ)/a-L*bCount*rCount ≤
      ∑ b,∑ i,((A.vertices b i).card:ℝ) := by
  have hmul := mul_le_mul hb hr (Nat.cast_nonneg (Fintype.card R))
    ((Nat.cast_nonneg (Fintype.card B)).trans hb)
  have hh := mul_le_mul_of_nonneg_left hmul hL
  have hl := active_mass_deficit A ha
  nlinarith only [hh,hl]

end
end Cycle12
