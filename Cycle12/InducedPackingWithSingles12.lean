import Cycle12.ParitySingletonLedger12
import Cycle12.CompletionInduction12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

theorem induced_edges_eq_inside (G : SimpleGraph V) (U : Finset V) :
    Sym2.map (Subtype.val : U → V) '' (G.induce (U:Set V)).edgeSet=(insideGraph G U).edgeSet := by
  ext e
  constructor
  · rintro ⟨d,hd,hde⟩
    induction d using Sym2.inductionOn with
    | _ x y => exact hde ▸ (show (insideGraph G U).Adj x.val y.val from ⟨hd,x.property,y.property⟩)
  · intro he
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨s((⟨x,he.2.1⟩:U),(⟨y,he.2.2⟩:U)),he.1,rfl⟩

theorem liftInducedPacking_residue_with_outside (G : SimpleGraph V) (U : Finset V)
    (P : CyclePacking (G.induce (U:Set V))) :
    (liftInducedPacking G U P).residue.edgeSet=
      (Sym2.map (Subtype.val : U → V) '' P.residue.edgeSet)∪
        (G.deleteEdges (insideGraph G U).edgeSet).edgeSet := by
  have hi : (insideGraph G U).edgeSet⊆G.edgeSet :=
    edgeSet_mono (show insideGraph G U≤G from fun _ _ h => h.1)
  have hu : Sym2.map (Subtype.val : U → V) '' P.used⊆(insideGraph G U).edgeSet := by
    rw [←induced_edges_eq_inside G U]
    exact Set.image_mono P.used_subset
  rw [CyclePacking.residue,edgeSet_deleteEdges,liftInducedPacking_used,
    CyclePacking.residue,edgeSet_deleteEdges,Set.image_sdiff (Sym2.map.injective Subtype.val_injective),
    induced_edges_eq_inside,edgeSet_deleteEdges]
  ext e
  simp only [Set.mem_sdiff,Set.mem_union]
  constructor
  · rintro ⟨he,hn⟩
    by_cases hx : e∈(insideGraph G U).edgeSet
    · exact Or.inl ⟨hx,hn⟩
    · exact Or.inr ⟨he,hx⟩
  · rintro (⟨he,hn⟩ | ⟨he,hn⟩)
    · exact ⟨hi he,hn⟩
    · exact ⟨he,fun h => hn (hu h)⟩

/-- Induced recursion leaves every outside edge as exactly one singleton;
isolated ambient vertices still have no cost. -/
theorem liftInducedPacking_weight_with_outside (G : SimpleGraph V) (U : Finset V)
    (P : CyclePacking (G.induce (U:Set V))) :
    (liftInducedPacking G U P).weight=P.weight+
      (23/42:ℝ)*(G.deleteEdges (insideGraph G U).edgeSet).edgeSet.ncard := by
  have hd : Disjoint (Sym2.map (Subtype.val : U → V) '' P.residue.edgeSet)
      (G.deleteEdges (insideGraph G U).edgeSet).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he ho
    have hi := Set.image_mono (edgeSet_mono P.residue_le) he
    rw [induced_edges_eq_inside G U] at hi
    rw [edgeSet_deleteEdges] at ho
    exact ho.2 hi
  have hs : (liftInducedPacking G U P).singles=P.singles+
      (G.deleteEdges (insideGraph G U).edgeSet).edgeSet.ncard := by
    rw [CyclePacking.singles,liftInducedPacking_residue_with_outside,Set.ncard_union_eq hd,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    rfl
  change (P.count:ℝ)+(23/42:ℝ)*(liftInducedPacking G U P).singles=_
  rw [hs,Nat.cast_add,CyclePacking.weight]
  ring

/-- Smaller-order induction closes the actual small residue; the only
extra parity cost is paid by original odd vertices outside that residue. -/
theorem parity_completion_induction_step {G : SimpleGraph V} (P : CyclePacking G)
    (U : Finset V) {eta K : ℝ} (heta : eta≤1) (hK : 0≤K)
    (hP : P.count≤Fintype.card V) (hU : (U.card:ℝ)<eta*Fintype.card V)
    (hd : ∀ v,v∉U → P.residue.degree v=if Even (G.degree v) then 0 else 1)
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H,Q.weight≤K*m) :
    ∃ T : CyclePacking G,T.weight≤(1+K*eta)*Fintype.card V+
      (23/42:ℝ)*(univ.filter (fun v => ¬Even (G.degree v))).card := by
  have hsmallR : (U.card:ℝ)<Fintype.card V :=
    hU.trans_le (by simpa only [one_mul] using mul_le_mul_of_nonneg_right heta (Nat.cast_nonneg (Fintype.card V)))
  have hsmall : U.card<Fintype.card V := by exact_mod_cast hsmallR
  have hUc : Fintype.card (U:Set V)=U.card :=
    (Fintype.card_congr (Equiv.refl U)).trans (Fintype.card_coe U)
  obtain ⟨Q,hQ⟩ := packing_weight_of_fin_bound (K:=K) (P.residue.induce (U:Set V))
    (by rw [hUc]; exact ih U.card hsmall)
  rw [hUc] at hQ
  let S := liftInducedPacking P.residue U Q
  refine ⟨P.extend S,?_⟩
  rw [CyclePacking.extend_weight,liftInducedPacking_weight_with_outside]
  have hcount : (P.count:ℝ)≤Fintype.card V := by exact_mod_cast hP
  have hsingle := Nat.cast_le (α:=ℝ).mpr (parity_outside_singletons_le_odd G P.residue U hd)
  have hmul := mul_le_mul_of_nonneg_left hU.le hK
  nlinarith only [hcount,hQ,hsingle,hmul]

end
end Cycle12
