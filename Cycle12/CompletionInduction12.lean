import Cycle12.GlobalEulerianCompletion12
import Cycle12.InducedPackingLift12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Relabeling preserves the exact weighted packing cost. -/
theorem packing_weight_of_fin_bound (H : SimpleGraph V) {K : ℝ}
    (hfin : ∀ J : SimpleGraph (Fin (Fintype.card V)),
      ∃ P : CyclePacking J, P.weight ≤ K*Fintype.card V) :
    ∃ P : CyclePacking H, P.weight ≤ K*Fintype.card V := by
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  obtain ⟨P,hP⟩ := hfin (H.comap e)
  let Q := P.mapIso (SimpleGraph.Iso.comap e H)
  have hc : (Q.cost:ℝ) = P.cost := by
    exact_mod_cast CyclePacking.cost_mapIso P (SimpleGraph.Iso.comap e H)
  simp only [CyclePacking.cost_eq_weight] at hc
  exact ⟨Q,by linarith only [hc,hP]⟩

/-- Strict residue shrinkage justifies the smaller-order induction call;
isolated padding contributes no cycle or singleton cost. -/
theorem completion_induction_step {G : SimpleGraph V} (P : CyclePacking G)
    (U : Finset V) {eta K : ℝ} (heta : eta ≤ 1) (hK : 0 ≤ K)
    (hP : P.count ≤ Fintype.card V) (hUcard : (U.card:ℝ) < eta*Fintype.card V)
    (hU : ∀ x y, P.residue.Adj x y → x ∈ U ∧ y ∈ U)
    (ih : ∀ m, m < Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight ≤ K*m) :
    ∃ Q : CyclePacking G, Q.weight ≤ (1+K*eta)*Fintype.card V := by
  have hsmallR : (U.card:ℝ) < Fintype.card V :=
    hUcard.trans_le (by simpa only [one_mul] using mul_le_mul_of_nonneg_right heta (Nat.cast_nonneg (Fintype.card V)))
  have hsmall : U.card < Fintype.card V := by exact_mod_cast hsmallR
  have hUc : Fintype.card (U:Set V) = U.card :=
    (Fintype.card_congr (Equiv.refl U)).trans (Fintype.card_coe U)
  obtain ⟨S,hS⟩ := packing_weight_of_fin_bound (K:=K) (P.residue.induce (U:Set V))
    (by rw [hUc]; exact ih U.card hsmall)
  rw [hUc] at hS
  obtain ⟨Q,hQ⟩ := completion_weight_from_induced (K:=K) (n:=(Fintype.card V:ℝ)) P U hU
    (by exact_mod_cast hP) ⟨S,hS⟩
  refine ⟨Q,hQ.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hUcard.le hK
  nlinarith only [hh]

namespace Global12

/-- The terminal Eulerian core budget is now justified by the actual
sampling/closing construction and an explicitly smaller-order IH. -/
theorem even_core_completion_weight [Nonempty V] (G : SimpleGraph V) {w : ℝ}
    (hn : 2 ≤ Fintype.card V) (hw : w0 ≤ w)
    (horder : (Fintype.card V:ℝ) ≤ (2:ℝ)^(rho*w))
    (hexp : OAI.ErdosGallai.CutExpansion G ((1023/1024)*(2:ℝ)^(s*w)))
    (heven : ∀ v, Even (G.degree v))
    (ih : ∀ m, m < Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H, Q.weight ≤ C*m) :
    ∃ Q : CyclePacking G, Q.weight ≤ (1+C*eta)*Fintype.card V := by
  obtain ⟨U,hU,P,hP,hres⟩ := even_completion_at_scale G hn hw horder hexp heven
  exact completion_induction_step P U (by norm_num [eta]) (by norm_num [C]) hP hU hres ih

end Global12
end
end Cycle12
