import Cycle12.DirectParityCompletion12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Gates for the actual completion proof. The reservoir probability
1/32768 pays the current quadratic route capacity and still fits eta. -/
theorem high_center_direct_gates {r n a g : ℝ} (hr : 0≤r)
    (hn : n≤(1+1/2048)*r) (ha : (2:ℝ)^45≤a)
    (halog : (2:ℝ)^26*log n≤a) (hg : 1024*a≤g) (hg2 : a*r/2≤g^2) :
    512≤g ∧
    4*log n+8≤g/524288 ∧
    9437184*n≤(1/32768:ℝ)*((511/1024)*g)^2 ∧
    8192≤(1/32768:ℝ)*((511/1024)*g) ∧
    8192*log n≤(1/32768:ℝ)*((511/1024)*g) ∧
    2112*n≤((1/32768:ℝ)*((511/1024)*g))^2 := by
  have hlin : (2:ℝ)^55≤g := by norm_num at ha ⊢; linarith only [ha,hg]
  have hlog : (2:ℝ)^36*log n≤g := by norm_num at halog ⊢; linarith only [halog,hg]
  have hmul := mul_le_mul_of_nonneg_right ha hr
  have hquad : (2:ℝ)^44*r≤g^2 := by norm_num at hmul ⊢; nlinarith only [hmul,hg2]
  norm_num only [Nat.reducePow] at hlin hlog hquad
  constructor
  · linarith only [hlin]
  constructor
  · linarith only [hlin,hlog]
  constructor
  · nlinarith only [hn,hquad,hr]
  constructor
  · linarith only [hlin]
  constructor
  · linarith only [hlog,hlin]
  · nlinarith only [hn,hquad,hr]

theorem high_center_residue_allowance {r n : ℝ} (hr : 0≤r) (hn : n≤(1+1/2048)*r) :
    (4*(1/32768:ℝ))*n≤Global12.eta*r := by
  have hh := mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤4*(1/32768:ℝ))
  have hcoef : (4*(1/32768:ℝ))*(1+1/2048)≤Global12.eta := by norm_num [Global12.eta]
  have hh' := mul_le_mul_of_nonneg_right hcoef hr
  nlinarith only [hh,hh']

variable {V : Type} [Fintype V]

theorem odd_vertices_card_le_core (G : SimpleGraph V) (U : Finset V)
    (heven : ∀ v,v∉U → Even (G.degree v)) :
    (univ.filter (fun v => ¬Even (G.degree v))).card≤U.card := by
  apply card_le_card
  intro v hv
  by_contra hu
  exact (mem_filter.mp hv).2 (heven v hu)

/-- Complete a core together with its few high exterior centers. All
parity cost is charged to core vertices; the induced residue fits eta
times the core order, including the exterior vertices in the sample. -/
theorem high_center_completion_weight [Nonempty V] (G : SimpleGraph V) (U : Finset V)
    {a g K : ℝ} (hn : 2≤Fintype.card V) (hK : 0≤K)
    (horder : (Fintype.card V:ℝ)≤(1+1/2048)*U.card)
    (ha : (2:ℝ)^45≤a) (halog : (2:ℝ)^26*log (Fintype.card V:ℝ)≤a)
    (hg : 1024*a≤g) (hg2 : a*U.card/2≤g^2)
    (hexp : OAI.ErdosGallai.CutExpansion G g)
    (heven : ∀ v,v∉U → Even (G.degree v))
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ Q : CyclePacking H,Q.weight≤K*m) :
    ∃ P : CyclePacking G,P.weight≤(Fintype.card V:ℝ)+(K*Global12.eta+23/42)*U.card := by
  obtain ⟨hmin,hbank,hscale,hz,hlog,hsquare⟩ := high_center_direct_gates
    (Nat.cast_nonneg U.card) horder ha halog hg hg2
  let prob : unitInterval := ⟨1/32768,by norm_num⟩
  obtain ⟨P,hP⟩ := direct_parity_completion_weight G (p:=prob) hn hmin hexp hbank
    (by norm_num [prob]) (by norm_num [prob]) hK hscale hz hlog hsquare ih
  have hres := high_center_residue_allowance (Nat.cast_nonneg U.card) horder
  have hm := mul_le_mul_of_nonneg_left hres hK
  have ho := Nat.cast_le (α:=ℝ).mpr (odd_vertices_card_le_core G U heven)
  refine ⟨P,?_⟩
  change P.weight≤(1+K*(4*(1/32768:ℝ)))*Fintype.card V+
    (23/42:ℝ)*(univ.filter (fun v => ¬Even (G.degree v))).card at hP
  nlinarith only [hP,hm,ho]

end
end Cycle12
