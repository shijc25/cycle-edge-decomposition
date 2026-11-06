import Cycle12.CoverCapacityApplication
import Cycle12.CoverSampleRealClosure
import Cycle12.RationalSamplerCase

namespace Cycle12
open Real Finset SimpleGraph Cycle13 Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_from_capacity_and_sampler (c : CoverCapacityParameters) (hc : c.Valid)
    (a : RatSamplerCase) (ha : a.Sound)
    (hlo : (a.moment.inputs.xl:ℝ) ≤ c.bank.sample.xl)
    (hhi : c.bank.sample.xh ≤ (a.moment.inputs.xh:ℝ))
    (hs0 : (a.moment.inputs.s0:ℝ) ≤ c.bank.sample.s0)
    (hdm : c.bank.dm=(a.degree.dm:ℝ)) (hbeta : c.bank.beta=(a.beta:ℝ)) (hL : c.bank.L=(a.L:ℝ))
    (hloc : c.localCuts=true → ∃ b, a.localBeta=some b ∧ (b:ℝ)=c.routeBeta)
    (G : SimpleGraph V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxl : c.bank.sample.xl ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ c.bank.sample.xh)
    (hs : c.bank.sample.s0 ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet))
    (hbounded : ∀ sh, c.bank.maximumScale=some sh → sOf (Fintype.card V) (Fintype.card G.edgeSet) ≤ sh)
    (hdegree : ∀ v, coverDeleteThreshold (Fintype.card V) (Fintype.card G.edgeSet) ≤ (G.degree v:ℝ))
    (hI : CoverSparseCutIrreducible G) : FineCover G 2 ∧ CoarseCover G 1 := by
  let n : ℝ := Fintype.card V
  let m : ℝ := Fintype.card G.edgeSet
  let x := coverGraphX n m
  let s := sOf n m
  let N := ⌊coverSampleP x*n⌋₊
  let p := (N:ℝ)/n
  let P := p/coverScaleW x
  have hsize := twice_graph_edges_le_order_sq G
  have hn : 0 < n := by dsimp [n]; nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  have hx : 0 < x := cover_graph_x_pos hn hm
  have hspos : 0 < s := by linarith only [hc.bank_valid.sampling.density_lower,hs]
  have hxm : x ≤ 17/250 := hxh.trans hc.bank_valid.sampling.xmax
  have hcoord := cover_graph_coordinates_exact hn hm
  have henv := cover_sampling_box_realizes c.bank.sample hc.bank_valid.sampling
    (p:=p) (P:=P) (k:=N) hx hxl hxh hs hcoord.1 rfl rfl rfl
  have hPl : c.bank.sample.Plo ≤ P := henv.2.2.1
  have hPu : P ≤ c.bank.sample.Pu := henv.2.2.2.1
  have hPw : P*coverScaleW x=p := div_mul_cancel₀ _ (cover_w_pos hx).ne'
  have hpn : p*n=(N:ℝ) := div_mul_cancel₀ _ hn.ne'
  have hrel := cover_scale_relations (P:=P) hx hxm hspos hcoord.1
  have hExp := cover_graph_expansion_scale hn hm hxm
  have hR : 0 < coverScaleR x s := by
    unfold coverScaleR
    positivity [cover_den_pos hx.le hxm,cover_h_pos hx.le,cover_w_pos hx]
  have hz : p*coverGraphExpansion n m=coverScaleZ x s P := by
    apply mul_right_cancel₀ hR.ne'
    calc
      _ = p*(coverGraphExpansion n m*coverScaleR x s) := by ring
      _ = p*n := by rw [hExp]
      _ = (P*coverScaleW x)*n := by rw [hPw]
      _ = coverScaleZ x s P*coverScaleR x s := by nlinarith only [hrel.2.2]
  have hedge : (97/100)*p^2*m=(97/100)*(2*s*(coverRoutingQ x s P)^2) := by
    have hh := cover_routing_edge_identity (P:=P) hx hspos hcoord.1 hcoord.2
    rw [hPw] at hh
    nlinarith only [hh]
  obtain ⟨U,hcard,hgood,hlocal⟩ := ha G hm (hlo.trans hxl) (hxh.trans hhi) (hs0.trans hs) hdegree hI
  have horder : (U.card:ℝ)=coverRoutingOrder x s P := by
    calc
      _ = (N:ℝ) := by rw [hcard]
      _ = (P*coverScaleW x)*n := by rw [hPw,hpn]
      _ = _ := cover_routing_sample_identity hx hcoord.1
  have hgood' : GoodVertexSample G U (c.bank.dm*coverScaleZ x s P)
      (c.bank.beta*coverScaleZ x s P) c.bank.L U.card U.card
      ((97/100)*(2*s*(coverRoutingQ x s P)^2)) (coverGraphBudget n m) := by
    rw [hdm,hbeta,hL,hcard]
    change GoodVertexSample G U ((a.degree.dm:ℝ)*coverScaleZ x s P)
      ((a.beta:ℝ)*coverScaleZ x s P) (a.L:ℝ) N N
      ((97/100)*(2*s*(coverRoutingQ x s P)^2)) (coverGraphBudget n m)
    rw [← hz,← hedge]
    exact hgood
  have hlocal' : c.localCuts=true → LocalSampleCutExpansion G U (c.routeBeta*coverScaleZ x s P) (1/125) := by
    intro he
    obtain ⟨b,hb,hbr⟩ := hloc he
    rw [hb] at hlocal
    simpa only [← hbr,← hz] using hlocal
  obtain ⟨C,hcount,hsingles⟩ := cover_cycles_from_sample c hc G U hx hxl hxh hs hPl hPu hbounded
    hcoord.1 horder hgood' hlocal'
  exact cover_of_sample_cycles_real G U C hm hxm hcard hcount hsingles

end
end Cycle12
