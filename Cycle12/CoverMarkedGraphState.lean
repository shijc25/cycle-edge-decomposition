import Cycle12.RationalMarkedGeometry
import Cycle12.CoverGraphCoordinates

namespace Cycle12
open Finset SimpleGraph Cycle13
open Cycle13.MixedSample
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Coordinates of one genuine floor sample and its ceil-sized marked set.
All scale inequalities are facts about this graph and these integers. -/
structure CoverMarkedGraphState (g : RatMarkedGeometry) (G : SimpleGraph V) where
  N : ℕ
  t : ℕ
  R : ℝ
  z : ℝ
  p : ℝ
  residual : unitInterval
  order_pos : (0:ℝ) < Fintype.card V
  mass_pos : (0:ℝ) < Fintype.card G.edgeSet
  x_lower : (g.inputs.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet)
  x_upper : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (g.inputs.xh:ℝ)
  sample_floor : N=⌊coverSampleP (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card V:ℝ)⌋₊
  mark_ceil : t=⌈(g.qmark:ℝ)*R⌉₊
  sample_fraction : p=(N:ℝ)/Fintype.card V
  residual_fraction : (residual:ℝ)=((N-t:ℕ):ℝ)/(Fintype.card V-t:ℕ)
  expansion_identity : coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)=z/p
  order_identity : (Fintype.card V:ℝ)=R*(z/p)
  sample_identity : (N:ℝ)=z*R
  sample_le_order : N ≤ Fintype.card V
  sample_twice_le : 2*N ≤ Fintype.card V
  mark_lt_sample : t < N
  scale_pos : 0 < R
  scale_lower : (g.Rlo:ℝ) ≤ R
  z_pos : 0 < z
  z_lower : (g.zlo:ℝ) ≤ z
  scale_ratio : (g.Dlo:ℝ)*R ≤ z
  weight_lower : (g.Wlo:ℝ) ≤ p*z
  fraction_pos : 0 < p
  fraction_lower : (g.inputs.pl:ℝ) ≤ p
  fraction_upper : p ≤ (g.pmax:ℝ)
  fraction_half : p < 1/2
  mark_lower : (g.qmark:ℝ)*R ≤ (t:ℝ)
  mark_upper : (t:ℝ) ≤ (g.M:ℝ)*R
  residual_lower : (g.ps:ℝ)*p ≤ (residual:ℝ)
  residual_pos : 0 < (residual:ℝ)
  residual_half : (residual:ℝ) ≤ 1/2
  residual_mean : ((Fintype.card V-t:ℕ):ℝ)*(residual:ℝ)=((N-t:ℕ):ℝ)

def cover_marked_graph_state (g : RatMarkedGeometry) (G : SimpleGraph V)
    (hi : g.inputs.Valid) (hg : g.Valid) (hsound : g.Sound)
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hxl : (g.inputs.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (g.inputs.xh:ℝ))
    (hs : (g.inputs.s0:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet)) :
    CoverMarkedGraphState g G := by
  let n : ℕ := Fintype.card V
  let x : ℝ := coverGraphX (Fintype.card V) (Fintype.card G.edgeSet)
  let s : ℝ := sOf (Fintype.card V) (Fintype.card G.edgeSet)
  let N : ℕ := ⌊coverSampleP x*(n:ℝ)⌋₊
  let p : ℝ := (N:ℝ)/n
  let P : ℝ := p/coverScaleW x
  let R : ℝ := coverScaleR x s
  let z : ℝ := coverScaleZ x s P
  let t : ℕ := ⌈(g.qmark:ℝ)*R⌉₊
  have hx : 0 < x := cover_graph_x_pos hn hm
  have horder : (n:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3 := (cover_graph_coordinates_exact hn hm).1
  obtain ⟨hRl,hzl,hD,hW,hN,hNhalf,hpl,hpu,hp,hphalf,ht,hq,hM,hvote,hps,hres,hhalf⟩ :=
    hsound hx hxl hxh hs horder (show N=⌊coverSampleP x*(n:ℝ)⌋₊ from rfl)
  have hRp : 0 < R := (show (0:ℝ) < (g.Rlo:ℝ) by exact_mod_cast hg.1).trans_le hRl
  have hzp : 0 < z := (show (0:ℝ) < (g.zlo:ℝ) by exact_mod_cast hg.2.1).trans_le hzl
  have hbox := (rat_moment_certificate_valid g.inputs hi).sampling
  have hsmin : (1:ℝ) ≤ (g.inputs.s0:ℝ) := hbox.density_lower
  have hsp : 0 < s := by linarith only [hsmin,hs]
  have hxmax : x ≤ 17/250 := hxh.trans hbox.xmax
  have hNZ : (N:ℝ)=z*R := cover_sample_order_eq_scale hn hx hxmax hsp horder (p:=p) rfl (P:=P) rfl
  have hn0 : (n:ℝ) ≠ 0 := hn.ne'
  have hp0 : p ≠ 0 := hp.ne'
  have hpn : p*(n:ℝ)=(N:ℝ) := by dsimp only [p]; exact div_mul_cancel₀ _ hn0
  have hncoord : (n:ℝ)=R*(z/p) := by
    apply (mul_right_cancel₀ hp.ne')
    have hid : (R*(z/p))*p=z*R := by rw [mul_assoc,div_mul_cancel₀ _ hp0,mul_comm]
    rw [hid,mul_comm (n:ℝ) p,hpn,hNZ]
  have he : coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)=z/p := by
    apply (mul_right_cancel₀ hRp.ne')
    have hh := cover_graph_expansion_scale hn hm hxmax
    change coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)*R=(n:ℝ) at hh
    rw [hh,hncoord,mul_comm]
  have hscales := cover_scale_relations (P:=P) hx hxmax hsp horder
  have hDz : (g.Dlo:ℝ)*R ≤ z := (le_div_iff₀ hRp).mp (hD.trans_eq hscales.1.symm)
  have hWz : (g.Wlo:ℝ) ≤ p*z := by
    have hpw : coverScaleW x*P=p := by dsimp only [P]; exact mul_div_cancel₀ _ (cover_w_pos hx).ne'
    have hh := hscales.2.1
    rw [hpw] at hh
    exact hW.trans_eq hh.symm
  let pres : unitInterval := ⟨((N-t:ℕ):ℝ)/(n-t:ℕ),hres.le,hhalf.trans (by norm_num)⟩
  have hreslo : (g.ps:ℝ)*p ≤ (pres:ℝ) := (le_div_iff₀ hp).mp hps
  have htD : t < n := ht.trans_le hN
  have hnt : (0:ℝ) < (n-t:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt htD
  have hmean : ((n-t:ℕ):ℝ)*(pres:ℝ)=((N-t:ℕ):ℝ) := by
    dsimp only [pres]
    field_simp
  exact {
    N:=N,t:=t,R:=R,z:=z,p:=p,residual:=pres,
    order_pos:=hn,mass_pos:=hm,x_lower:=hxl,x_upper:=hxh,
    sample_floor:=rfl,mark_ceil:=rfl,sample_fraction:=rfl,residual_fraction:=rfl,
    expansion_identity:=he,order_identity:=hncoord,sample_identity:=hNZ,
    sample_le_order:=hN,sample_twice_le:=hNhalf,mark_lt_sample:=ht,
    scale_pos:=hRp,scale_lower:=hRl,z_pos:=hzp,z_lower:=hzl,scale_ratio:=hDz,weight_lower:=hWz,
    fraction_pos:=hp,fraction_lower:=hpl,fraction_upper:=hpu,fraction_half:=hphalf,
    mark_lower:=(le_div_iff₀ hRp).mp hq,mark_upper:=(div_le_iff₀ hRp).mp hM,
    residual_lower:=hreslo,residual_pos:=hres,residual_half:=hhalf,residual_mean:=hmean }

end
end Cycle12
