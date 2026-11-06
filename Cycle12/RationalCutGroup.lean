import Cycle12.RationalCutCell
import Cycle12.RationalMarkedGeometry

namespace Cycle12
open Finset SimpleGraph Cycle13 Real

structure RatCutGroup where
  geometry : RatMarkedGeometry
  population : RatPopulationCertificate
  cells : List RatCutCellCertificate
  lower : ℚ
  upper : Option ℚ
  cap : ℚ
  exponent : ℚ
  entropyBound : Option ℚ
  labelRho : Option ℚ

def RatCutGroup.interval (g : RatCutGroup) : RatSideInterval := ⟨g.lower,g.upper⟩

def RatCutGroup.CellMatches (g : RatCutGroup) (c : RatCutCellCertificate) : Prop :=
  c.region.Rlo=g.geometry.Rlo ∧ c.region.cap=g.cap ∧ c.exponent=g.exponent ∧
  c.region.bin.residual.retention.xl=g.geometry.inputs.xl ∧
  c.region.bin.residual.retention.xh=g.geometry.inputs.xh ∧
  c.region.bin.residual.M=g.geometry.M ∧ c.region.bin.residual.pmax=g.geometry.pmax ∧
  c.region.bin.residual.Dlo=g.geometry.Dlo ∧ c.region.bin.residual.zlo=g.geometry.zlo ∧
  c.region.bin.ps=g.geometry.ps ∧
  (match g.entropyBound with | none => True | some e => c.entropy.bound=e) ∧
  (match g.labelRho with | none => True | some r => c.entropy.rho=r)

instance instDecidableRatCutGroupCellMatches (g : RatCutGroup) (c : RatCutCellCertificate) :
    Decidable (g.CellMatches c) := by
  unfold RatCutGroup.CellMatches
  cases g.entropyBound <;> cases g.labelRho <;> infer_instance

def RatCutGroup.NumericValid (g : RatCutGroup) : Prop :=
  0 < g.lower ∧ g.population.nu ≤ g.lower ∧
  (match g.upper with
    | none => ratRayChain g.lower (g.cells.map (fun c => c.region.interval))
    | some r => ratClosedChain r g.lower (g.cells.map (fun c => c.region.interval))) ∧
  ∀ c∈g.cells, g.CellMatches c

instance instDecidableRatCutGroupNumeric (g : RatCutGroup) : Decidable g.NumericValid := by
  unfold RatCutGroup.NumericValid
  cases g.upper <;> infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

theorem rat_cut_group_covers (g : RatCutGroup) (hc : g.NumericValid)
    {x : ℝ} (hx : g.interval.Contains x) : ∃ c∈g.cells, c.region.interval.Contains x := by
  have hcover := hc.2.2.1
  have h : ∃ a∈g.cells.map (fun c => c.region.interval), a.Contains x := by
    cases he : g.upper with
    | none =>
      simp only [he] at hcover
      exact rat_ray_chain_covers hcover hx.1
    | some r =>
      simp only [he] at hcover
      exact rat_closed_chain_covers hcover hx.1 (hx.2 r he)
  obtain ⟨a,ha,hax⟩ := h
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
  exact ⟨c,hc,hax⟩

theorem rat_cut_group_actual_cut (g : RatCutGroup) (hc : g.NumericValid)
    (hsound : ∀ c∈g.cells, c.Sound)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S T : Finset V)
    (R z p : ℝ) (pres : unitInterval)
    (hn : (0:ℝ) < Fintype.card V) (hm : (0:ℝ) < Fintype.card G.edgeSet)
    (hI : CoverSparseCutIrreducible G)
    (hxl : (g.geometry.inputs.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (g.geometry.inputs.xh:ℝ))
    (hcoord : coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)=z/p)
    (hncoord : (Fintype.card V:ℝ)=R*(z/p))
    (hR0 : 0 ≤ R) (hR : (g.geometry.Rlo:ℝ) ≤ R) (hp : 0 < p) (hz : 0 < z)
    (hpu : p ≤ (g.geometry.pmax:ℝ)) (hzlo : (g.geometry.zlo:ℝ) ≤ z)
    (hD : (g.geometry.Dlo:ℝ)*R ≤ z) (hres : (g.geometry.ps:ℝ)*p ≤ (pres:ℝ))
    (hmark : (T.card:ℝ) ≤ (g.geometry.M:ℝ)*R)
    (hW : ∀ c∈g.cells, (c.population.Wlo:ℝ) ≤ p*z)
    (hside : g.interval.Contains ((S.card:ℝ)/(z/p)))
    (hcap : (S.card:ℝ) ≤ (g.cap:ℝ)*Fintype.card V) :
    ∃ c∈g.cells,
      RoundedCutLabelValid G S T pres c.region.bin.residual.retention.lambda
        ((c.region.bin.residual.kappa:ℝ)*(z/p)*S.card) c.region.bin.tau
        (2*exp (-(c.region.bin.gamma:ℝ)*z)) ∧
      c.threshold.Bound p z pres S.card := by
  obtain ⟨c,hcMem,hinterval⟩ := rat_cut_group_covers g hc hside
  have hs := hsound c hcMem
  obtain ⟨hRl,hcp,hexp,hcx,hch,hM,hpmax,hDlo,hzlower,hps,_,_⟩ := hc.2.2.2 c hcMem
  have hbounds := rat_cut_region_side_bounds c.region hs.1 (div_pos hz hp)
    (by rwa [hRl]) hncoord hinterval (by rwa [hcp])
  have hcut := hs.2.1 G S T R z p pres hn hm hI (by rwa [hcx]) (by rwa [hch]) hcoord
    hR0 hp (by rwa [hpmax]) (by rwa [hzlower]) (by rwa [hDlo]) (by rwa [hps])
    (by rwa [hM]) hbounds.1 hbounds.2
  exact ⟨c,hcMem,hcut,hs.2.2.1 p z pres S.card hp hz hbounds.1 (by
    change (c.region.bin.ps:ℝ)*p ≤ (pres:ℝ)
    rwa [hps]) (hW c hcMem)⟩

end
end Cycle12
