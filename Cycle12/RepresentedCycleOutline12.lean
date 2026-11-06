import Cycle12.SoftOutlinePacking12
import Cycle12.QuotientPackingLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
variable {G : SimpleGraph V} {Q : SimpleGraph W}

/-- A quotient cycle with actual, uniquely represented original edges.
The quotient type and projection remain visible for block-fibre arguments. -/
structure RepresentedCyclePorts12 (π : V → W) (S : Set (Sym2 V))
    {a : W} (p : Q.Walk a a) where
  rep : Q.Dart → G.Dart
  rep_mem : ∀ d,(rep d).edge∈S
  rep_project : ∀ d,π (rep d).fst=d.fst ∧ π (rep d).snd=d.snd
  start : W → V
  finish : W → V
  ports : ∀ d∈p.darts,finish d.fst=(rep d).fst ∧ start d.snd=(rep d).snd
  projects : ∀ z∈p.dropLast.support,π (start z)=z ∧ π (finish z)=z
  outside : ∀ z,z∉p.dropLast.support → start z=finish z

def chooseRepresentedCyclePorts12 (π : V → W) (S : Set (Sym2 V))
    (hSG : S⊆G.edgeSet) (hrep : ∀ e∈Q.edgeSet,∃ f∈S,Sym2.map π f=e)
    {a : W} (p : Q.Walk a a) (hp : p.IsCycle) :
    RepresentedCyclePorts12 (G:=G) π S p := by
  let R := (orient_edge_representatives π S hSG hrep).choose
  have hR := (orient_edge_representatives π S hSG hrep).choose_spec
  let v₀ := (R ⟨(a,p.snd),p.adj_snd hp.not_nil⟩).fst
  let hc := choose_cycle_ports π R (fun d => (hR d).2) p hp v₀
  let s := hc.choose
  let t := hc.choose_spec.choose
  have hports := hc.choose_spec.choose_spec.1
  have hproj := hc.choose_spec.choose_spec.2
  have hfst (d : Q.Dart) (hd : d∈p.darts) : d.fst∈p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil,←Walk.map_fst_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  have hsnd (d : Q.Dart) (hd : d∈p.darts) : d.snd∈p.dropLast.support := by
    rw [p.support_dropLast hp.not_nil]
    apply p.tail_support_perm_dropLast_support.mem_iff.mp
    rw [←Walk.map_snd_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  exact {
    rep:=R,rep_mem:=fun d => (hR d).1,rep_project:=fun d => (hR d).2,
    start:=fun z => if z∈p.dropLast.support then s z else v₀,
    finish:=fun z => if z∈p.dropLast.support then t z else v₀,
    ports:=by intro d hd; simpa only [ite_eq_left (hfst d hd),ite_eq_left (hsnd d hd)] using hports d hd,
    projects:=by intro z hz; simpa only [ite_eq_left hz] using hproj z hz,
    outside:=by intro z hz; simp only [ite_eq_right hz] }

namespace RepresentedCyclePorts12
variable {π : V → W} {S : Set (Sym2 V)} {a : W} {p : Q.Walk a a}

@[reducible] def outline (r : RepresentedCyclePorts12 (G:=G) π S p) (hp : p.IsCycle) : CycleOutline G where
  W:=W
  finiteW:=inferInstance
  Q:=Q
  base:=a
  cycle:=p
  isCycle:=hp
  rep:=r.rep
  start:=r.start
  finish:=r.finish
  project:=π
  ports:=r.ports
  projects:=r.projects
  outside:=r.outside

theorem outline_edges (r : RepresentedCyclePorts12 (G:=G) π S p) (hp : p.IsCycle)
    (hu : Set.InjOn (Sym2.map π) S) :
    (r.outline hp).edges=S∩Sym2.map π ⁻¹' p.edgeSet := by
  change {e | ∃ d∈p.darts,e=(r.rep d).edge}=S∩Sym2.map π ⁻¹' p.edgeSet
  have hm (d : Q.Dart) : Sym2.map π (r.rep d).edge=d.edge := by
    change s(π (r.rep d).fst,π (r.rep d).snd)=s(d.fst,d.snd)
    rw [(r.rep_project d).1,(r.rep_project d).2]
  apply Set.Subset.antisymm
  · rintro e ⟨d,hd,rfl⟩
    refine ⟨r.rep_mem d,?_⟩
    change Sym2.map π (r.rep d).edge∈p.edges
    rw [hm,Walk.edges_eq_map_darts]
    exact List.mem_map.mpr ⟨d,hd,rfl⟩
  · rintro e ⟨he,hpE⟩
    change Sym2.map π e∈p.edges at hpE
    rw [Walk.edges_eq_map_darts] at hpE
    obtain ⟨d,hd,hmE⟩ := List.mem_map.mp hpE
    exact ⟨d,hd,hu he (r.rep_mem d) (hmE.symm.trans (hm d).symm)⟩

end RepresentedCyclePorts12
end
end Cycle12
