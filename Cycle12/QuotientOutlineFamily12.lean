import Cycle12.SoftQuotientAssembly12
import Cycle12.ContractedCycleSoftBudget12
import Cycle12.OutlineEndpointIncidence12
import Cycle12.OriginalEndpointFamilies12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]

/-- Actual quotient cycles and their chosen original representatives,
retaining the projection for the later block and soft-collision arguments. -/
structure QuotientOutlineFamily12 (G H : SimpleGraph V) (π : V → W) (P : CyclePacking (H.map π)) where
  base : Fin P.count → W
  walk : ∀ j,(H.map π).Walk (base j) (base j)
  isCycle : ∀ j,(walk j).IsCycle
  parts : ∀ j,P.parts j=(walk j).edgeSet
  ports : ∀ j,RepresentedCyclePorts12 (G:=G) π H.edgeSet (walk j)

theorem quotientOutlineFamily_exists (G H : SimpleGraph V) (π : V → W)
    (hHG : H ≤ G) (hproper : ∀ {x y},H.Adj x y → π x ≠ π y) (P : CyclePacking (H.map π)) :
    Nonempty (QuotientOutlineFamily12 G H π P) := by
  choose a p hp he using P.cycles
  have hrep : ∀ e,e∈(H.map π).edgeSet → ∃ f∈H.edgeSet,Sym2.map π f=e := by
    intro e he
    rwa [edgeSet_map_of_no_internal H π hproper] at he
  exact ⟨⟨a,p,hp,he,fun j => chooseRepresentedCyclePorts12 π H.edgeSet (edgeSet_mono hHG) hrep (p j) (hp j)⟩⟩

namespace QuotientOutlineFamily12
variable {G H : SimpleGraph V} {π : V → W} {P : CyclePacking (H.map π)}

def outline (D : QuotientOutlineFamily12 G H π P) (j : Fin P.count) : CycleOutline G :=
  (D.ports j).outline (D.isCycle j)

theorem outline_edges (D : QuotientOutlineFamily12 G H π P)
    (hu : Set.InjOn (Sym2.map π) H.edgeSet) (j : Fin P.count) :
    (D.outline j).edges=H.edgeSet∩Sym2.map π ⁻¹' P.parts j := by
  rw [D.parts j]
  exact (D.ports j).outline_edges (D.isCycle j) hu

theorem outline_subset (D : QuotientOutlineFamily12 G H π P)
    (hu : Set.InjOn (Sym2.map π) H.edgeSet) (j : Fin P.count) : (D.outline j).edges⊆H.edgeSet := by
  rw [D.outline_edges hu j]
  exact Set.inter_subset_left

theorem outlines_disjoint (D : QuotientOutlineFamily12 G H π P)
    (hu : Set.InjOn (Sym2.map π) H.edgeSet) :
    Pairwise (fun j k => Disjoint (D.outline j).edges (D.outline k).edges) := by
  intro j k hjk
  rw [D.outline_edges hu j,D.outline_edges hu k]
  apply Set.disjoint_left.mpr
  intro e he hf
  exact Set.disjoint_left.mp (P.disjoint hjk) he.2 hf.2

theorem outlines_used (D : QuotientOutlineFamily12 G H π P)
    (hu : Set.InjOn (Sym2.map π) H.edgeSet) :
    (⋃ j,(D.outline j).edges)=H.edgeSet∩Sym2.map π ⁻¹' P.used := by
  simp_rw [D.outline_edges hu]
  simp only [CyclePacking.used,Set.preimage_iUnion,Set.inter_iUnion]

/-- A chosen original neighbor at every switch port, with injectivity
coming from the distinct ports of the original representative cycle. -/
def outlineCertificate (c : CycleOutline G) :
    OriginalEndpointCertificate G (fun z : c.Switch => c.start z) (fun z => c.finish z) c.edges := by
  choose neighbor hn using fun k : c.Switch × Bool => outlineSwitchPort_original_neighbor c k
  exact ⟨neighbor,fun k => (hn k).1,fun k => (hn k).2,
    fun _ _ h => outlineSwitchPort_injective c (congrArg Prod.fst h)⟩

abbrev RequestIndex (D : QuotientOutlineFamily12 G H π P) := Σ j,(D.outline j).Switch

def certificate (D : QuotientOutlineFamily12 G H π P)
    (hu : Set.InjOn (Sym2.map π) H.edgeSet) :
    OriginalEndpointCertificate G (fun k : D.RequestIndex => (D.outline k.1).start k.2)
      (fun k => (D.outline k.1).finish k.2) (⋃ j,(D.outline j).edges) :=
  OriginalEndpointCertificate.sigma (fun j => outlineCertificate (D.outline j)) (D.outlines_disjoint hu)

/-- The numerical soft budget is charged to the lengths of the actual
quotient cycles, hence to at most the original retained edge count. -/
theorem total_length (D : QuotientOutlineFamily12 G H π P)
    (hproper : ∀ {x y},H.Adj x y → π x ≠ π y)
    (hu : Set.InjOn (Sym2.map π) H.edgeSet) :
    (∑ j,(D.outline j).cycle.length)=P.used.ncard ∧ P.used.ncard ≤ H.edgeSet.ncard :=
  quotient_outline_total_length G H π hproper hu P D.outline (D.outline_edges hu)

end QuotientOutlineFamily12
end
end Cycle12
