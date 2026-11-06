import Cycle12.PackingIsolatedPadding
import Cycle12.Foundations.PackingExtension

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

def inducedValHom (G : SimpleGraph V) (U : Finset V) : G.induce (U:Set V) →g G :=
  {toFun := Subtype.val,map_rel' := fun h => h}

/-- Lift actual cycles from an induced graph to the original vertex set. -/
def liftInducedPacking (G : SimpleGraph V) (U : Finset V)
    (P : CyclePacking (G.induce (U:Set V))) : CyclePacking G where
  count := P.count
  parts i := Sym2.map (Subtype.val : U → V) '' P.parts i
  cycles i := by
    obtain ⟨v,p,hp,he⟩ := P.cycles i
    refine ⟨v.val,p.map (inducedValHom G U),hp.map Subtype.val_injective,?_⟩
    rw [he]
    exact (p.edgeSet_map (inducedValHom G U)).symm
  disjoint := by
    intro i j hij
    exact (Set.disjoint_image_iff (Sym2.map.injective Subtype.val_injective)).mpr (P.disjoint hij)

theorem liftInducedPacking_used (G : SimpleGraph V) (U : Finset V)
    (P : CyclePacking (G.induce (U:Set V))) :
    (liftInducedPacking G U P).used = Sym2.map (Subtype.val : U → V) '' P.used := by
  simp only [CyclePacking.used,liftInducedPacking,Set.image_iUnion]

theorem induced_edges_of_supported (G : SimpleGraph V) (U : Finset V)
    (hU : ∀ x y, G.Adj x y → x ∈ U ∧ y ∈ U) :
    Sym2.map (Subtype.val : U → V) '' (G.induce (U:Set V)).edgeSet = G.edgeSet := by
  ext e
  constructor
  · rintro ⟨d,hd,hde⟩
    induction d using Sym2.inductionOn with
    | _ x y => exact hde ▸ (show s(x.val,y.val) ∈ G.edgeSet from hd)
  · intro he
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨s((⟨x,(hU x y he).1⟩ : U),(⟨y,(hU x y he).2⟩ : U)),he,rfl⟩

theorem liftInducedPacking_residue (G : SimpleGraph V) (U : Finset V)
    (P : CyclePacking (G.induce (U:Set V))) (hU : ∀ x y, G.Adj x y → x ∈ U ∧ y ∈ U) :
    (liftInducedPacking G U P).residue.edgeSet = Sym2.map (Subtype.val : U → V) '' P.residue.edgeSet := by
  rw [CyclePacking.residue,edgeSet_deleteEdges,liftInducedPacking_used,
    ←induced_edges_of_supported G U hU,←Set.image_sdiff (Sym2.map.injective Subtype.val_injective)]
  rw [CyclePacking.residue,edgeSet_deleteEdges]

theorem liftInducedPacking_weight (G : SimpleGraph V) (U : Finset V)
    (P : CyclePacking (G.induce (U:Set V))) (hU : ∀ x y, G.Adj x y → x ∈ U ∧ y ∈ U) :
    (liftInducedPacking G U P).weight = P.weight := by
  have hs : (liftInducedPacking G U P).singles = P.singles := by
    rw [CyclePacking.singles,liftInducedPacking_residue G U P hU,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
    rfl
  change (P.count:ℝ)+(23/42:ℝ)*(liftInducedPacking G U P).singles = P.weight
  rw [hs]
  rfl

/-- Continue on the actual induced residue and pay only its true order,
without charging isolated ambient vertices. -/
theorem completion_weight_from_induced {G : SimpleGraph V} (P : CyclePacking G)
    (U : Finset V) (hU : ∀ x y, P.residue.Adj x y → x ∈ U ∧ y ∈ U)
    {K n : ℝ} (hP : (P.count:ℝ) ≤ n)
    (hQ : ∃ Q : CyclePacking (P.residue.induce (U:Set V)), Q.weight ≤ K*U.card) :
    ∃ T : CyclePacking G, T.weight ≤ n+K*U.card := by
  obtain ⟨Q,hQ⟩ := hQ
  let S := liftInducedPacking P.residue U Q
  refine ⟨P.extend S,?_⟩
  rw [CyclePacking.extend_weight,liftInducedPacking_weight P.residue U Q hU]
  linarith only [hP,hQ]

end
end Cycle12
