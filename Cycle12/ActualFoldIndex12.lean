import Cycle12.ActualFoldBox12
import Cycle12.ExactActiveBatches12
import Cycle12.EvenActualPrefixMass12

namespace Cycle12
open SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem actualBox_children {P : AssignedPiece V} (sp : StageSplit P) :
    sp.children=List.ofFn (fun j : Fin sp.boxes.length =>
      actualBoxRemainder sp (sp.boxes.get j) (List.get_mem _ j)) := by
  apply List.ext_getElem (by simp [StageSplit.children])
  intro j h1 h2
  simp only [StageSplit.children,List.getElem_pmap,List.getElem_ofFn,actualBoxRemainder,List.get_eq_getElem]

theorem actualBox_child_sum {P : AssignedPiece V} (sp : StageSplit P) (f : AssignedPiece V → ℝ) :
    (sp.children.map f).sum=∑ j : Fin sp.boxes.length,
      f (actualBoxRemainder sp (sp.boxes.get j) (List.get_mem _ j)) := by
  rw [actualBox_children,List.map_ofFn,List.sum_ofFn]
  rfl

theorem advance_singleton_flatMap (sp : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V)) :
    advance sp j k L=L.flatMap (fun P => advance sp j k [P]) := by
  simpa only [List.flatMap_singleton'] using advance_flatMap sp j k L (fun P => [P])

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches ActiveFamily)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev EvenScaleLayers12.FoldBoxIndex {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :=
  (p : Fin (advance L.splitter 0 i [originalPiece G]).length) ×
    Fin (L.splitter i ((advance L.splitter 0 i [originalPiece G]).get p)).boxes.length

def EvenScaleLayers12.foldParent {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : AssignedPiece V :=
  (advance L.splitter 0 i [originalPiece G]).get z.1

def EvenScaleLayers12.foldBox {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : AssignedPiece V :=
  (L.splitter i (L.foldParent i z)).boxes.get z.2

theorem EvenScaleLayers12.foldParent_mem {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : L.foldParent i z∈advance L.splitter 0 i [originalPiece G] :=
  List.get_mem _ z.1

theorem EvenScaleLayers12.foldBox_mem {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : L.foldBox i z∈(L.splitter i (L.foldParent i z)).boxes :=
  List.get_mem _ z.2

def EvenScaleLayers12.foldChild {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : AssignedPiece V :=
  actualBoxRemainder (L.splitter i (L.foldParent i z)) (L.foldBox i z) (L.foldBox_mem i z)

def EvenScaleLayers12.foldCores {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : List (AssignedPiece V) :=
  (L.splitter i (L.foldParent i z)).pieces (L.foldBox i z)

def EvenScaleLayers12.foldDescendants {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : List (AssignedPiece V) :=
  advance L.splitter (i+1) 2 [L.foldChild i z]

def EvenScaleLayers12.foldDescendantGraph {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ)
    (z : L.FoldBoxIndex i) : SimpleGraph V :=
  graphUnion ((L.foldDescendants i z).map AssignedPiece.graph)

theorem EvenScaleLayers12.fold_box_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :
    (∑ z : L.FoldBoxIndex i,((L.foldBox i z).vertices.card:ℝ))=
      vertexMass (advance L.splitter 0 (i+1) [originalPiece G]) := by
  rw [Fintype.sum_sigma,advance_succ,Nat.zero_add,nextLayer,vertexMass_flatMap]
  simp only [foldBox,foldParent]
  simp_rw [StageSplit.children_mass]
  rw [←list_sum_get]
  apply sum_congr rfl
  intro p hp
  exact list_sum_get _ (fun B : AssignedPiece V => (B.vertices.card:ℝ))

theorem EvenScaleLayers12.fold_core_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :
    (∑ z : L.FoldBoxIndex i,vertexMass (L.foldCores i z))=L.coreMass i := by
  rw [Fintype.sum_sigma,EvenScaleLayers12.coreMass,levelPieces,vertexMass_flatMap]
  simp only [foldCores,foldBox,foldParent]
  rw [←list_sum_get]
  apply sum_congr rfl
  intro p hp
  rw [vertexMass_flatMap]
  exact list_sum_get _ (fun B => vertexMass ((L.splitter i _).pieces B))

theorem EvenScaleLayers12.fold_descendant_mass {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) :
    (∑ z : L.FoldBoxIndex i,vertexMass (L.foldDescendants i z))=
      vertexMass (advance L.splitter 0 (i+3) [originalPiece G]) := by
  rw [show i+3=(i+1)+2 by omega,advance_add,Nat.zero_add]
  rw [advance_succ L.splitter 0 i,Nat.zero_add]
  rw [nextLayer,advance_flatMap,vertexMass_flatMap,Fintype.sum_sigma]
  simp only [foldDescendants,foldChild,foldBox,foldParent]
  rw [←list_sum_get]
  apply sum_congr rfl
  intro p hp
  rw [advance_singleton_flatMap L.splitter (i+1) 2
    (L.splitter i ((advance L.splitter 0 i [originalPiece G]).get p)).children]
  rw [vertexMass_flatMap,actualBox_child_sum]

theorem EvenScaleLayers12.fold_box_order {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i) :
    ((L.foldBox i z).vertices.card:ℝ) ≤ (2:ℝ)^(rho*logScale (originalLog V) L.stopIndex i) :=
  (L.bounds i (by omega) _ (L.foldParent_mem i z)).2.2.1 _ (L.foldBox_mem i z)

/-- The whole indexed stage uses actual box children and their original
core lists. Indexing keeps repeated occurrences distinct. -/
theorem EvenScaleLayers12.fold_box_active_exact {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) (z : L.FoldBoxIndex i) :
    let w := logScale (originalLog V) L.stopIndex i
    let U := fun r : Fin (L.foldCores i z).length => ((L.foldCores i z).get r).vertices
    ∃ B : GraphBatches (L.foldDescendantGraph i z) (L.foldBox i z).vertices
        ((2:ℝ)^(b*w)) (vertexMass (L.foldDescendants i z)),
      ∃ A : ActiveFamily (L.foldDescendantGraph i z) (L.foldBox i z).vertices B.vertices U
        ((2:ℝ)^(alpha*w)) ((2:ℝ)^(lam*w)),
        (∀ t,Function.Injective (A.router t)) ∧
        (∑ r,((U r).card:ℝ))-
          (entropyRemainder12 (q0*w)*M*(L.foldBox i z).vertices.card)/(2:ℝ)^(alpha*w)-
          (2:ℝ)^(lam*w)*(1+2*(M*(L.foldBox i z).vertices.card)/(2:ℝ)^(b*w))*
            (((L.foldBox i z).vertices.card:ℝ)/(2:ℝ)^(s*w)) ≤
          ∑ t,∑ j,((A.vertices t j).card:ℝ) ∧
        (∑ t,∑ j,((A.vertices t j).card:ℝ))+(L.foldBox i z).vertices.card ≤
          (∑ r,((U r).card:ℝ))+vertexMass (L.foldDescendants i z) := by
  dsimp only
  have hd := L.actual_box_data hi (L.foldParent_mem i z) (L.foldBox_mem i z)
  exact L.prepare_active_descendants_exact hi hd.1 _ hd.2.1 hd.2.2.1
    (fun r => (hd.2.2.2.1 r).1.le)

end
end Cycle12.Even12
