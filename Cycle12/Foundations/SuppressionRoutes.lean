import Cycle12.Foundations.SuppressionCounts

/-! Actual suppression of one vertex: retain nonincident edges and splice
the incident nonloop ports according to a matching. Parallel edges survive. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MatchingPortFamily
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {H : SimpleGraph I} (M : H.Subgraph) (o : I → V)
    {G : SimpleGraph W} (φ : V ↪ W) (z : W) (P : ∀ i, G.Walk z (φ (o i)))

theorem degree_routed_full (hM : M.IsMatching) (hcover : M.verts=Set.univ)
    (hP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet))
    (havoid : ∀ i v, φ v ∈ (P i).support → v=o i) (v : V) :
    (routed M o φ z P hM hP havoid).degree v=(univ.filter (fun i : I => o i=v)).card := by
  rw [degree_routed,← Fintype.card_subtype,← Fintype.card_subtype]
  apply Fintype.card_congr
  exact {
    toFun i := ⟨i.val.val,i.property⟩
    invFun i := ⟨⟨i.val,by rw [hcover]; trivial⟩,i.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }

end MatchingPortFamily

namespace RoutedEdges
variable {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)

def afterVertex : {v : V // v≠z} ↪ W :=
  ⟨fun v => φ v.val,fun _ _ h => Subtype.ext (φ.injective h)⟩

abbrev Ports := {i // Suppression.portPred R.left R.right z i}
abbrev Kept := {i // Suppression.keepPred R.left R.right z i}

def portTip (i : R.Ports z) : {v : V // v≠z} :=
  ⟨Suppression.otherEnd R.left R.right z i.val,
    Suppression.otherEnd_ne R.left R.right z i⟩

def portWalk (i : R.Ports z) : G.Walk (φ z) (afterVertex (φ:=φ) z (R.portTip z i)) := by
  by_cases ha : R.left i.val=z
  · exact (R.route i.val).copy (congrArg φ ha)
      (by simp [afterVertex,portTip,Suppression.otherEnd,ha]; rfl)
  · have hb : R.right i.val=z := (i.property.resolve_left (fun h => ha h.1)).1
    exact (R.route i.val).reverse.copy (congrArg φ hb)
      (by simp [afterVertex,portTip,Suppression.otherEnd,ha]; rfl)

lemma portWalk_edgeSet (i : R.Ports z) : (R.portWalk z i).edgeSet=(R.route i.val).edgeSet := by
  unfold portWalk
  split_ifs <;> simp

lemma portWalk_support (i : R.Ports z) (x : W) :
    x ∈ (R.portWalk z i).support ↔ x ∈ (R.route i.val).support := by
  unfold portWalk
  split_ifs <;> simp

lemma portWalk_disjoint : Pairwise (fun i j : R.Ports z =>
    Disjoint (R.portWalk z i).edgeSet (R.portWalk z j).edgeSet) := by
  intro i j h
  rw [portWalk_edgeSet,portWalk_edgeSet]
  exact R.disjoint (Subtype.val_injective.ne h)

lemma portWalk_avoids (i : R.Ports z) (v : {v : V // v≠z})
    (hv : afterVertex (φ:=φ) z v ∈ (R.portWalk z i).support) : v=R.portTip z i := by
  have hR := R.avoids i.val v.val ((R.portWalk_support z i (φ v.val)).mp hv)
  apply Subtype.ext
  change v.val=Suppression.otherEnd R.left R.right z i.val
  by_cases ha : R.left i.val=z
  · rw [Suppression.otherEnd,if_pos ha]
    exact hR.resolve_left (fun h => v.property (h.trans ha))
  · have hb : R.right i.val=z := (i.property.resolve_left (fun h => ha h.1)).1
    rw [Suppression.otherEnd,if_neg ha]
    exact hR.resolve_right (fun h => v.property (h.trans hb))

def keptRoutes : RoutedEdges G (afterVertex (φ:=φ) z) (R.Kept z) where
  left i := ⟨R.left i.val,i.property.1⟩
  right i := ⟨R.right i.val,i.property.2⟩
  route i := R.route i.val
  disjoint := by
    intro i j h
    exact R.disjoint (Subtype.val_injective.ne h)
  avoids i v h := (R.avoids i.val v.val h).imp Subtype.ext Subtype.ext

lemma kept_ne_port (i : R.Kept z) (j : R.Ports z) : i.val≠j.val := by
  intro he
  have hp : Suppression.portPred R.left R.right z i.val := he.symm ▸ j.property
  exact hp.elim (fun h => i.property.1 h.1) (fun h => i.property.2 h.1)

variable {H : SimpleGraph (R.Ports z)}

def pairedRoutes (M : H.Subgraph) (hM : M.IsMatching) :
    RoutedEdges G (afterVertex (φ:=φ) z) M.edgeSet :=
  MatchingPortFamily.routed M (R.portTip z) (afterVertex (φ:=φ) z) (φ z) (R.portWalk z)
    hM (R.portWalk_disjoint z) (R.portWalk_avoids z)

lemma kept_paired_disjoint (M : H.Subgraph) (hM : M.IsMatching)
    (i : R.Kept z) (e : M.edgeSet) :
    Disjoint ((R.keptRoutes z).route i).edgeSet ((R.pairedRoutes z M hM).route e).edgeSet := by
  change Disjoint (R.route i.val).edgeSet
    (((R.portWalk z e.val.out.1).reverse.append (R.portWalk z e.val.out.2)).edgeSet)
  rw [Walk.edgeSet_append,Walk.edgeSet_reverse,portWalk_edgeSet,portWalk_edgeSet]
  exact (R.disjoint (R.kept_ne_port z i _)).union_right (R.disjoint (R.kept_ne_port z i _))

def suppress (M : H.Subgraph) (hM : M.IsMatching) :
    RoutedEdges G (afterVertex (φ:=φ) z) ((R.Kept z) ⊕ M.edgeSet) :=
  (R.keptRoutes z).append (R.pairedRoutes z M hM) (R.kept_paired_disjoint z M hM)

theorem degree_suppress (M : H.Subgraph) (hM : M.IsMatching) (hcover : M.verts=Set.univ)
    (v : {v : V // v≠z}) : (R.suppress z M hM).degree v=R.degree v.val := by
  rw [suppress,degree_append]
  have hp := MatchingPortFamily.degree_routed_full M (R.portTip z)
    (afterVertex (φ:=φ) z) (φ z) (R.portWalk z) hM hcover
    (R.portWalk_disjoint z) (R.portWalk_avoids z) v
  change (R.pairedRoutes z M hM).degree v=_ at hp
  rw [hp]
  have h := Suppression.degree_retained R.left R.right z v.val v.property
  simpa only [degree,keptRoutes,Subtype.ext_iff,portTip,Suppression.incidenceDegree] using h.symm

theorem exists_suppression_matching (heven : Even (R.degree z)) :
    ∃ M : (⊤ : SimpleGraph (R.Ports z)).Subgraph, M.IsMatching ∧ M.verts=Set.univ := by
  have he := Suppression.even_ports_of_even_degree R.left R.right z heven
  have hc : (⊤ : SimpleGraph (R.Ports z)).IsClique Set.univ := by
    intro x _ y _ hxy
    exact hxy
  obtain ⟨M,hcover,hM⟩ := (hc.even_iff_exists_isMatching (Set.toFinite _)).mp
    (by simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using he)
  exact ⟨M,hM,hcover⟩

end RoutedEdges
end
end Cycle13
