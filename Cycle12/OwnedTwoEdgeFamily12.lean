import Cycle12.OriginalEndpointFamilies12
import Cycle12.Foundations.BipartitePairRemoval

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V]

/-- Disjoint original two-edge paths with their actual active-block owner.
The center is allowed inside the owning core; that decision is made only
after all batches have been aggregated. -/
structure OwnedTwoEdgeFamily12 (G : SimpleGraph V) (A : I → Finset V) where
  Index : Type
  finite : Fintype Index
  owner : Index → I
  left : Index → V
  right : Index → V
  center : Index → V
  adj_left : ∀ j,G.Adj (center j) (left j)
  adj_right : ∀ j,G.Adj (center j) (right j)
  distinct : ∀ j,left j ≠ right j
  left_mem : ∀ j,left j∈A (owner j)
  right_mem : ∀ j,right j∈A (owner j)
  disjoint : Pairwise (fun j k => Disjoint
    ({s(center j,left j),s(center j,right j)}:Set (Sym2 V))
    {s(center k,left k),s(center k,right k)})
attribute [instance] OwnedTwoEdgeFamily12.finite

namespace OwnedTwoEdgeFamily12
variable {G : SimpleGraph V} {A : I → Finset V}

def edges (P : OwnedTwoEdgeFamily12 G A) (j : P.Index) : Set (Sym2 V) :=
  {s(P.center j,P.left j),s(P.center j,P.right j)}
def used (P : OwnedTwoEdgeFamily12 G A) : Set (Sym2 V) := ⋃ j,P.edges j

theorem edges_subset (P : OwnedTwoEdgeFamily12 G A) (j : P.Index) : P.edges j⊆G.edgeSet := by
  rintro e (rfl|rfl)
  · exact P.adj_left j
  · exact P.adj_right j

theorem used_subset (P : OwnedTwoEdgeFamily12 G A) : P.used⊆G.edgeSet := by
  intro e he
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  exact P.edges_subset j hj

def empty (G : SimpleGraph V) (A : I → Finset V) : OwnedTwoEdgeFamily12 G A where
  Index := Empty
  finite := inferInstance
  owner := Empty.elim
  left := Empty.elim
  right := Empty.elim
  center := Empty.elim
  adj_left := fun j => j.elim
  adj_right := fun j => j.elim
  distinct := fun j => j.elim
  left_mem := fun j => j.elim
  right_mem := fun j => j.elim
  disjoint := by intro j; exact j.elim

@[simp] theorem empty_used (G : SimpleGraph V) (A : I → Finset V) : (empty G A).used=∅ := by
  ext e
  simp only [used,Set.mem_iUnion,Set.mem_empty_iff_false]
  exact ⟨fun ⟨j,_⟩ => (show Empty from j).elim,False.elim⟩

def ofPairing {H : SimpleGraph V} {U : Finset V} (P : CenterPairings H U)
    (hHG : H ≤ G) (r : I) (hends : ∀ j,P.left j∈A r ∧ P.right j∈A r) :
    OwnedTwoEdgeFamily12 G A where
  Index := P.Index
  finite := inferInstance
  owner := fun _ => r
  left := P.left
  right := P.right
  center := fun j => j.1.val
  adj_left := fun j => hHG j.2.val.out.1.property.2
  adj_right := fun j => hHG j.2.val.out.2.property.2
  distinct := fun j => by
    intro he
    have hh := (edge_out_adj (P.matching j.1).spanningCoe j.2).ne
    exact hh (Subtype.ext he)
  left_mem := fun j => (hends j).1
  right_mem := fun j => (hends j).2
  disjoint := by
    intro j k hjk
    have hh := P.walks_disjoint hjk
    simp only [CenterPairings.walk,StarPairing.paired_edges] at hh
    convert hh using 1 <;> congr!

@[simp] theorem ofPairing_used {H : SimpleGraph V} {U : Finset V} (P : CenterPairings H U)
    (hHG : H ≤ G) (r : I) (hends : ∀ j,P.left j∈A r ∧ P.right j∈A r) :
    (ofPairing P hHG r hends).used=P.used := by
  simp only [used,edges,ofPairing,CenterPairings.used,CenterPairings.walk,StarPairing.paired_edges]
  congr!

theorem edges_subset_used (P : OwnedTwoEdgeFamily12 G A) (j : P.Index) : P.edges j⊆P.used :=
  Set.subset_iUnion P.edges j

def sum (P Q : OwnedTwoEdgeFamily12 G A) (hd : Disjoint P.used Q.used) :
    OwnedTwoEdgeFamily12 G A where
  Index := P.Index ⊕ Q.Index
  finite := inferInstance
  owner := Sum.elim P.owner Q.owner
  left := Sum.elim P.left Q.left
  right := Sum.elim P.right Q.right
  center := Sum.elim P.center Q.center
  adj_left := by intro j; cases j <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> first | exact P.adj_left _ | exact Q.adj_left _
  adj_right := by intro j; cases j <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> first | exact P.adj_right _ | exact Q.adj_right _
  distinct := by intro j; cases j <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> first | exact P.distinct _ | exact Q.distinct _
  left_mem := by intro j; cases j <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> first | exact P.left_mem _ | exact Q.left_mem _
  right_mem := by intro j; cases j <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> first | exact P.right_mem _ | exact Q.right_mem _
  disjoint := by
    intro j k hjk
    cases j with
    | inl j =>
      cases k with
      | inl k => exact P.disjoint (fun h => hjk (congrArg Sum.inl h))
      | inr k => exact hd.mono (P.edges_subset_used j) (Q.edges_subset_used k)
    | inr j =>
      cases k with
      | inl k => exact hd.symm.mono (Q.edges_subset_used j) (P.edges_subset_used k)
      | inr k => exact Q.disjoint (fun h => hjk (congrArg Sum.inr h))

@[simp] theorem sum_used (P Q : OwnedTwoEdgeFamily12 G A) (hd : Disjoint P.used Q.used) :
    (P.sum Q hd).used=P.used∪Q.used := by
  simp only [used,edges,sum,Set.iUnion_sum,Sum.elim_inl,Sum.elim_inr]

variable {J : Type} [Fintype J]

def sigma (P : J → OwnedTwoEdgeFamily12 G A)
    (hd : Pairwise (fun j k => Disjoint (P j).used (P k).used)) :
    OwnedTwoEdgeFamily12 G A where
  Index := Σ j,(P j).Index
  finite := inferInstance
  owner := fun j => (P j.1).owner j.2
  left := fun j => (P j.1).left j.2
  right := fun j => (P j.1).right j.2
  center := fun j => (P j.1).center j.2
  adj_left := fun j => (P j.1).adj_left j.2
  adj_right := fun j => (P j.1).adj_right j.2
  distinct := fun j => (P j.1).distinct j.2
  left_mem := fun j => (P j.1).left_mem j.2
  right_mem := fun j => (P j.1).right_mem j.2
  disjoint := by
    rintro ⟨j,k⟩ ⟨l,m⟩ hne
    by_cases hjl : j=l
    · subst l
      exact (P j).disjoint (fun h => hne (congrArg (Sigma.mk j) h))
    · exact (hd hjl).mono ((P j).edges_subset_used k) ((P l).edges_subset_used m)

@[simp] theorem sigma_used (P : J → OwnedTwoEdgeFamily12 G A)
    (hd : Pairwise (fun j k => Disjoint (P j).used (P k).used)) :
    (sigma P hd).used=⋃ j,(P j).used := by
  simp only [used,edges,sigma,Set.iUnion_sigma]

/-- Moving a batch back to its ambient graph also moves its true owner. -/
def map {W K : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W} {B : K → Finset W}
    (P : OwnedTwoEdgeFamily12 G A) (e : V ↪ W) (owner : I → K)
    (he : ∀ {x y},G.Adj x y → H.Adj (e x) (e y))
    (hA : ∀ r v,v∈A r → e v∈B (owner r)) : OwnedTwoEdgeFamily12 H B where
  Index := P.Index
  finite := inferInstance
  owner := owner ∘ P.owner
  left := e ∘ P.left
  right := e ∘ P.right
  center := e ∘ P.center
  adj_left := fun j => he (P.adj_left j)
  adj_right := fun j => he (P.adj_right j)
  distinct := fun j => e.injective.ne (P.distinct j)
  left_mem := fun j => hA _ _ (P.left_mem j)
  right_mem := fun j => hA _ _ (P.right_mem j)
  disjoint := by
    intro j k hjk
    have hh := Set.disjoint_image_of_injective (Sym2.map.injective e.injective) (P.disjoint hjk)
    simpa only [Set.image_insert_eq,Set.image_singleton,Sym2.map_mk,Function.comp_apply] using hh

@[simp] theorem map_used {W K : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W} {B : K → Finset W}
    (P : OwnedTwoEdgeFamily12 G A) (e : V ↪ W) (owner : I → K)
    (he : ∀ {x y},G.Adj x y → H.Adj (e x) (e y))
    (hA : ∀ r v,v∈A r → e v∈B (owner r)) :
    (P.map e owner he hA).used=Sym2.map e '' P.used := by
  simp only [used,edges,map,Set.image_iUnion,Set.image_insert_eq,Set.image_singleton,
    Sym2.map_mk,Function.comp_apply]

def enlarge {H : SimpleGraph V} (P : OwnedTwoEdgeFamily12 G A) (hGH : G ≤ H) :
    OwnedTwoEdgeFamily12 H A where
  Index := P.Index
  finite := P.finite
  owner := P.owner
  left := P.left
  right := P.right
  center := P.center
  adj_left := fun j => hGH (P.adj_left j)
  adj_right := fun j => hGH (P.adj_right j)
  distinct := P.distinct
  left_mem := P.left_mem
  right_mem := P.right_mem
  disjoint := P.disjoint

@[simp] theorem enlarge_used {H : SimpleGraph V} (P : OwnedTwoEdgeFamily12 G A) (hGH : G ≤ H) :
    (P.enlarge hGH).used=P.used := rfl

def restrict (P : OwnedTwoEdgeFamily12 G A) (keep : P.Index → Prop) : OwnedTwoEdgeFamily12 G A where
  Index := {j : P.Index // keep j}
  finite := inferInstance
  owner := fun j => P.owner j.val
  left := fun j => P.left j.val
  right := fun j => P.right j.val
  center := fun j => P.center j.val
  adj_left := fun j => P.adj_left j.val
  adj_right := fun j => P.adj_right j.val
  distinct := fun j => P.distinct j.val
  left_mem := fun j => P.left_mem j.val
  right_mem := fun j => P.right_mem j.val
  disjoint := fun _ _ h => P.disjoint (Subtype.val_injective.ne h)

theorem restrict_used_subset (P : OwnedTwoEdgeFamily12 G A) (keep : P.Index → Prop) :
    (P.restrict keep).used⊆P.used := by
  rintro e he
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  exact Set.mem_iUnion.mpr ⟨j.val,hj⟩

def certificate (P : OwnedTwoEdgeFamily12 G A) :
    OriginalEndpointCertificate G P.left P.right P.used where
  neighbor k := P.center k.1
  adj := by rintro ⟨j,t⟩; cases t <;> first | exact (P.adj_left j).symm | exact (P.adj_right j).symm
  mem := by
    rintro ⟨j,t⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    cases t <;> simp [edges,Sym2.eq_swap]
  injective := twoEdge_incidence_injective P.left P.right P.center P.adj_left P.adj_right P.distinct (by
    simpa only [twoEdgeWalk_edges] using P.disjoint)

theorem used_card (P : OwnedTwoEdgeFamily12 G A) : P.used.ncard=2*Fintype.card P.Index := by
  have hd : Pairwise (fun j k => Disjoint (P.edges j) (P.edges k)) := P.disjoint
  rw [used,ncard_iUnion_disjoint _ hd]
  have hc (j : P.Index) : (P.edges j).ncard=2 := by
    have hn : s(P.center j,P.left j) ≠ s(P.center j,P.right j) := by
      intro he
      rcases Sym2.eq_iff.mp he with h|h
      · exact P.distinct j h.2
      · exact (P.adj_right j).ne h.1
    exact Set.ncard_pair hn
  simp only [hc,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_comm]

end OwnedTwoEdgeFamily12
end
end Cycle12
