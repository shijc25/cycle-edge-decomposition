import Cycle12.ReservedPathFamily12
import Cycle12.TwoEdgeIncidence12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq I]

/-- A single injection for all endpoint occurrences pays the complete
mixed demand family from the degree in the original descendant graph. -/
theorem endpointLoad_from_incidence_injection (F : SimpleGraph V) (a b : I → V)
    (neighbor : I × Bool → V)
    (hadj : ∀ k,F.Adj (if k.2 then b k.1 else a k.1) (neighbor k))
    (hinj : Function.Injective
      (fun k : I × Bool => ((if k.2 then b k.1 else a k.1),neighbor k))) (v : V) :
    endpointLoad a b v ≤ F.degree v := by
  let E := {k : I × Bool // (if k.2 then b k.1 else a k.1)=v}
  let f : E → F.neighborSet v := fun k => ⟨neighbor k.val,by
    have hh := hadj k.val
    rw [k.property] at hh
    exact hh⟩
  have hf : Function.Injective f := by
    intro k l he
    apply Subtype.ext
    apply hinj
    apply Prod.ext
    · exact k.property.trans l.property.symm
    · exact congrArg Subtype.val he
  have hc := Fintype.card_le_of_injective f hf
  have hcard : Fintype.card E=endpointLoad a b v := by
    dsimp only [E]
    rw [Fintype.card_subtype,card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false]
    rw [sum_add_distrib]
    simp only [endpointLoad,card_eq_sum_ones,sum_filter]
    omega
  simpa only [hcard,card_neighborSet_eq_degree] using hc

/-- Independent original edge classes can be combined before routing.
Within each class an occurrence has a unique directed incident edge;
disjointness of the classes preserves that property for the whole family. -/
theorem mixed_incidence_injective (K : J → Type) (S : J → Set (Sym2 V))
    (root next : (Σ j,K j) → V)
    (hmem : ∀ k,s(root k,next k)∈S k.1)
    (hdisj : Pairwise (fun j l => Disjoint (S j) (S l)))
    (hlocal : ∀ j,Function.Injective (fun k : K j => (root ⟨j,k⟩,next ⟨j,k⟩))) :
    Function.Injective (fun k => (root k,next k)) := by
  rintro ⟨j,k⟩ ⟨l,m⟩ he
  have hjl : j=l := by
    by_contra hn
    have hs : s(root ⟨j,k⟩,next ⟨j,k⟩)=s(root ⟨l,m⟩,next ⟨l,m⟩) :=
      congrArg (fun p : V × V => s(p.1,p.2)) he
    exact Set.disjoint_left.mp (hdisj hn) (hmem ⟨j,k⟩) (hs.symm ▸ hmem ⟨l,m⟩)
  subst l
  exact congrArg (Sigma.mk j) (hlocal j he)

/-- Reconnecting or deleting endpoint occurrences does not increase
load, provided their original incidence assignment is injective. -/
theorem endpointLoad_from_mixed_ports (F : SimpleGraph V) (a b : I → V)
    (K : Type) (root next : K → V)
    (hroot : ∀ k,F.Adj (root k) (next k))
    (hinj : Function.Injective (fun k => (root k,next k)))
    (pick : I × Bool ↪ K)
    (hport : ∀ k,root (pick k)=(if k.2 then b k.1 else a k.1)) (v : V) :
    endpointLoad a b v ≤ F.degree v := by
  apply endpointLoad_from_incidence_injection F a b (next ∘ pick)
  · intro k
    rw [←hport k]
    exact hroot (pick k)
  · intro k l he
    apply pick.injective
    apply hinj
    simpa only [hport,Function.comp_apply] using he

/-- The two endpoint occurrences of every disjoint original two-edge
path already give the required incidence injection, across all batches. -/
theorem twoEdge_incidence_injective {F : SimpleGraph V} (a b z : I → V)
    (ha : ∀ i,F.Adj (z i) (a i)) (hb : ∀ i,F.Adj (z i) (b i))
    (hne : ∀ i,a i ≠ b i)
    (hd : Pairwise (fun i j => Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet
      (twoEdgeWalk (ha j) (hb j)).edgeSet)) :
    Function.Injective (fun k : I × Bool => ((if k.2 then b k.1 else a k.1),z k.1)) := by
  rintro ⟨i,c⟩ ⟨j,d⟩ he
  have hv : (if c then b i else a i)=(if d then b j else a j) := congrArg Prod.fst he
  have hz : z i=z j := congrArg Prod.snd he
  have hij : i=j := by
    by_contra hn
    have hm : s(z i,if c then b i else a i)∈(twoEdgeWalk (ha i) (hb i)).edgeSet := by
      rw [twoEdgeWalk_edges]
      cases c <;> simp
    have hm' : s(z i,if c then b i else a i)∈(twoEdgeWalk (ha j) (hb j)).edgeSet := by
      rw [twoEdgeWalk_edges,hz,hv]
      cases d <;> simp
    exact Set.disjoint_left.mp (hd hn) hm hm'
  subst j
  have hcd : c=d := by
    cases c <;> cases d <;> simp_all [eq_comm]
  rw [hcd]

end
end Cycle12
