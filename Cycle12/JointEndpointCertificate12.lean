import Cycle12.MixedEndpointIncidence12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

/-- A checkable assignment of requests to distinct original incidences.
Its edge class records exactly what may be combined disjointly. -/
structure OriginalEndpointCertificate (F : SimpleGraph V) (a b : I → V)
    (S : Set (Sym2 V)) where
  neighbor : I × Bool → V
  adj : ∀ k,F.Adj (if k.2 then b k.1 else a k.1) (neighbor k)
  mem : ∀ k,s((if k.2 then b k.1 else a k.1),neighbor k)∈S
  injective : Function.Injective (fun k : I × Bool =>
    ((if k.2 then b k.1 else a k.1),neighbor k))

namespace OriginalEndpointCertificate
variable {F : SimpleGraph V} {a b : I → V} {c d : J → V}
  {S T : Set (Sym2 V)}

/-- Combine original edge classes before choosing any routes. Requests
from both classes are counted in one endpoint load. -/
def sum (P : OriginalEndpointCertificate F a b S)
    (Q : OriginalEndpointCertificate F c d T) (hST : Disjoint S T) :
    OriginalEndpointCertificate F (Sum.elim a c) (Sum.elim b d) (S∪T) where
  neighbor k := match k.1 with
    | .inl i => P.neighbor (i,k.2)
    | .inr j => Q.neighbor (j,k.2)
  adj := by
    rintro ⟨i,t⟩
    cases i with
    | inl i => exact P.adj (i,t)
    | inr j => exact Q.adj (j,t)
  mem := by
    rintro ⟨i,t⟩
    cases i with
    | inl i => exact Or.inl (P.mem (i,t))
    | inr j => exact Or.inr (Q.mem (j,t))
  injective := by
    rintro ⟨i,t⟩ ⟨j,u⟩ he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hh : (i,t)=(j,u) := P.injective (by cases t <;> cases u <;> exact he)
        exact congrArg (fun p : I × Bool => (Sum.inl p.1,p.2)) hh
      | inr j =>
        have hh : s((if t then b i else a i),P.neighbor (i,t))=
            s((if u then d j else c j),Q.neighbor (j,u)) := by
          have hm := congrArg (fun p : V × V => s(p.1,p.2)) he
          cases t <;> cases u <;> exact hm
        exact False.elim (Set.disjoint_left.mp hST (P.mem (i,t)) (hh.symm ▸ Q.mem (j,u)))
    | inr i =>
      cases j with
      | inl j =>
        have hh : s((if t then d i else c i),Q.neighbor (i,t))=
            s((if u then b j else a j),P.neighbor (j,u)) := by
          have hm := congrArg (fun p : V × V => s(p.1,p.2)) he
          cases t <;> cases u <;> exact hm
        exact False.elim (Set.disjoint_left.mp hST (P.mem (j,u)) (hh ▸ Q.mem (i,t)))
      | inr j =>
        have hh : (i,t)=(j,u) := Q.injective (by cases t <;> cases u <;> exact he)
        exact congrArg (fun p : J × Bool => (Sum.inr p.1,p.2)) hh

/-- Restrict to one core or any subfamily, retaining the same original
incidence witnesses and all of their disjointness. -/
def restrict (P : OriginalEndpointCertificate F a b S) (e : J ↪ I) :
    OriginalEndpointCertificate F (a ∘ e) (b ∘ e) S where
  neighbor k := P.neighbor (e k.1,k.2)
  adj := by rintro ⟨i,t⟩; exact P.adj (e i,t)
  mem := by rintro ⟨i,t⟩; exact P.mem (e i,t)
  injective := by
    rintro ⟨i,t⟩ ⟨j,u⟩ he
    have hh : (e i,t)=(e j,u) := P.injective (by cases t <;> cases u <;> exact he)
    have ht : t=u := congrArg (fun p : I × Bool => p.2) hh
    exact Prod.ext (e.injective (congrArg Prod.fst hh)) ht

theorem load_le (P : OriginalEndpointCertificate F a b S) (v : V) :
    endpointLoad a b v ≤ F.degree v :=
  endpointLoad_from_incidence_injection F a b P.neighbor P.adj P.injective v

end OriginalEndpointCertificate
end
end Cycle12
