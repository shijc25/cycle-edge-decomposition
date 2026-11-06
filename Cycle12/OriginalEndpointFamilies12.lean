import Cycle12.JointEndpointCertificate12
import Cycle12.RouteEmbedding12

namespace Cycle12.OriginalEndpointCertificate
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W J : Type} [Fintype V] [Fintype W] [Fintype J] [DecidableEq V] [DecidableEq W]
variable {I : J → Type} [∀ j,Fintype (I j)]

/-- Combine any finite indexed family of disjoint original edge classes.
This retains one joint incidence injection across all batches and origins. -/
def sigma {F : SimpleGraph V} {a b : ∀ j,I j → V} {S : J → Set (Sym2 V)}
    (P : ∀ j,OriginalEndpointCertificate F (a j) (b j) (S j))
    (hd : Pairwise (fun j k => Disjoint (S j) (S k))) :
    OriginalEndpointCertificate F (fun k : Σ j,I j => a k.1 k.2)
      (fun k : Σ j,I j => b k.1 k.2) (⋃ j,S j) where
  neighbor k := (P k.1.1).neighbor (k.1.2,k.2)
  adj := by rintro ⟨⟨j,i⟩,t⟩; exact (P j).adj (i,t)
  mem := by rintro ⟨⟨j,i⟩,t⟩; exact Set.mem_iUnion.mpr ⟨j,(P j).mem (i,t)⟩
  injective := by
    rintro ⟨⟨j,i⟩,t⟩ ⟨⟨k,l⟩,u⟩ he
    by_cases hjk : j=k
    · subst k
      have hh : (i,t)=(l,u) := (P j).injective (by cases t <;> cases u <;> exact he)
      cases hh
      rfl
    · have hh : s((if t then b j i else a j i),(P j).neighbor (i,t))=
          s((if u then b k l else a k l),(P k).neighbor (l,u)) := by
        have h := congrArg (fun p : V × V => s(p.1,p.2)) he
        cases t <;> cases u <;> exact h
      exact False.elim (Set.disjoint_left.mp (hd hjk) ((P j).mem (i,t)) (hh.symm ▸ (P k).mem (l,u)))

variable {K : Type} [Fintype K] {F : SimpleGraph V} {H : SimpleGraph W}
  {a b : K → V} {S : Set (Sym2 V)}

/-- Move local batch certificates to their original ambient vertices.
The embedding also transports the recorded original edge class. -/
def map (P : OriginalEndpointCertificate F a b S) (e : V ↪ W)
    (hmap : ∀ {x y},F.Adj x y → H.Adj (e x) (e y)) :
    OriginalEndpointCertificate H (fun i => e (a i)) (fun i => e (b i)) (Sym2.map e '' S) where
  neighbor k := e (P.neighbor k)
  adj := by
    rintro ⟨i,t⟩
    cases t with
    | false => exact hmap (P.adj (i,false))
    | true => exact hmap (P.adj (i,true))
  mem := by
    rintro ⟨i,t⟩
    refine ⟨s((if t then b i else a i),P.neighbor (i,t)),P.mem (i,t),?_⟩
    cases t <;> rfl
  injective := by
    intro k l he
    apply P.injective
    apply Prod.ext
    · have hh := congrArg Prod.fst he
      have hk : (if k.2 then e (b k.1) else e (a k.1))=e (if k.2 then b k.1 else a k.1) := by
        cases k.2 <;> rfl
      have hl : (if l.2 then e (b l.1) else e (a l.1))=e (if l.2 then b l.1 else a l.1) := by
        cases l.2 <;> rfl
      dsimp only at hh
      rw [hk,hl] at hh
      exact e.injective hh
    · exact e.injective (congrArg Prod.snd he)

def enlarge {F' : SimpleGraph V} (P : OriginalEndpointCertificate F a b S) (hFF' : F ≤ F') :
    OriginalEndpointCertificate F' a b S :=
  ⟨P.neighbor,fun k => hFF' (P.adj k),P.mem,P.injective⟩

end
end Cycle12.OriginalEndpointCertificate
