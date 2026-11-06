import Cycle12.OriginalEndpointFamilies12
import Cycle12.PreparedMatchingRequests12
import Cycle12.PreparedBatchPaths12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V]

/-- Requests retain both their actual core owner and one joint injection
into the original edge incidences. The charged class is an explicit parameter. -/
structure OwnedEndpointFamily12 (G : SimpleGraph V) (A : I → Finset V)
    (S : Set (Sym2 V)) where
  Index : Type
  finite : Fintype Index
  owner : Index → I
  left : Index → V
  right : Index → V
  left_mem : ∀ j,left j∈A (owner j)
  right_mem : ∀ j,right j∈A (owner j)
  certificate : OriginalEndpointCertificate G left right S
attribute [instance] OwnedEndpointFamily12.finite

namespace OwnedEndpointFamily12
variable {G : SimpleGraph V} {A : I → Finset V} {S : Set (Sym2 V)}

def empty (G : SimpleGraph V) (A : I → Finset V) : OwnedEndpointFamily12 G A ∅ where
  Index := Empty
  finite := inferInstance
  owner := Empty.elim
  left := Empty.elim
  right := Empty.elim
  left_mem := fun j => j.elim
  right_mem := fun j => j.elim
  certificate := {
    neighbor := fun k => k.1.elim
    adj := fun k => k.1.elim
    mem := fun k => k.1.elim
    injective := by intro k; exact k.1.elim }

def enlarge {H : SimpleGraph V} (P : OwnedEndpointFamily12 G A S) (hGH : G ≤ H) :
    OwnedEndpointFamily12 H A S where
  Index := P.Index
  finite := P.finite
  owner := P.owner
  left := P.left
  right := P.right
  left_mem := P.left_mem
  right_mem := P.right_mem
  certificate := P.certificate.enlarge hGH

variable {J : Type} [Fintype J]

def sigma {S : J → Set (Sym2 V)} (P : ∀ j,OwnedEndpointFamily12 G A (S j))
    (hd : Pairwise (fun j k => Disjoint (S j) (S k))) :
    OwnedEndpointFamily12 G A (⋃ j,S j) where
  Index := Σ j,(P j).Index
  finite := inferInstance
  owner := fun j => (P j.1).owner j.2
  left := fun j => (P j.1).left j.2
  right := fun j => (P j.1).right j.2
  left_mem := fun j => (P j.1).left_mem j.2
  right_mem := fun j => (P j.1).right_mem j.2
  certificate := OriginalEndpointCertificate.sigma (fun j => (P j).certificate) hd

def map {W K : Type} [Fintype W] [DecidableEq W] {H : SimpleGraph W} {B : K → Finset W}
    (P : OwnedEndpointFamily12 G A S) (e : V ↪ W) (owner : I → K)
    (he : ∀ {x y},G.Adj x y → H.Adj (e x) (e y))
    (hA : ∀ r v,v∈A r → e v∈B (owner r)) :
    OwnedEndpointFamily12 H B (Sym2.map e '' S) where
  Index := P.Index
  finite := P.finite
  owner := owner ∘ P.owner
  left := e ∘ P.left
  right := e ∘ P.right
  left_mem := fun j => hA _ _ (P.left_mem j)
  right_mem := fun j => hA _ _ (P.right_mem j)
  certificate := P.certificate.map e he

theorem load_le (P : OwnedEndpointFamily12 G A S) (v : V) :
    endpointLoad P.left P.right v ≤ G.degree v := P.certificate.load_le v

end OwnedEndpointFamily12

variable [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}
  {e : Sym2 (Option I)} {H : SimpleGraph V}

/-- Instantiate the alternating requests of the exact matching witness
stored in each actual prepared class. Other classes create no requests. -/
def PreparedClassLedger12.matchingFamily (D : PreparedClassLedger12 G A Q e H)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) :
    OwnedEndpointFamily12 (edgeLabelGraph G (blockLabel A) e) A D.matchingEdges := by
  cases D with
  | crossing r t hrt he P hh =>
    have hcross : ∀ {x y},(edgeLabelGraph G (blockLabel A) e).Adj x y →
        (x∈A r ∧ y∈A t) ∨ (x∈A t ∧ y∈A r) := by
      intro x y hxy
      rw [he] at hxy
      exact ((block_cross_graph G A hd r t x y).mp hxy).2
    let R := Classical.choice (P.request_data hcross)
    let cert := Classical.choice (R.certificate_exists P.isMatching)
    exact {
      Index := R.Index
      finite := inferInstance
      owner := Sum.elim (fun _ => r) (fun _ => t)
      left := R.left
      right := R.right
      left_mem := by
        intro j
        cases j with
        | inl j => exact (R.endpoints (.inl j)).1
        | inr j => exact (R.endpoints (.inr j)).1
      right_mem := by
        intro j
        cases j with
        | inl j => exact (R.endpoints (.inl j)).2
        | inr j => exact (R.endpoints (.inr j)).2
      certificate := cert.enlarge (fun _ _ h => h.1.1) }
  | internal r he hh => exact OwnedEndpointFamily12.empty _ _
  | external he hh => exact OwnedEndpointFamily12.empty _ _
  | outside r he P hh => exact OwnedEndpointFamily12.empty _ _

namespace PreparedBlockBatch12

def classMatchingFamily (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) (e : Sym2 (Option I)) :
    OwnedEndpointFamily12 G A (P.classes e).ledger.matchingEdges :=
  ((P.classes e).ledger.matchingFamily hd).enlarge (fun _ _ h => h.1)

theorem classMatching_disjoint (P : PreparedBlockBatch12 G A Q) :
    Pairwise (fun e f => Disjoint (P.classes e).ledger.matchingEdges (P.classes f).ledger.matchingEdges) := by
  intro e f hef
  exact ((edgeLabelGraph_partition G (blockLabel A)).1 hef).mono
    (P.classes e).ledger.matching_subset (P.classes f).ledger.matching_subset

/-- All matching requests of a prepared batch share a single original
incidence budget. No endpoint is charged once per label class. -/
def matchingFamily (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) :
    OwnedEndpointFamily12 G A P.matchingEdges :=
  OwnedEndpointFamily12.sigma (P.classMatchingFamily hd) P.classMatching_disjoint

end PreparedBlockBatch12
end
end Cycle12
