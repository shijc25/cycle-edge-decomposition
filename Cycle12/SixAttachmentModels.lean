import Cycle12.CycleWordEmbedding
import Cycle12.SixCycleIsolatedNeighbors

namespace Cycle12
open SimpleGraph Finset

def sixAttachment : Fin 11 → Finset (Fin 6) :=
  ![{0,2},{1,3},{2,4},{3,5},{0,4},{1,5},{0,3},{1,4},{2,5},{0,2,4},{1,3,5}]

def sixIntoEight : Fin 6 ↪ Fin 8 := Fin.castLEEmb (by decide)

def sixPairEdges (A B : Finset (Fin 6)) : Finset (Sym2 (Fin 8)) :=
  ((univ : Finset (Fin 6)).image fun i => s(sixIntoEight i,sixIntoEight (i+1))) ∪
  (A.image fun i => s(6,sixIntoEight i)) ∪ (B.image fun i => s(7,sixIntoEight i))

theorem six_attachment_complete : ∀ S : Finset (Fin 6),
    (∃ i∈S, ∃ j∈S, i≠j) → (∀ i, i∈S → i+1∉S) →
    ∃ k : Fin 11, S=sixAttachment k := by decide +kernel

theorem six_attachment_injective : Function.Injective sixAttachment := by decide +kernel

/-- The six-cycle and two specified exterior vertices realize the finite
pair model. Extra edges in the ambient graph are allowed. -/
theorem six_pair_model_embedding {V : Type} {G : SimpleGraph V}
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    {x y : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i) (hxy : x≠y)
    (A B : Finset (Fin 6)) (hA : ∀ i∈A, G.Adj x (f i))
    (hB : ∀ i∈B, G.Adj y (f i)) :
    ∃ e : (TerminalCert.graph (sixPairEdges A B)) →g G, Function.Injective e := by
  let e : Fin 8 → V := ![f 0,f 1,f 2,f 3,f 4,f 5,x,y]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [e,f.injective.eq_iff,eq_comm]
  have hcore : ∀ i : Fin 6, e (sixIntoEight i)=f i := by
    intro i
    fin_cases i <;> rfl
  have hadj : ∀ i j, (TerminalCert.graph (sixPairEdges A B)).Adj i j → G.Adj (e i) (e j) := by
    intro i j hij
    have hmem : s(i,j)∈sixPairEdges A B := hij.1
    rcases Finset.mem_union.mp hmem with hleft | hBedge
    · rcases Finset.mem_union.mp hleft with hCedge | hAedge
      · obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hCedge
        apply adj_of_sym2_eq e _ hk
        simpa only [hcore] using hcycle k
      · obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp hAedge
        apply adj_of_sym2_eq e _ hke
        change G.Adj x (e (sixIntoEight k))
        rw [hcore]
        exact hA k hk
    · obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp hBedge
      apply adj_of_sym2_eq e _ hke
      change G.Adj y (e (sixIntoEight k))
      rw [hcore]
      exact hB k hk
  exact ⟨⟨e,fun {_ _} h => hadj _ _ h⟩,he⟩

end Cycle12
