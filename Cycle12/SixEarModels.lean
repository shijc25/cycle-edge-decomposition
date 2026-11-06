import Cycle12.SixCycleIndependentClassification

namespace Cycle12
open SimpleGraph Finset

def sixIntoNine : Fin 6 ↪ Fin 9 := Fin.castLEEmb (by decide)

def sixEarEdges (A : Finset (Fin 6)) : Finset (Sym2 (Fin 9)) :=
  ((univ : Finset (Fin 6)).image fun i => s(sixIntoNine i,sixIntoNine (i+1))) ∪
  {s(0,6),s(6,7),s(3,7)} ∪ (A.image fun i => s(8,sixIntoNine i))

theorem six_ear_model_embedding {V : Type} {G : SimpleGraph V}
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    {x y z : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i) (hz : ∀ i, z≠f i)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hxa : G.Adj x (f 0)) (hxyadj : G.Adj x y) (hyb : G.Adj y (f 3))
    (A : Finset (Fin 6)) (hA : ∀ i∈A, G.Adj z (f i)) :
    ∃ e : (TerminalCert.graph (sixEarEdges A)) →g G, Function.Injective e := by
  let e : Fin 9 → V := ![f 0,f 1,f 2,f 3,f 4,f 5,x,y,z]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [e,f.injective.eq_iff,hx,hy,hz,hxy,hxz,hyz,eq_comm] at hij ⊢
  have hcore : ∀ i : Fin 6, e (sixIntoNine i)=f i := by
    intro i
    fin_cases i <;> rfl
  have hadj : ∀ i j, (TerminalCert.graph (sixEarEdges A)).Adj i j → G.Adj (e i) (e j) := by
    intro i j hij
    have hmem : s(i,j)∈sixEarEdges A := hij.1
    rcases Finset.mem_union.mp hmem with hleft | hAedge
    · rcases Finset.mem_union.mp hleft with hCedge | hear
      · obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hCedge
        apply adj_of_sym2_eq e _ hk
        simpa only [hcore] using hcycle k
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hear
        rcases hear with hh | hh | hh
        · apply adj_of_sym2_eq e _ hh.symm
          exact hxa.symm
        · apply adj_of_sym2_eq e _ hh.symm
          exact hxyadj
        · apply adj_of_sym2_eq e _ hh.symm
          exact hyb.symm
    · obtain ⟨k,hk,hke⟩ := Finset.mem_image.mp hAedge
      apply adj_of_sym2_eq e _ hke
      change G.Adj z (e (sixIntoNine k))
      rw [hcore]
      exact hA k hk
  exact ⟨⟨e,fun {_ _} h => hadj _ _ h⟩,he⟩

theorem six_attachment_vertex_no_external_neighbors {V : Type} {G : SimpleGraph V}
    {f : Fin 6 ↪ V} {i : Fin 11} {x : V} (hx : SixAttachmentVertex G f i x)
    {y : V} (hy : ∀ k, y≠f k) : ¬G.Adj x y := by
  intro hxy
  obtain ⟨k,_,hk⟩ := (hx.2 y).mp hxy
  exact hy k hk.symm

end Cycle12
