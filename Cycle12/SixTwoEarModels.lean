import Cycle12.SixEarCompatibility

namespace Cycle12
open SimpleGraph Finset

def sixIntoTen : Fin 6 ↪ Fin 10 := Fin.castLEEmb (by decide)

def sixTwoEarEdges (a b : Fin 6) : Finset (Sym2 (Fin 10)) :=
  ((univ : Finset (Fin 6)).image fun i => s(sixIntoTen i,sixIntoTen (i+1))) ∪
  {s(0,6),s(6,7),s(3,7)} ∪ {s(sixIntoTen a,8),s(8,9),s(sixIntoTen b,9)}

theorem six_two_ear_model_embedding {V : Type} {G : SimpleGraph V}
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    {x y z w : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i)
    (hz : ∀ i, z≠f i) (hw : ∀ i, w≠f i)
    (hxy : x≠y) (hxz : x≠z) (hxw : x≠w)
    (hyz : y≠z) (hyw : y≠w) (hzw : z≠w)
    (hxa : G.Adj x (f 0)) (hxyadj : G.Adj x y) (hyb : G.Adj y (f 3))
    (a b : Fin 6) (hza : G.Adj z (f a)) (hzwadj : G.Adj z w) (hwb : G.Adj w (f b)) :
    ∃ e : (TerminalCert.graph (sixTwoEarEdges a b)) →g G, Function.Injective e := by
  let e : Fin 10 → V := ![f 0,f 1,f 2,f 3,f 4,f 5,x,y,z,w]
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [e,f.injective.eq_iff,hx,hy,hz,hw,hxy,hxz,hxw,hyz,hyw,hzw,eq_comm] at hij ⊢
  have hcore : ∀ i : Fin 6, e (sixIntoTen i)=f i := by
    intro i
    fin_cases i <;> rfl
  have hadj : ∀ i j, (TerminalCert.graph (sixTwoEarEdges a b)).Adj i j → G.Adj (e i) (e j) := by
    intro i j hij
    have hmem : s(i,j)∈sixTwoEarEdges a b := hij.1
    rcases Finset.mem_union.mp hmem with hleft | hear2
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
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hear2
      rcases hear2 with hh | hh | hh
      · apply adj_of_sym2_eq e _ hh.symm
        change G.Adj (e (sixIntoTen a)) z
        rw [hcore]
        exact hza.symm
      · apply adj_of_sym2_eq e _ hh.symm
        exact hzwadj
      · apply adj_of_sym2_eq e _ hh.symm
        change G.Adj (e (sixIntoTen b)) w
        rw [hcore]
        exact hwb.symm
  exact ⟨⟨e,fun {_ _} h => hadj _ _ h⟩,he⟩

end Cycle12
