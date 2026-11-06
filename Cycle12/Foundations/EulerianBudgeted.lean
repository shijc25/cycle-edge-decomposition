import Cycle12.Foundations.SeedCarrier

/-! The Eulerian degree-deficiency theorem with an actual 11t/10-budgeted
weak clique model. The proof uses a true minimum-order counterexample,
maximum ordered seed, controlled suppression, and both carrier regimes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem budgeted_clique_of_even_deficiency {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {d t : ℕ} (ht : 4≤t) (hteven : Even t) (hd : 7*t≤d)
    (heven : ∀ v, Even (G.degree v)) (hdef : degreeDeficiency G d<d) :
    HasBudgetedClique t G := by
  by_contra hbad
  obtain ⟨n,H,hn,hHe,hHd,hHb,hmin⟩ := exists_minimum_bad G heven hdef hbad
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨root,hroot⟩ := exists_degree_ge_of_deficiency H hHd
  obtain ⟨p,A,hmax⟩ := OrderedSeed.exists_maximal H root (by omega : 1<t)
  obtain ⟨B,hB,hBt,hout,hmiss⟩ := A.external_block hd hroot hHb hHe hHd hmin
  have hlarge := A.block_large_of_maximal B hmax hB hout hmiss
  exact hHb (A.model_of_external_block hd hroot ht hteven B hBt hlarge hout hmiss)

end
end Cycle13
