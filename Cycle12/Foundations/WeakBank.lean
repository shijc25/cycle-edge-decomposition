import Cycle12.Foundations.DenseWeak
import Cycle12.Foundations.AllCutsProbability

namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable

theorem exists_weak_routing_bank_of_cut_bounds {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : unitInterval) {E N D T d g f ε a b c lam : ℝ}
    (hT : 5 ≤ T) (hTD : 7*T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V:ℝ) ≤ N)
    (hE : E ≤ (1-(q:ℝ)-ε)*G.edgeSet.ncard)
    (hdense : D*N-D^2/2 ≤ E)
    (hbase : ∀ v, d ≤ (G.degree v:ℝ))
    (hg0 : 0 ≤ g) (hgq : g < (q:ℝ)) (hε : 0 ≤ ε) (hfq : f ≤ (q:ℝ))
    (hlam : 0 < lam) (hn : 2 ≤ Fintype.card V)
    (hmin : ∀ S : Finset V, S.Nonempty → S≠univ → lam ≤ (cutSize G S:ℝ))
    (hr : (Fintype.card V:ℝ)*exp (-((q:ℝ)-f)^2*lam) < 1)
    (hcut : 2*(Fintype.card V:ℝ)^3*exp (-2*((q:ℝ)-f)^2*lam)/
      (1-(Fintype.card V:ℝ)*exp (-((q:ℝ)-f)^2*lam)) ≤ a)
    (hcore : exp (-2*ε^2*G.edgeSet.ncard) ≤ b)
    (hbranch : (g=f ∧ 0 ≤ c) ∨ Fintype.card V*exp (-2*D*((q:ℝ)-g)^2/(1-g)) ≤ c)
    (hbudget : a+b+c < 1) :
    ∃ J : WeakCliqueImmersion (evenFloor (T-1)) G,
      Disjoint J.residue.edgeSet J.used ∧ J.residue.edgeSet∪J.used=G.edgeSet ∧
      (∀ S : Finset V, f*cutSize G S ≤ (cutSize J.residue S:ℝ)) ∧
      ∀ i, max (D/(1-g)) d-11/10*T ≤ (J.residue.degree (J.branch i):ℝ) := by
  have hfail := (edge_split_all_cuts_failure G q (sub_nonneg.mpr hfq) hlam hn hmin hr).trans hcut
  simp only [sub_sub_cancel] at hfail
  obtain ⟨ω,hωcut,hωcore,hωbranch⟩ := exists_simultaneous_edge_split G q (by linarith : 0 < D)
    hg0 hgq hε hfail hcore hbranch hbudget
  have hpart := splitBank_partition G ω
  have hEcore : E ≤ ((splitBank G ω false).edgeFinset.card:ℝ) := by
    have hh := hE.trans hωcore
    simpa only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card'] using hh
  obtain ⟨J,hF,hdegree⟩ := exists_dense_recycled_weak_model G (splitBank G ω true)
    (splitBank G ω false) hpart.1 hpart.2 hT hTD hDN horder hEcore hdense
    (hgq.trans_le q.2.2) hωbranch hbase
  refine ⟨J,J.residue_disjoint_used,J.residue_used_cover,?_,hdegree⟩
  intro S
  exact (hωcut S).trans (by exact_mod_cast cutSize_mono hF S)

end
end Cycle13
