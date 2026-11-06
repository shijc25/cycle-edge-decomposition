import Cycle12.Foundations.AllCutsProbability

/-! The strong bank from a successful Bernoulli split. The final theorem
uses the proved all-cut estimate and only explicit scalar bounds. -/
namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable

theorem exists_strong_routing_bank {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : unitInterval) {E N D T d g f ε a b c : ℝ}
    (hT : 4 ≤ T) (hTD : T ≤ D) (hDN : D ≤ N)
    (horder : (Fintype.card V : ℝ) ≤ N)
    (hE : E ≤ (1 - (q : ℝ) - ε) * G.edgeSet.ncard)
    (hdense : D * N - D ^ 2 / 2 ≤ E)
    (hstop : T * (1 + log (N / T)) ≤ 2 * E / N)
    (hbase : ∀ v : V, d ≤ (G.degree v : ℝ))
    (hg₀ : 0 ≤ g) (hgq : g < (q : ℝ)) (hε : 0 ≤ ε)
    (hcut : (edgeSplitMeasure V q).real
      {ω | ¬∀ S : Finset V, f * cutSize G S ≤ (cutSize (splitBank G ω true) S : ℝ)} ≤ a)
    (hcore : exp (-2 * ε ^ 2 * G.edgeSet.ncard) ≤ b)
    (hbranch : (g = f ∧ 0 ≤ c) ∨
      Fintype.card V * exp (-2 * D * ((q : ℝ) - g) ^ 2 / (1 - g)) ≤ c)
    (hbudget : a + b + c < 1) :
    ∃ J : StrongCliqueImmersion (evenFloor T) G,
      Disjoint J.residue.edgeSet J.used ∧ J.residue.edgeSet ∪ J.used = G.edgeSet ∧
      (∀ S : Finset V, f * cutSize G S ≤ (cutSize J.residue S : ℝ)) ∧
      (∀ i : Fin (evenFloor T), max (D / (1 - g)) d - T ≤
        (J.residue.degree (J.branch i) : ℝ)) := by
  have hD : 0 < D := by linarith
  obtain ⟨ω, hωcut, hωcore, hωbranch⟩ := exists_simultaneous_edge_split G q hD hg₀ hgq hε
    hcut hcore hbranch hbudget
  have hpart := splitBank_partition G ω
  have hEcore : E ≤ ((splitBank G ω false).edgeFinset.card : ℝ) := by
    have h := hE.trans hωcore
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using h
  obtain ⟨J, hF, hdeg⟩ := exists_dense_recycled_strong_model G (splitBank G ω true)
    (splitBank G ω false) hpart.1 hpart.2 hT hTD hDN horder hEcore hdense hstop
    (hgq.trans_le q.2.2) hωbranch hbase
  refine ⟨J, J.residue_disjoint_used, J.residue_used_cover, ?_, hdeg⟩
  intro S
  exact (hωcut S).trans (by exact_mod_cast cutSize_mono hF S)

theorem exists_strong_routing_bank_of_cut_bounds {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : unitInterval) {E N D T d g f ε a b c lam : ℝ}
    (hT : 4≤T) (hTD : T≤D) (hDN : D≤N)
    (horder : (Fintype.card V:ℝ)≤N)
    (hE : E≤(1-(q:ℝ)-ε)*G.edgeSet.ncard)
    (hdense : D*N-D^2/2≤E) (hstop : T*(1+log (N/T))≤2*E/N)
    (hbase : ∀ v : V, d≤(G.degree v:ℝ))
    (hg0 : 0≤g) (hgq : g<(q:ℝ)) (hε : 0≤ε) (hfq : f≤(q:ℝ))
    (hlam : 0<lam) (hn : 2≤Fintype.card V)
    (hmin : ∀ S : Finset V, S.Nonempty → S ≠ univ → lam≤(cutSize G S:ℝ))
    (hr : (Fintype.card V:ℝ)*exp (-((q:ℝ)-f)^2*lam)<1)
    (hcut : 2*(Fintype.card V:ℝ)^3*exp (-2*((q:ℝ)-f)^2*lam)/
      (1-(Fintype.card V:ℝ)*exp (-((q:ℝ)-f)^2*lam))≤a)
    (hcore : exp (-2*ε^2*G.edgeSet.ncard)≤b)
    (hbranch : (g=f ∧ 0≤c) ∨
      Fintype.card V*exp (-2*D*((q:ℝ)-g)^2/(1-g))≤c)
    (hbudget : a+b+c<1) :
    ∃ J : StrongCliqueImmersion (evenFloor T) G,
      Disjoint J.residue.edgeSet J.used ∧ J.residue.edgeSet ∪ J.used=G.edgeSet ∧
      (∀ S : Finset V, f*cutSize G S≤(cutSize J.residue S:ℝ)) ∧
      (∀ i : Fin (evenFloor T), max (D/(1-g)) d-T≤(J.residue.degree (J.branch i):ℝ)) := by
  have hfail := (edge_split_all_cuts_failure G q (sub_nonneg.mpr hfq) hlam hn hmin hr).trans hcut
  simp only [sub_sub_cancel] at hfail
  exact exists_strong_routing_bank G q hT hTD hDN horder hE hdense hstop hbase
    hg0 hgq hε hfail hcore hbranch hbudget

end
end Cycle13
