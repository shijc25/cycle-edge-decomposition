import Cycle12.ReservoirSampling12
import Cycle12.BalancedReservoirRouter12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Actual simultaneous reservoirs in three possibly different spanning
graphs. Their size sum pays the common `4 p n` recursion budget. -/
theorem three_reservoir_samples (G : Fin 3 → SimpleGraph V) {p : unitInterval} {h : ℝ}
    (hp : 0 < (p:ℝ)) (hp3 : 3*(p:ℝ) ≤ 1) (hh : 0 < h)
    (hn : 2 ≤ Fintype.card V) (hratio : 4*h ≤ (Fintype.card V:ℝ))
    (hscale : 9437184*(Fintype.card V:ℝ) ≤ (p:ℝ)*h^2)
    (hlog : 3072*log (Fintype.card V:ℝ) ≤ (p:ℝ)*h)
    (hexp : ∀ i, OAI.ErdosGallai.CutExpansion (G i) h) :
    ∃ U : Fin 3 → Finset V, Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      (∀ i, ReservoirSample (G i) (U i) ((p:ℝ)*h) ((9/8)*(p:ℝ)*Fintype.card V)) ∧
      ((univ.biUnion U).card:ℝ) ≤ (27/8)*(p:ℝ)*Fintype.card V ∧
      ((univ.biUnion U).card:ℝ) < 4*(p:ℝ)*Fintype.card V := by
  obtain ⟨U,hdis,hU⟩ := exists_three_disjoint_samples p hp3
    (fun i U => ReservoirSample (G i) U ((p:ℝ)*h) ((9/8)*(p:ℝ)*Fintype.card V))
    (fun i => reservoir_sample_failure (G i) hp hh hn hratio hscale hlog (hexp i))
  have hcard : ((univ.biUnion U).card:ℝ) ≤ (27/8)*(p:ℝ)*Fintype.card V := by
    have hb : (univ.biUnion U).card ≤ ∑ i : Fin 3, (U i).card := card_biUnion_le
    calc
      _ ≤ ∑ i : Fin 3, ((U i).card:ℝ) := by exact_mod_cast hb
      _ ≤ ∑ _i : Fin 3, (9/8)*(p:ℝ)*Fintype.card V := sum_le_sum (fun i _ => (hU i).order_upper)
      _ = _ := by simp; ring
  refine ⟨U,hdis,hU,hcard,hcard.trans_lt ?_⟩
  have hn0 : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (show 0 < Fintype.card V by omega)
  nlinarith only [mul_pos hp hn0]

theorem ReservoirSample.nonempty [Nonempty V] {G : SimpleGraph V} {U : Finset V}
    {z upper : ℝ} (h : ReservoirSample G U z upper) (hz : 0 < z) : U.Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hn := h.neighbors v
  have hpos : 0 < (neighborsIn G v U).card := by
    exact_mod_cast (show (0:ℝ) < (neighborsIn G v U).card by linarith only [hn,hz])
  obtain ⟨w,hw⟩ := card_pos.mp hpos
  exact ⟨w,(mem_filter.mp hw).1⟩

/-- The actual sampled induced graph supports all bounded-load demands;
its order is bounded by the original order in the logarithmic gate. -/
theorem ReservoirSample.route [Nonempty V] {I : Type} [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} {U : Finset V} {z upper : ℝ}
    (hU : ReservoirSample G U z upper) (source : I × Bool → U)
    (hz : 8192 ≤ z) (hlog : 8192*log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card I:ℝ) ≤ z^2)
    (hload : ∀ v : U, ((univ.filter (fun k => source k = v)).card:ℝ) ≤ z/64) :
    ∃ q : ∀ i, (G.induce (U:Set V)).Walk (source (i,false)) (source (i,true)),
      (∀ i, (q i).IsPath) ∧ Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  letI : Nonempty U := (hU.nonempty (by linarith only [hz])).to_subtype
  have hc : (Fintype.card U:ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective (fun v : U => v.val) Subtype.val_injective
  have hn0 : 0 < (Fintype.card U:ℝ) := by exact_mod_cast Fintype.card_pos
  have hl := mul_le_mul_of_nonneg_left (log_le_log hn0 hc) (by norm_num : (0:ℝ) ≤ 8192)
  have hd : ∀ v : U, (15/16)*z ≤ ((G.induce (U:Set V)).degree v:ℝ) := by
    intro v
    have he := sample_induced_degree G U v
    have hh := hU.neighbors v.val
    rw [← he] at hh
    simpa only [SimpleGraph.degree,SimpleGraph.neighborFinset,Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using hh
  exact balanced_reservoir_router _ source hz (hl.trans hlog) hsquare hd hU.induced_expansion hload

end
end Cycle12
