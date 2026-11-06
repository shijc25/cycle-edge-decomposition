import Cycle12.Foundations.BranchConcentration
import Cycle12.Foundations.StrongRecycling

/-! A single actual Bernoulli edge-splitting experiment, including uniform
control of every possible high-core-degree branch. -/
namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def edgeSplitMeasure (V : Type) [Fintype V] (q : unitInterval) :
    Measure (Sym2 V → Bool) :=
  Measure.pi (fun _ : Sym2 V => bernoulliMeasure true false q)

instance edgeSplitMeasure_probability (q : unitInterval) :
    IsProbabilityMeasure (edgeSplitMeasure V q) := by
  unfold edgeSplitMeasure
  infer_instance

def splitIndicator (e : Sym2 V) (ω : Sym2 V → Bool) : ℝ := if ω e = true then 1 else 0

theorem splitIndicator_indep (q : unitInterval) :
    iIndepFun (splitIndicator (V := V)) (edgeSplitMeasure V q) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun b : Bool => if b = true then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

theorem splitIndicator_measurable (e : Sym2 V) : Measurable (splitIndicator e) := by
  unfold splitIndicator
  fun_prop

theorem splitIndicator_bound (e : Sym2 V) (ω : Sym2 V → Bool) :
    splitIndicator e ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold splitIndicator
  split_ifs <;> norm_num

theorem splitIndicator_mean (q : unitInterval) (e : Sym2 V) :
    ∫ ω, splitIndicator e ω ∂edgeSplitMeasure V q = (q : ℝ) := by
  have hl := (measurePreserving_eval (fun _ : Sym2 V => bernoulliMeasure true false q) e).hasLaw
  have hi := hl.integral_comp (f := fun b : Bool => if b = true then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [integral_bernoulliMeasure] at hi
  simpa [edgeSplitMeasure, splitIndicator] using hi

def splitBank (G : SimpleGraph V) (ω : Sym2 V → Bool) (b : Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω s(x,y) = b
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

theorem splitBank_edges (G : SimpleGraph V) (ω : Sym2 V → Bool) (b : Bool) :
    (splitBank G ω b).edgeSet = G.edgeSet ∩ {e | ω e = b} := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rfl

theorem splitBank_partition (G : SimpleGraph V) (ω : Sym2 V → Bool) :
    Disjoint (splitBank G ω true) (splitBank G ω false) ∧
      splitBank G ω true ⊔ splitBank G ω false = G := by
  constructor
  · apply SimpleGraph.disjoint_left.mpr
    intro x y ht hf
    have he := ht.2.symm.trans hf.2
    cases he
  · ext x y
    change (G.Adj x y ∧ ω s(x,y) = true ∨ G.Adj x y ∧ ω s(x,y) = false) ↔ G.Adj x y
    cases ω s(x,y) <;> simp

theorem splitBank_edgeFinset (G : SimpleGraph V) (ω : Sym2 V → Bool) (b : Bool) :
    (splitBank G ω b).edgeFinset = G.edgeFinset.filter (fun e => ω e = b) := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, Finset.mem_filter, splitBank_edges,
    Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem splitBank_core_edge_sum (G : SimpleGraph V) (ω : Sym2 V → Bool) :
    ((splitBank G ω false).edgeSet.ncard : ℝ) =
      ∑ e ∈ G.edgeFinset, (1 - splitIndicator e ω) := by
  have hf : ∀ e : Sym2 V, (1 - splitIndicator e ω) = if ω e = false then (1 : ℝ) else 0 := by
    intro e
    unfold splitIndicator
    cases ω e <;> norm_num
  simp_rw [hf]
  rw [Finset.sum_boole, ← splitBank_edgeFinset]
  simp only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']

theorem splitBank_incidence (G : SimpleGraph V) (ω : Sym2 V → Bool) (b : Bool) (v : V) :
    (splitBank G ω b).incidenceFinset v = (G.incidenceFinset v).filter (fun e => ω e = b) := by
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, Finset.mem_filter,
    SimpleGraph.incidenceSet, splitBank_edges, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem splitBank_degree_sum (G : SimpleGraph V) (ω : Sym2 V → Bool) (v : V) :
    ((splitBank G ω true).degree v : ℝ) = ∑ e ∈ G.incidenceFinset v, splitIndicator e ω := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, splitBank_incidence]
  simp only [splitIndicator, Finset.sum_boole]

theorem splitBank_core_degree (G : SimpleGraph V) (ω : Sym2 V → Bool) (v : V) :
    ((splitBank G ω false).degree v : ℝ) =
      (G.degree v : ℝ) - ∑ e ∈ G.incidenceFinset v, splitIndicator e ω := by
  have hp := splitBank_partition G ω
  have hd := degree_edge_partition _ _ _ hp.1 hp.2 v
  have hr : ((splitBank G ω true).degree v : ℝ) + (splitBank G ω false).degree v = G.degree v := by
    exact_mod_cast hd
  rw [splitBank_degree_sum] at hr
  linarith

theorem edge_split_branch_failure (G : SimpleGraph V) (q : unitInterval) {D g : ℝ}
    (hD : 0 < D) (hg₀ : 0 ≤ g) (hgq : g < (q : ℝ)) :
    (edgeSplitMeasure V q).real {ω | ∃ v : V,
      D ≤ ((splitBank G ω false).degree v : ℝ) ∧
        ((splitBank G ω true).degree v : ℝ) < g * G.degree v} ≤
      Fintype.card V * exp (-2 * D * ((q : ℝ) - g) ^ 2 / (1 - g)) := by
  have h := uniform_conditional_degree_failure (fun v : V => G.incidenceFinset v) splitIndicator_measurable
    (splitIndicator_indep q) splitIndicator_bound (splitIndicator_mean q) hD hg₀ hgq q.2.2
  simpa only [splitBank_core_degree, splitBank_degree_sum,
    SimpleGraph.card_incidenceFinset_eq_degree] using h

theorem edge_split_core_edge_failure (G : SimpleGraph V) (q : unitInterval) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (edgeSplitMeasure V q).real {ω |
      ((splitBank G ω false).edgeSet.ncard : ℝ) < (1 - (q : ℝ) - ε) * G.edgeSet.ncard} ≤
        exp (-2 * ε ^ 2 * G.edgeSet.ncard) := by
  let Y : Sym2 V → (Sym2 V → Bool) → ℝ := fun e ω => 1 - splitIndicator e ω
  have hi : iIndepFun Y (edgeSplitMeasure V q) :=
    (splitIndicator_indep q).comp (fun _ x => 1 - x) (fun _ => by fun_prop)
  have hmean : ∀ e : Sym2 V, ∫ ω, Y e ω ∂edgeSplitMeasure V q = 1 - (q : ℝ) := by
    intro e
    have hiX : Integrable (splitIndicator e) (edgeSplitMeasure V q) :=
      Integrable.of_mem_Icc 0 1 (splitIndicator_measurable e).aemeasurable
        (ae_of_all _ (splitIndicator_bound e))
    rw [show Y e = fun ω => 1 - splitIndicator e ω from rfl,
      integral_sub (integrable_const _) hiX, integral_const, splitIndicator_mean]
    simp
  have hb : ∀ e ω, Y e ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro e ω
    have h := splitIndicator_bound e ω
    exact ⟨by dsimp [Y]; linarith [h.2], by dsimp [Y]; linarith [h.1]⟩
  have h := hoeffding_unit_relative_lower_tail G.edgeFinset
    (X := Y) (fun e => measurable_const.sub (splitIndicator_measurable e)) hi hb hmean hε
  have hc : G.edgeFinset.card = G.edgeSet.ncard := by
    simp only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [hc] at h
  apply (measureReal_mono (show {ω |
      ((splitBank G ω false).edgeSet.ncard : ℝ) < (1 - (q : ℝ) - ε) * G.edgeSet.ncard} ⊆
      {ω | (∑ e ∈ G.edgeFinset, Y e ω) ≤ (1 - (q : ℝ) - ε) * G.edgeSet.ncard} from ?_)).trans h
  intro ω hω
  change (∑ e ∈ G.edgeFinset, (1 - splitIndicator e ω)) ≤ _
  rw [← splitBank_core_edge_sum]
  exact hω.le

end
end Cycle13
