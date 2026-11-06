import Cycle12.Foundations.SimpleCutCount
import Cycle12.Foundations.EdgeSplitExistence

/-! All-cut retention in the same Bernoulli edge split. Contraction counts
half-minimum-cut buckets, and Hoeffding pays for each member of a bucket. -/
namespace Cycle13
open SimpleGraph Finset Real MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable

lemma finite_geometric_level_bound {I : Type} (C : Finset I) (f : I → ℝ)
    (level : I → ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : ∀ j, (∑ i ∈ C.filter (fun i => level i=j), f i) ≤ A*r^j) :
    (∑ i ∈ C, f i) ≤ A/(1-r) := by
  classical
  have he := sum_fiberwise_of_maps_to (s:=C) (t:=C.image level)
    (fun i hi => mem_image_of_mem level hi) f
  rw [← he]
  calc
    _ ≤ ∑ j ∈ C.image level, A*r^j := sum_le_sum (fun j _ => hb j)
    _ = A*∑ j ∈ C.image level, r^j := (mul_sum ..).symm
    _ ≤ A*(∑' j : ℕ, r^j) := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun _ _ => pow_nonneg hr0 _)) hA
    _ = _ := by rw [tsum_geometric_of_lt_one hr0 hr1]; ring

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma splitBank_edge_sum (ω : Sym2 V → Bool) :
    ((splitBank G ω true).edgeSet.ncard:ℝ)=∑ e ∈ G.edgeFinset, splitIndicator e ω := by
  simp only [splitIndicator,Finset.sum_boole]
  rw [← splitBank_edgeFinset]
  simp only [SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']

lemma splitBank_cutGraph (ω : Sym2 V → Bool) (S : Finset V) :
    splitBank (cutGraph G S) ω true=cutGraph (splitBank G ω true) S := by
  ext x y
  change ((G.Adj x y ∧ _) ∧ ω s(x,y)=true) ↔ ((G.Adj x y ∧ ω s(x,y)=true) ∧ _)
  tauto

theorem edge_split_single_cut_failure (q : unitInterval) {ε : ℝ} (hε : 0 ≤ ε)
    (S : Finset V) :
    (edgeSplitMeasure V q).real {ω |
      (cutSize (splitBank G ω true) S:ℝ) < ((q:ℝ)-ε)*cutSize G S} ≤
      exp (-2*ε^2*cutSize G S) := by
  have h := hoeffding_unit_relative_lower_tail (cutGraph G S).edgeFinset
    splitIndicator_measurable (splitIndicator_indep q) splitIndicator_bound (splitIndicator_mean q) hε
  have hc : (cutGraph G S).edgeFinset.card=cutSize G S := by
    simp only [cutSize,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']
  rw [hc] at h
  apply (measureReal_mono (show {ω |
      (cutSize (splitBank G ω true) S:ℝ) < ((q:ℝ)-ε)*cutSize G S} ⊆
      {ω | (∑ e ∈ (cutGraph G S).edgeFinset, splitIndicator e ω) ≤
        ((q:ℝ)-ε)*cutSize G S} from ?_)).trans h
  intro ω hω
  change (∑ e ∈ (cutGraph G S).edgeFinset, splitIndicator e ω) ≤ _
  rw [← splitBank_edge_sum,splitBank_cutGraph]
  exact hω.le

lemma cutSize_empty : cutSize G ∅=0 := by
  have h : cutGraph G ∅=⊥ := by ext x y; simp [cutGraph,SimpleGraph.between_adj]
  simp [cutSize,h]

lemma cutSize_univ : cutSize G univ=0 := by
  have h : cutGraph G univ=⊥ := by ext x y; simp [cutGraph,SimpleGraph.between_adj]
  simp [cutSize,h]

theorem edge_split_all_cuts_failure (q : unitInterval) {ε lam : ℝ}
    (hε : 0 ≤ ε) (hlam : 0 < lam) (hn : 2 ≤ Fintype.card V)
    (hcut : ∀ S : Finset V, S.Nonempty → S ≠ univ → lam ≤ (cutSize G S:ℝ))
    (hr : (Fintype.card V:ℝ)*exp (-ε^2*lam)<1) :
    (edgeSplitMeasure V q).real
      {ω | ¬∀ S : Finset V, ((q:ℝ)-ε)*cutSize G S ≤ (cutSize (splitBank G ω true) S:ℝ)} ≤
    2*(Fintype.card V:ℝ)^3*exp (-2*ε^2*lam)/
      (1-(Fintype.card V:ℝ)*exp (-ε^2*lam)) := by
  classical
  let l := ⌈lam⌉₊
  have hlR : lam ≤ (l:ℝ) := Nat.le_ceil lam
  have hl : 0<l := by exact_mod_cast (show (0:ℝ)<l by linarith)
  have hcutN : ∀ S : Finset V, S.Nonempty → S ≠ univ → l ≤ cutSize G S := by
    intro S hS hSu
    exact Nat.ceil_le.mpr (hcut S hS hSu)
  let C := univ.filter (fun S : Finset V => S.Nonempty ∧ S ≠ univ)
  let E := fun S : Finset V => {ω : Sym2 V → Bool |
    (cutSize (splitBank G ω true) S:ℝ) < ((q:ℝ)-ε)*cutSize G S}
  have hsub : {ω | ¬∀ S : Finset V,
      ((q:ℝ)-ε)*cutSize G S ≤ (cutSize (splitBank G ω true) S:ℝ)} ⊆ ⋃ S ∈ C, E S := by
    intro ω hω
    push_neg at hω
    obtain ⟨S,hS⟩ := hω
    have hSne : S.Nonempty := by
      by_contra! h
      simp only [h,cutSize_empty,Nat.cast_zero,mul_zero,lt_self_iff_false] at hS
    have hSu : S ≠ univ := by
      rintro rfl
      simp only [cutSize_univ,Nat.cast_zero,mul_zero,lt_self_iff_false] at hS
    exact Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨mem_univ _,hSne,hSu⟩,hS⟩⟩
  have hex : ∀ S : C, ∃ j, S.val ∈ cutBucket G l j := by
    intro S
    have hS := (mem_filter.mp S.property).2
    exact mem_some_cutBucket G hl _ (hcutN _ hS.1 hS.2)
  let level : Finset V → ℕ := fun S => if hS : S ∈ C then (hex ⟨S,hS⟩).choose else 0
  have hlevel : ∀ S ∈ C, S ∈ cutBucket G l (level S) := by
    intro S hS
    simpa only [level,dif_pos hS] using (hex ⟨S,hS⟩).choose_spec
  let A : ℝ := 2*(Fintype.card V:ℝ)^3*exp (-2*ε^2*lam)
  let r : ℝ := (Fintype.card V:ℝ)*exp (-ε^2*lam)
  have hsum : (∑ S ∈ C, (edgeSplitMeasure V q).real (E S)) ≤ A/(1-r) := by
    apply finite_geometric_level_bound C _ level (A:=A) (r:=r) (by positivity) (by positivity) hr
    intro j
    let F := C.filter (fun S => level S=j)
    have hF : F ⊆ cutBucket G l j := by
      intro S hS
      have hs := mem_filter.mp hS
      simpa only [hs.2] using hlevel S hs.1
    have hcard : (F.card:ℝ) ≤ 2*(Fintype.card V:ℝ)^(j+3) := by
      exact_mod_cast (card_le_card hF).trans (cutBucket_card G hl hn hcutN j)
    have hprob : ∀ S ∈ F, (edgeSplitMeasure V q).real (E S) ≤ exp (-ε^2*lam*(j+2)) := by
      intro S hS
      have hb := (mem_filter.mp (hF hS)).2.1
      have hbR : ((j:ℝ)+2)*(l:ℝ) ≤ 2*cutSize G S := by exact_mod_cast hb
      have hlamj : lam*((j:ℝ)+2) ≤ 2*cutSize G S := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlR) (show 0≤(j:ℝ)+2 by positivity)]
      apply (edge_split_single_cut_failure G q hε S).trans
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hlamj)]
    calc
      _ ≤ ∑ _S ∈ F, exp (-ε^2*lam*(j+2)) := sum_le_sum hprob
      _ = (F.card:ℝ)*exp (-ε^2*lam*(j+2)) := by simp
      _ ≤ (2*(Fintype.card V:ℝ)^(j+3))*exp (-ε^2*lam*(j+2)) :=
        mul_le_mul_of_nonneg_right hcard (exp_nonneg _)
      _ = A*r^j := by
        have he : exp (-ε^2*lam*((j:ℝ)+2))=exp (-2*ε^2*lam)*(exp (-ε^2*lam))^j := by
          rw [← exp_nat_mul,← exp_add]
          congr 1
          ring
        rw [he]
        simp only [A,r,mul_pow,pow_add]
        ring
  exact (measureReal_mono (μ:=edgeSplitMeasure V q) hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le C E).trans hsum)

theorem exists_edge_split_of_cut_bounds (q : unitInterval) {D g f ε a b c lam : ℝ}
    (hD : 0<D) (hg0 : 0≤g) (hgq : g<(q:ℝ)) (hε : 0≤ε)
    (hfq : f≤(q:ℝ)) (hlam : 0<lam) (hn : 2≤Fintype.card V)
    (hmin : ∀ S : Finset V, S.Nonempty → S ≠ univ → lam≤(cutSize G S:ℝ))
    (hr : (Fintype.card V:ℝ)*exp (-((q:ℝ)-f)^2*lam)<1)
    (hcut : 2*(Fintype.card V:ℝ)^3*exp (-2*((q:ℝ)-f)^2*lam)/
      (1-(Fintype.card V:ℝ)*exp (-((q:ℝ)-f)^2*lam))≤a)
    (hcore : exp (-2*ε^2*G.edgeSet.ncard)≤b)
    (hbranch : (g=f ∧ 0≤c) ∨
      Fintype.card V*exp (-2*D*((q:ℝ)-g)^2/(1-g))≤c)
    (hbudget : a+b+c<1) :
    ∃ ω : Sym2 V → Bool,
      (∀ S : Finset V, f*cutSize G S≤(cutSize (splitBank G ω true) S:ℝ)) ∧
      (1-(q:ℝ)-ε)*G.edgeSet.ncard≤((splitBank G ω false).edgeSet.ncard:ℝ) ∧
      (∀ v : V, D≤((splitBank G ω false).degree v:ℝ) →
        g*G.degree v≤((splitBank G ω true).degree v:ℝ)) := by
  have hfail := (edge_split_all_cuts_failure G q (sub_nonneg.mpr hfq) hlam hn hmin hr).trans hcut
  simp only [sub_sub_cancel] at hfail
  exact exists_simultaneous_edge_split G q hD hg0 hgq hε hfail hcore hbranch hbudget

end
end Cycle13
