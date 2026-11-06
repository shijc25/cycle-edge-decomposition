import Cycle12.Independent.SetFamilyTail
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Cycle12.Foundations.PartitionListColoring

/-! Janson's lower tail for the number of actual edges retained by a
Bernoulli vertex sample. The dependency bound counts adjacent edge pairs. -/
namespace Cycle13
open SimpleGraph Finset MeasureTheory ProbabilityTheory unitInterval
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def edgeVertexSet (e : G.edgeSet) : Finset V := e.val.toFinset

lemma edgeVertexSet_card (e : G.edgeSet) : (edgeVertexSet G e).card=2 :=
  Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.property)

lemma edgeVertexSet_injective : Function.Injective (edgeVertexSet G) := by
  intro e f h
  apply Subtype.ext
  apply SetLike.coe_injective
  ext v
  have hh := Finset.ext_iff.mp h v
  simpa [edgeVertexSet] using hh

lemma edgeVertexSet_union_card (e f : G.edgeSet) (hne : e ≠ f) :
    3 ≤ (edgeVertexSet G e ∪ edgeVertexSet G f).card := by
  have he := edgeVertexSet_card G e
  have hf := edgeVertexSet_card G f
  by_contra! h
  have h₁ : edgeVertexSet G e=edgeVertexSet G e ∪ edgeVertexSet G f :=
    eq_of_subset_of_card_le subset_union_left (by omega)
  have h₂ : edgeVertexSet G f=edgeVertexSet G e ∪ edgeVertexSet G f :=
    eq_of_subset_of_card_le subset_union_right (by omega)
  exact hne (edgeVertexSet_injective G (h₁.trans h₂.symm))

lemma incident_edges_card (v : V) :
    (univ.filter (fun e : G.edgeSet => v ∈ e.val)).card=G.degree v := by
  rw [← Fintype.card_subtype, ← G.card_incidenceSet_eq_degree]
  apply Fintype.card_congr
  exact {
    toFun e := ⟨e.val.val,e.val.property,e.property⟩
    invFun e := ⟨⟨e.val,e.property.1⟩,e.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }

theorem lineGraph_degree_bound (e : G.edgeSet) :
    G.lineGraph.degree e+2 ≤ G.degree e.val.out.1+G.degree e.val.out.2 := by
  classical
  let A := univ.filter (fun f : G.edgeSet => e.val.out.1 ∈ f.val)
  let B := univ.filter (fun f : G.edgeSet => e.val.out.2 ∈ f.val)
  have hA : e ∈ A := mem_filter.mpr ⟨mem_univ _,Sym2.out_fst_mem _⟩
  have hB : e ∈ B := mem_filter.mpr ⟨mem_univ _,Sym2.out_snd_mem _⟩
  have hs : G.lineGraph.neighborFinset e ⊆ A.erase e ∪ B.erase e := by
    intro f hf
    have hh := lineGraph_adj_iff_exists.mp ((G.lineGraph.mem_neighborFinset e f).mp hf)
    obtain ⟨v,hve,hvf⟩ := hh.2
    rw [← e.val.out_eq,Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · exact mem_union_left _ (mem_erase.mpr ⟨hh.1.symm,mem_filter.mpr ⟨mem_univ _,hvf⟩⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨hh.1.symm,mem_filter.mpr ⟨mem_univ _,hvf⟩⟩)
  have h₁ := card_le_card hs
  have h₂ := card_union_le (A.erase e) (B.erase e)
  have h₃ := card_erase_add_one hA
  have h₄ := card_erase_add_one hB
  have hcA : A.card=G.degree e.val.out.1 := incident_edges_card G _
  have hcB : B.card=G.degree e.val.out.2 := incident_edges_card G _
  rw [G.lineGraph.card_neighborFinset_eq_degree] at h₁
  omega

def edgeDependencies : Finset (G.edgeSet × G.edgeSet) :=
  univ.filter (fun q => G.lineGraph.Adj q.1 q.2)

lemma edgeDependencies_valid (e f : G.edgeSet) (hne : e ≠ f)
    (h : (e,f) ∉ edgeDependencies G) :
    Disjoint (edgeVertexSet G e : Set V) (edgeVertexSet G f : Set V) := by
  apply Set.disjoint_left.mpr
  intro v hve hvf
  apply h
  exact mem_filter.mpr ⟨mem_univ _,lineGraph_adj_iff_exists.mpr
    ⟨hne,v,by simpa [edgeVertexSet] using hve,by simpa [edgeVertexSet] using hvf⟩⟩

lemma edgeDependencies_card :
    (edgeDependencies G).card=∑ e : G.edgeSet, G.lineGraph.degree e := by
  unfold edgeDependencies
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro e _
  rw [← sum_filter]
  simp only [sum_const,smul_eq_mul,mul_one]
  rw [← G.lineGraph.card_neighborFinset_eq_degree e]
  congr 1
  ext f
  simp

def sampledEdgeCount (U : Set V) : ℕ :=
  ({e : G.edgeSet | (edgeVertexSet G e : Set V) ⊆ U} : Set G.edgeSet).ncard

theorem vertex_sample_edge_lower_tail (p : I) {D : ℕ}
    (hD : ∀ v w, G.Adj v w → G.degree v+G.degree w ≤ D+2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2) :
    (setBernoulli Set.univ p {U : Set V |
      (sampledEdgeCount G U:ℝ) ≤ (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-t}).toReal ≤
    Real.exp (-t^2/(2*((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
      (Fintype.card G.edgeSet:ℝ)*D*(p:ℝ)^3))) := by
  have hcard : ∀ e : G.edgeSet, (G.lineGraph.neighborFinset e).card ≤ D := by
    intro e
    rw [G.lineGraph.card_neighborFinset_eq_degree]
    have h₁ := lineGraph_degree_bound G e
    have h₂ := hD _ _ (edge_out_adj G e)
    omega
  have hdis : ∀ e f : G.edgeSet,
      f ∈ univ \ insert e (G.lineGraph.neighborFinset e) →
        Disjoint (edgeVertexSet G e) (edgeVertexSet G f) := by
    intro e f hf
    have hnot := (mem_sdiff.mp hf).2
    have hfe : f ≠ e := by intro he; subst f; exact hnot (mem_insert_self _ _)
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    apply hnot
    apply mem_insert_of_mem
    apply (G.lineGraph.mem_neighborFinset e f).mpr
    exact lineGraph_adj_iff_exists.mpr ⟨hfe.symm,v,
      by simpa [edgeVertexSet] using hve,by simpa [edgeVertexSet] using hvf⟩
  have htail := Cycle12.Independent.setFamily_lower_tail p (edgeVertexSet G)
    (fun e => G.lineGraph.neighborFinset e) (edgeVertexSet_card G) (by intro e; simp) hcard
    (fun e f hf => edgeVertexSet_union_card G e f
      (lineGraph_adj_iff_exists.mp ((G.lineGraph.mem_neighborFinset e f).mp hf)).1)
    hdis ht0 ht
  have hcount : ∀ S : Finset V,
      Cycle12.Independent.indicatorCount (edgeVertexSet G) univ S =
        (sampledEdgeCount G (S:Set V):ℝ) := by
    intro S
    have hset : {e : G.edgeSet | (edgeVertexSet G e:Set V) ⊆ (S:Set V)} =
        (univ.filter (fun e : G.edgeSet => edgeVertexSet G e ⊆ S):Set G.edgeSet) := by
      ext e
      simp
    unfold sampledEdgeCount
    rw [hset,Set.ncard_coe_finset]
    simp [Cycle12.Independent.indicatorCount,containsIndicator,← sum_filter]
  simp_rw [hcount] at htail
  rw [bernoulliSubset_prob_eq_setBernoulli p
    (fun S : Set V => (sampledEdgeCount G S:ℝ) ≤
      (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-t)] at htail
  exact htail

end
end Cycle13
