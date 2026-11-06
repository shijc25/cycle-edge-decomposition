import Cycle12.Foundations.CarrierEdgeColoring

/-! Constructing an actual weak clique immersion from the carrier's
reserved paths. A proper coloring of the remaining new-branch pairs
assigns each such pair to an old branch. All edge ownership is proved. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

structure PreparedCarrier {V : Type} {t : ℕ} (G : SimpleGraph V)
    (R : SimpleGraph (Fin t)) (A C : Finset (Fin t)) where
  branch : Fin t ↪ V
  supported : ∀ {i j}, R.Adj i j → i ∈ C ∧ j ∈ C
  base : ∀ p : CliquePair t, ¬R.Adj p.1.1 p.1.2 → G.Path (branch p.1.1) (branch p.1.2)
  spoke : ∀ a : A, ∀ v : C, G.Path (branch a.val) (branch v.val)
  base_disjoint : ∀ p q hp hq, p ≠ q →
    Disjoint (base p hp).val.edgeSet (base q hq).val.edgeSet
  spoke_disjoint : ∀ a v b w, (a,v) ≠ (b,w) →
    Disjoint (spoke a v).val.edgeSet (spoke b w).val.edgeSet
  base_spoke_disjoint : ∀ p hp a v,
    Disjoint (base p hp).val.edgeSet (spoke a v).val.edgeSet
  base_avoids : ∀ p hp i, branch i ∈ (base p hp).val.support →
    i = p.1.1 ∨ i = p.1.2
  spoke_avoids : ∀ a v i, branch i ∈ (spoke a v).val.support →
    i = a.val ∨ i = v.val

namespace PreparedCarrier
variable {V : Type} {t : ℕ} {G : SimpleGraph V} {R : SimpleGraph (Fin t)}
    {A C : Finset (Fin t)} (K : PreparedCarrier G R A C) (f : R.lineGraph.Coloring A)

def residualEdge (p : CliquePair t) (hp : R.Adj p.1.1 p.1.2) : R.edgeSet :=
  ⟨p.edge,hp⟩

lemma spoke_disjoint_across (p q : CliquePair t)
    (hp : R.Adj p.1.1 p.1.2) (hq : R.Adj q.1.1 q.1.2) (hpq : p ≠ q)
    (v w : C) (hv : v.val=p.1.1 ∨ v.val=p.1.2) (hw : w.val=q.1.1 ∨ w.val=q.1.2) :
    Disjoint (K.spoke (f (residualEdge p hp)) v).val.edgeSet
      (K.spoke (f (residualEdge q hq)) w).val.edgeSet := by
  apply K.spoke_disjoint
  intro heq
  have hc := congrArg Prod.fst heq
  have hvw := congrArg Prod.snd heq
  change v=w at hvw
  have hadj : R.lineGraph.Adj (residualEdge p hp) (residualEdge q hq) := by
    apply lineGraph_adj_iff_exists.mpr
    refine ⟨?_,v.val,Sym2.mem_iff.mpr hv,?_⟩
    · intro h
      exact hpq (CliquePair.edge_injective (congrArg Subtype.val h))
    · rw [hvw]
      exact Sym2.mem_iff.mpr hw
  exact f.valid hadj hc

def routedWalk (p : CliquePair t) : G.Walk (K.branch p.1.1) (K.branch p.1.2) :=
  if hp : R.Adj p.1.1 p.1.2 then
    (K.spoke (f (residualEdge p hp)) ⟨p.1.1,(K.supported hp).1⟩).val.reverse.append
      (K.spoke (f (residualEdge p hp)) ⟨p.1.2,(K.supported hp).2⟩).val
  else (K.base p hp).val

theorem routedWalk_disjoint : Pairwise (fun p q =>
    Disjoint (K.routedWalk f p).edgeSet (K.routedWalk f q).edgeSet) := by
  intro p q hpq
  by_cases hp : R.Adj p.1.1 p.1.2 <;> by_cases hq : R.Adj q.1.1 q.1.2
  · simp only [routedWalk, dif_pos hp, dif_pos hq, Walk.edgeSet_append, Walk.edgeSet_reverse]
    apply Set.disjoint_left.mpr
    rintro e (hep | hep) (heq | heq)
    · exact Set.disjoint_left.mp
        (K.spoke_disjoint_across f p q hp hq hpq _ _ (Or.inl rfl) (Or.inl rfl)) hep heq
    · exact Set.disjoint_left.mp
        (K.spoke_disjoint_across f p q hp hq hpq _ _ (Or.inl rfl) (Or.inr rfl)) hep heq
    · exact Set.disjoint_left.mp
        (K.spoke_disjoint_across f p q hp hq hpq _ _ (Or.inr rfl) (Or.inl rfl)) hep heq
    · exact Set.disjoint_left.mp
        (K.spoke_disjoint_across f p q hp hq hpq _ _ (Or.inr rfl) (Or.inr rfl)) hep heq
  · simp only [routedWalk, dif_pos hp, dif_neg hq, Walk.edgeSet_append, Walk.edgeSet_reverse]
    exact (K.base_spoke_disjoint q hq _ _).symm.union_left
      (K.base_spoke_disjoint q hq _ _).symm
  · simp only [routedWalk, dif_neg hp, dif_pos hq, Walk.edgeSet_append, Walk.edgeSet_reverse]
    exact (K.base_spoke_disjoint p hp _ _).union_right (K.base_spoke_disjoint p hp _ _)
  · simp only [routedWalk, dif_neg hp, dif_neg hq]
    exact K.base_disjoint p q hp hq hpq

theorem routedWalk_branch_support (p : CliquePair t) (i : Fin t)
    (hi : K.branch i ∈ (K.routedWalk f p).support) :
    i=p.1.1 ∨ i=p.1.2 ∨ ∃ hp : R.Adj p.1.1 p.1.2, i=(f (residualEdge p hp)).val := by
  by_cases hp : R.Adj p.1.1 p.1.2
  · simp only [routedWalk, dif_pos hp, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse] at hi
    rcases hi with hi | hi
    · rcases K.spoke_avoids _ _ i hi with h | h
      · exact Or.inr (Or.inr ⟨hp,h⟩)
      · exact Or.inl h
    · rcases K.spoke_avoids _ _ i hi with h | h
      · exact Or.inr (Or.inr ⟨hp,h⟩)
      · exact Or.inr (Or.inl h)
  · simp only [routedWalk, dif_neg hp] at hi
    rcases K.base_avoids p hp i hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

def model : WeakCliqueImmersion t G where
  branch := K.branch
  route p := (K.routedWalk f p).toPath
  disjoint := by
    intro p q hpq
    exact (K.routedWalk_disjoint f hpq).mono
      (K.routedWalk f p).edges_toPath_subset_edges
      (K.routedWalk f q).edges_toPath_subset_edges

theorem internal_visit_color [Fintype V] (i : Fin t) (p : CliquePair t)
    (hp : p ∈ (K.model f).internalVisits i) :
    ∃ hr : R.Adj p.1.1 p.1.2, i=(f (residualEdge p hr)).val := by
  simp only [WeakCliqueImmersion.internalVisits, mem_filter, mem_univ, true_and] at hp
  have hs := K.routedWalk_branch_support f p i
    ((K.routedWalk f p).support_toPath_subset_support hp.2)
  exact (hs.resolve_left (fun h => hp.1 (Or.inl h))).resolve_left
    (fun h => hp.1 (Or.inr h))

theorem internalVisits_eq_empty_of_not_mem [Fintype V] (i : Fin t) (hi : i ∉ A) :
    (K.model f).internalVisits i = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hr,he⟩ := K.internal_visit_color f i p hp
  exact hi (he ▸ (f (residualEdge p hr)).property)

theorem internalVisits_le_colorSize [Fintype V] (a : A) :
    ((K.model f).internalVisits a.val).card ≤ colorSize f a := by
  let S := (K.model f).internalVisits a.val
  let T := univ.filter (fun e : R.edgeSet => f e=a)
  have hex : ∀ p : S, ∃ hr : R.Adj p.val.1.1 p.val.1.2,
      f (residualEdge p.val hr)=a := by
    intro p
    obtain ⟨hr,he⟩ := K.internal_visit_color f a.val p.val p.property
    exact ⟨hr,Subtype.ext he.symm⟩
  let F : S → T := fun p =>
    ⟨residualEdge p.val (hex p).choose,
      mem_filter.mpr ⟨mem_univ _,(hex p).choose_spec⟩⟩
  apply card_le_card_of_injective (f := F)
  intro p q heq
  apply Subtype.ext
  apply CliquePair.edge_injective
  exact congrArg (fun e : T => e.val.val) heq

include K in
lemma support_subset : R.support ⊆ (C : Set (Fin t)) := by
  intro v hv
  obtain ⟨w,hw⟩ := R.mem_support.mp hv
  exact (K.supported hw).1

/-- Removing isolated vertices from the residual graph preserves its line
graph, including exact edge multiplicities (the residual graph is simple). -/
def restrictedLineIso : (R.induce (C : Set (Fin t))).lineGraph ≃g R.lineGraph := by
  let L := (SimpleGraph.Copy.induce R (C : Set (Fin t))).toLineGraphEmbedding
  have hc : Fintype.card (R.induce (C : Set (Fin t))).edgeSet = Fintype.card R.edgeSet := by
    have h := R.card_edgeFinset_induce_of_support_subset K.support_subset
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at h ⊢
    exact h
  have hs : Function.Surjective L :=
    ((Fintype.bijective_iff_injective_and_card L).mpr ⟨L.injective,hc⟩).2
  exact RelIso.ofSurjective L hs

include K in
theorem exists_balanced_coloring (hpalette : 2*C.card ≤ A.card) :
    ∃ f : R.lineGraph.Coloring A, ∀ a : A,
      colorSize f a ≤ (R.edgeFinset.card+A.card-1)/A.card := by
  have hCcard : Fintype.card (C : Set (Fin t)) = C.card := Fintype.card_coe _
  let f₁ : R.lineGraph.Coloring (Fin A.card) :=
    (endpointSumColoring (R.induce (C : Set (Fin t)))
      (by simpa only [hCcard] using hpalette)).comp K.restrictedLineIso.symm.toHom
  let f₀ := R.lineGraph.recolorOfEquiv (Finset.equivFin A).symm f₁
  simpa only [Fintype.card_coe] using exists_edge_coloring_class_bound R f₀

/-- This constructs the weak model from actual reserved paths and proves
its full branch budget. Existence of the prepared carrier remains separate. -/
theorem exists_budgeted_model [Fintype V] (ht : 4 ≤ t) (heven : Even t)
    (hA : A.card < t) (hC : C.card = t-A.card) (hthree : 3*t < 4*A.card) :
    ∃ M : WeakCliqueImmersion t G, M.branch=K.branch ∧
      ∀ i, 10*{e ∈ M.used | M.branch i ∈ e}.ncard ≤ 11*t := by
  obtain ⟨f,hf⟩ := K.exists_balanced_coloring (by omega)
  have he : 2*R.edgeFinset.card ≤ (t-A.card)*(t-A.card-1) := by
    have h := twice_edges_le_order_product (R.induce (C : Set (Fin t)))
    have heq := R.card_edgeFinset_induce_of_support_subset K.support_subset
    have hCcard : Fintype.card (C : Set (Fin t)) = C.card := Fintype.card_coe _
    simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at h heq ⊢
    rw [heq] at h
    have hCC : Nat.card (C : Set (Fin t)) = t-A.card := by
      rw [Nat.card_eq_fintype_card,hCcard,hC]
    simpa only [hCC] using h
  have hb := balanced_class_branch_budget ht heven hA hthree he
  refine ⟨K.model f,rfl,fun i => ?_⟩
  rw [(K.model f).branch_used_edges]
  by_cases hi : i ∈ A
  · have hv := K.internalVisits_le_colorSize f ⟨i,hi⟩
    have hc := hf ⟨i,hi⟩
    change ((K.model f).internalVisits i).card ≤ colorSize f ⟨i,hi⟩ at hv
    omega
  · rw [K.internalVisits_eq_empty_of_not_mem f i hi, card_empty]
    omega

end PreparedCarrier
end
end Cycle13
