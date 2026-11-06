import Cycle12.Foundations.ReservoirPorts

/-! Source-to-reservoir capacity cuts imply the separator hypothesis in
the port graph. Outside sources cannot be used as transit vertices. -/
namespace Cycle13.ReservoirPorts
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def internalGraph (G : SimpleGraph V) (U : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem internalGraph_le (G : SimpleGraph V) (U : Finset V) : internalGraph G U ≤ G :=
  fun _ _ h => h.1

theorem internal_cut_mem (G : SimpleGraph V) (U S : Finset V)
    (e : (cutGraph (internalGraph G U) S).edgeSet) {v : V} (hv : v ∈ e.val) : v ∈ U := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    change (G.Adj x y ∧ x ∈ U ∧ y ∈ U) ∧ _ at he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact he.1.2.1
    · exact he.1.2.2

/-- The exact directed-source cut condition. `Y` is any chosen set of
sources and `S` any reservoir side. All attachments from `Y` to `U\S`
point into the reservoir. -/
def CutCondition (G : SimpleGraph V) (A U B : Finset V) (c : ℕ) : Prop :=
  ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U →
    Y.card ≤ cutSize (internalGraph G U) S + (G.interedges Y (U \ S)).card +
      c * (B ∩ S).card

theorem separator_card_bound (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (hAU : Disjoint A U) (hcut : CutCondition G A U B c)
    (X : Finset (Vertex G A B c))
    (hsep : Menger.Separates (graph G A U B c) (sources G A B c) (targets G A B c) X) :
    A.card ≤ X.card := by
  let S := side G A U B c X
  let Y₀ := univ.filter (fun a : A => Sum.inl a ∉ X)
  let Y := Y₀.image (Subtype.val : A → V)
  let R := univ \ Y₀
  have hYA : Y ⊆ A := by
    intro a ha
    obtain ⟨a', _, rfl⟩ := mem_image.mp ha
    exact a'.property
  have hsurv : ∀ a (ha : a ∈ Y), Sum.inl (⟨a, hYA ha⟩ : A) ∉ X := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    exact (mem_filter.mp ha').2
  have hsum : R.card + Y.card = A.card := by
    rw [show Y.card = Y₀.card from card_image_of_injective _ Subtype.val_injective]
    simpa only [R, card_univ, Fintype.card_coe] using
      card_sdiff_add_card_eq_card (subset_univ Y₀)
  have hcut' := hcut Y hYA S (side_subset G A U B c X)
  let C := (cutGraph (internalGraph G U) S).edgeSet
  let E := G.interedges Y (U \ S)
  let L := (B ∩ S) ×ˢ univ (α := Fin c)
  have hCG : cutGraph (internalGraph G U) S ≤ G :=
    SimpleGraph.between_le.trans (internalGraph_le G U)
  let ce : C → G.edgeSet := fun e => ⟨e.val, SimpleGraph.edgeSet_mono hCG e.property⟩
  let ae : E → G.edgeSet := fun e => ⟨s(e.val.1, e.val.2),
    (Rel.mem_interedges_iff.mp e.property).2.2⟩
  have hc_inj : Function.Injective ce := by
    intro p q h
    exact Subtype.ext (congrArg (fun e : G.edgeSet => e.val) h)
  have ha_inj : Function.Injective ae := by
    intro p q h
    have he := congrArg Subtype.val h
    change s(p.val.1, p.val.2) = s(q.val.1, q.val.2) at he
    have hp := Rel.mem_interedges_iff.mp p.property
    have hq := Rel.mem_interedges_iff.mp q.property
    rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Subtype.ext (Prod.ext h1 h2)
    · exact (Finset.disjoint_left.mp hAU (hYA hp.1)
        (h1 ▸ (mem_sdiff.mp hq.2.1).1)).elim
  have hca : ∀ p : C, ∀ q : E, ce p ≠ ae q := by
    intro p q he
    have he' := congrArg Subtype.val he
    have hm : q.val.1 ∈ p.val := by
      rw [he']
      exact Sym2.mem_mk_left _ _
    exact Finset.disjoint_left.mp hAU
      (hYA (Rel.mem_interedges_iff.mp q.property).1)
      (internal_cut_mem G U S p hm)
  let I := R ⊕ C ⊕ E ⊕ L
  let f : I → Vertex G A B c := fun z => match z with
    | .inl a => Sum.inl a.val
    | .inr (.inl e) => Sum.inr (Sum.inl (ce e))
    | .inr (.inr (.inl e)) => Sum.inr (Sum.inl (ae e))
    | .inr (.inr (.inr q)) => Sum.inr (Sum.inr
        (⟨q.val.1, (mem_inter.mp (mem_product.mp q.property).1).1⟩, q.val.2))
  have hf : ∀ z, f z ∈ X := by
    intro z
    rcases z with a | e | e | q
    · have h := (mem_sdiff.mp a.property).2
      simpa [Y₀, f] using h
    · rcases e with ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
        change (G.Adj x y ∧ x ∈ U ∧ y ∈ U) ∧ _ at he
        rcases he.2 with hxy | hyx
        · exact boundary_edge_in_separator hxy.1 he.1.2.2 hxy.2 he.1.1
        · have h := boundary_edge_in_separator hyx.2 he.1.2.1 hyx.1 he.1.1.symm
          simpa [f, ce, Sym2.eq_swap] using h
    · have he := Rel.mem_interedges_iff.mp e.property
      exact attachment_edge_in_separator ⟨e.val.1, hYA he.1⟩ (hsurv _ he.1)
        (mem_sdiff.mp he.2.1).1 (mem_sdiff.mp he.2.1).2 he.2.2
    · have hq := mem_inter.mp (mem_product.mp q.property).1
      exact branch_slot_in_separator hsep ⟨q.val.1, hq.1⟩ hq.2 q.val.2
  have hinj : Function.Injective f := by
    intro p q h
    rcases p with p | p | p | p <;> rcases q with q | q | q | q
    all_goals simp only [f, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact congrArg (fun e => Sum.inr (Sum.inl e)) (hc_inj h)
    · exact (hca p q h).elim
    · exact (hca q p h.symm).elim
    · exact congrArg (fun e => Sum.inr (Sum.inr (Sum.inl e))) (ha_inj h)
    · have hv := congrArg (fun z : B × Fin c => (z.1.val, z.2)) h
      exact congrArg (fun e => Sum.inr (Sum.inr (Sum.inr e))) (Subtype.ext hv)
  have hcard := Fintype.card_le_of_injective
    (fun z : I => (⟨f z, hf z⟩ : X))
    (fun p q h => hinj (congrArg Subtype.val h))
  have hcard' : R.card + cutSize (internalGraph G U) S + E.card +
      c * (B ∩ S).card ≤ X.card := by
    simpa only [I, C, L, Fintype.card_sum, Fintype.card_coe, Set.fintypeCard_eq_ncard,
      card_product, card_univ, Fintype.card_fin, cutSize, Nat.mul_comm,
      Nat.add_assoc] using hcard
  dsimp only [E] at hcard'
  omega

/-- The port graph contains one vertex-disjoint source-to-slot path per
source. The original directed-source cut condition is the only cut
hypothesis; it has not been replaced by a weaker undirected condition. -/
theorem port_paths_of_cuts (G : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (hAU : Disjoint A U) (hcut : CutCondition G A U B c) :
    Menger.Aux.Fam (graph G A U B c) (sources G A B c) (targets G A B c) A.card := by
  apply Menger.Aux.fam_of_le _ _ rfl
  intro X hX
  exact separator_card_bound G A U B c hAU hcut X hX

end
end Cycle13.ReservoirPorts
