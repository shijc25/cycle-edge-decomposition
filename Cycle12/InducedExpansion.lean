import Cycle12.ShortPaths

/-! Transfer the core cut property to an induced graph and lift its actual simple paths. -/
namespace Cycle12

universe u
variable {V : Type u} [Fintype V]
open scoped Classical
open Finset

theorem cutCount_induce_map (G : SimpleGraph V) (U : Finset V)
    (S T : Finset {v // v ∈ U}) :
    cutCount (G.induce (U : Set V)) S T =
      cutCount G (S.map (.subtype (· ∈ U))) (T.map (.subtype (· ∈ U))) := by
  let f : {v // v ∈ U} ↪ V := .subtype (· ∈ U)
  simp only [cutCount_eq_filter_card]
  apply Finset.card_bij (fun e _ => f.sym2Map e)
  · intro e he
    obtain ⟨heG, x, hx, y, hy, rfl⟩ := mem_filter.mp he
    have hxy : G.Adj x.val y.val := SimpleGraph.mem_edgeFinset.mp heG
    refine mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hxy, f x, ?_, f y, ?_, rfl⟩
    · exact mem_map.mpr ⟨x, hx, rfl⟩
    · exact mem_map.mpr ⟨y, hy, rfl⟩
  · intro e he e' he' heq
    exact f.sym2Map.injective heq
  · intro e he
    obtain ⟨heG, x, hx, y, hy, rfl⟩ := mem_filter.mp he
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    have hxy : (G.induce (U : Set V)).Adj x' y' := SimpleGraph.mem_edgeFinset.mp heG
    refine ⟨s(x',y'), mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hxy,
      x', hx', y', hy', rfl⟩, rfl⟩

theorem subtype_map_compl (U : Finset V) [Fintype {v // v ∈ U}]
    (T : Finset {v // v ∈ U}) :
    Tᶜ.map (.subtype (· ∈ U)) = U \ T.map (.subtype (· ∈ U)) := by
  ext v
  simp only [mem_map, mem_compl, mem_sdiff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.property, ?_⟩
    rintro ⟨w', hw', heq⟩
    have he : w' = w := Subtype.ext heq
    exact hw (he ▸ hw')
  · rintro ⟨hv, hn⟩
    refine ⟨⟨v,hv⟩, ?_, rfl⟩
    intro ht
    exact hn ⟨⟨v,hv⟩, ht, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem cutExpandsOn_induce {G : SimpleGraph V} {U : Finset V} {h : ℝ}
    (hG : CutExpandsOn G U h) : CutExpands (G.induce (U : Set V)) h := by
  intro T hT
  let f : {v // v ∈ U} ↪ V := .subtype (· ∈ U)
  have hsub : T.map f ⊆ U := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
    exact w.property
  have hsmall : 2*(T.map f).card ≤ U.card := by simpa using hT
  have hb := hG (T.map f) hsub hsmall
  unfold boundaryCount
  rw [cutCount_induce_map]
  have htmap := subtype_map_compl U T
  convert hb using 1
  · simp
  · congr 2
    convert htmap using 1
    ext x
    simp

theorem expanding_induced_short_path {G : SimpleGraph V} {U : Finset V} {h : ℝ}
    (hh : 0 < h) (hG : CutExpandsOn G U h) (u v : V) (hu : u ∈ U) (hv : v ∈ U) :
    ∃ p : G.Walk u v, p.IsPath ∧ (∀ w ∈ p.support, w ∈ U) ∧
      (p.length : ℝ) ≤ 2*Real.sqrt (2*(U.card : ℝ)/h)+2 := by
  let f : (G.induce (U : Set V)) →g G :=
    ⟨Subtype.val, fun h => h⟩
  obtain ⟨p, hp, hlen⟩ := expanding_graph_short_path hh (cutExpandsOn_induce hG) ⟨u,hu⟩ ⟨v,hv⟩
  refine ⟨p.map f, hp.map Subtype.val_injective, ?_, ?_⟩
  · intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact w'.property
  · simpa using hlen

end Cycle12
