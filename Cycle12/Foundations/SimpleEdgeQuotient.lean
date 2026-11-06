import Cycle12.Foundations.DisjointBlockContraction

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W]

/-- Pushing forward a graph loses exactly the edges inside fibers. Once
these have been assigned elsewhere, every quotient edge has an original
representative. This statement does not require injectivity on vertices. -/
theorem edgeSet_map_of_no_internal (G : SimpleGraph V) (π : V → W)
    (hproper : ∀ {u v},G.Adj u v → π u ≠ π v) :
    (G.map π).edgeSet=Sym2.map π '' G.edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hne,a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj' π G x y).mp he
      refine ⟨s(a,b),hab,?_⟩
      simp only [Sym2.map_mk,ha,hb]
  · exact (SimpleGraph.Hom.map π G hproper).image_edgeSet_subset

/-- The original-edge uniqueness condition makes quotient edges and
retained original edges genuinely bijective, even though entire vertex
blocks have been collapsed. -/
def simpleEdgeQuotientEquiv (G : SimpleGraph V) (π : V → W)
    (hproper : ∀ {u v},G.Adj u v → π u ≠ π v)
    (hunique : Set.InjOn (Sym2.map π) G.edgeSet) : G.edgeSet ≃ (G.map π).edgeSet :=
  Equiv.ofBijective (SimpleGraph.Hom.map π G hproper).mapEdgeSet (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hunique a.property b.property (congrArg Subtype.val hab)
    · intro e
      have he : e.val ∈ Sym2.map π '' G.edgeSet := by
        simpa only [edgeSet_map_of_no_internal G π hproper] using e.property
      obtain ⟨d,hd,hde⟩ := he
      exact ⟨⟨d,hd⟩,Subtype.ext hde⟩)

theorem simpleEdgeQuotientEquiv_apply (G : SimpleGraph V) (π : V → W)
    (hproper : ∀ {u v},G.Adj u v → π u ≠ π v)
    (hunique : Set.InjOn (Sym2.map π) G.edgeSet) (e : G.edgeSet) :
    (simpleEdgeQuotientEquiv G π hproper hunique e).val=Sym2.map π e.val := rfl

theorem simple_quotient_edge_count (G : SimpleGraph V) (π : V → W)
    (hproper : ∀ {u v},G.Adj u v → π u ≠ π v)
    (hunique : Set.InjOn (Sym2.map π) G.edgeSet) :
    (G.map π).edgeSet.ncard=G.edgeSet.ncard := by
  exact (Nat.card_congr (simpleEdgeQuotientEquiv G π hproper hunique)).symm

/-- Pull back any partition of quotient edges. Disjointness and the exact
union are preserved, so edges assigned to different quotient cycles cannot
be reused during lifting. No cycle-lifting theorem is assumed here. -/
theorem quotient_partition_pullback (G : SimpleGraph V) (π : V → W)
    (hproper : ∀ {u v},G.Adj u v → π u ≠ π v)
    {J : Type} (parts : J → Set (Sym2 W))
    (hdis : Pairwise (fun i j => Disjoint (parts i) (parts j)))
    (hcover : (⋃ i,parts i)=(G.map π).edgeSet) :
    Pairwise (fun i j => Disjoint (G.edgeSet∩Sym2.map π ⁻¹' parts i)
      (G.edgeSet∩Sym2.map π ⁻¹' parts j)) ∧
    (⋃ i,G.edgeSet∩Sym2.map π ⁻¹' parts i)=G.edgeSet := by
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    exact Set.disjoint_left.mp (hdis hij) he.2 hf.2
  · ext e
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_preimage]
    constructor
    · rintro ⟨i,he,hi⟩
      exact he
    · intro he
      have hm := (SimpleGraph.Hom.map π G hproper).map_mem_edgeSet he
      rw [← hcover] at hm
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hm
      exact ⟨i,he,hi⟩

end
end Cycle13
