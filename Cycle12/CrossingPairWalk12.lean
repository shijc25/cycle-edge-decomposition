import Cycle12.GroupedFamilyPacking12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I T : Type} [Fintype V] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq I] [DecidableEq T] {G : SimpleGraph V}

theorem walk_support_split {u v : V} (p : G.Walk u v) :
    p.support.toFinset={u,v}∪routeInterior p := by
  ext x
  simp only [List.mem_toFinset,mem_union,mem_insert,mem_singleton,mem_routeInterior_iff]
  constructor
  · intro hx
    by_cases hu : x=u
    · exact Or.inl (Or.inl hu)
    by_cases hv : x=v
    · exact Or.inl (Or.inr hv)
    exact Or.inr ⟨hx,hu,hv⟩
  · rintro ((rfl|rfl)|h)
    · exact p.start_mem_support
    · exact p.end_mem_support
    · exact h.1

theorem grouped_route_supports_disjoint (group : I → T) (a b : I → V)
    (p : ∀ i,G.Walk (a i) (b i))
    (hports : Pairwise (fun i j => Disjoint ({a i,b i}:Finset V) {a j,b j}))
    (hhard : ∀ i,Disjoint (routeInterior (p i)) (groupPorts group a b (group i)))
    (hi : ∀ i j,i ≠ j → group i=group j → Disjoint (routeInterior (p i)) (routeInterior (p j)))
    {i j : I} (hij : i ≠ j) (hg : group i=group j) :
    Disjoint (p i).support.toFinset (p j).support.toFinset := by
  rw [walk_support_split,walk_support_split]
  have hp (k l : I) (hkl : group k=group l) :
      Disjoint (routeInterior (p k)) ({a l,b l}:Finset V) := by
    apply (hhard k).mono_right
    intro v hv
    apply (mem_groupPorts group a b (group k) v).mpr
    refine ⟨l,hkl.symm,?_⟩
    simpa only [mem_insert,mem_singleton,eq_comm] using hv
  apply Finset.disjoint_left.mpr
  rintro v hv hw
  rcases mem_union.mp hv with hv|hv <;> rcases mem_union.mp hw with hw|hw
  · exact Finset.disjoint_left.mp (hports hij) hv hw
  · exact Finset.disjoint_left.mp (hp j i hg.symm) hw hv
  · exact Finset.disjoint_left.mp (hp i j hg) hv hw
  · exact Finset.disjoint_left.mp (hi i j hij hg) hv hw

def crossingPairWalk {a₀ a₁ b₀ b₁ : V} (h₀ : G.Adj a₀ b₀) (h₁ : G.Adj a₁ b₁)
    (p : G.Walk b₀ b₁) : G.Walk a₀ a₁ :=
  Walk.cons h₀ (p.append (Walk.cons h₁.symm Walk.nil))

theorem crossingPairWalk_support {a₀ a₁ b₀ b₁ : V} (h₀ : G.Adj a₀ b₀) (h₁ : G.Adj a₁ b₁)
    (p : G.Walk b₀ b₁) :
    (crossingPairWalk h₀ h₁ p).support.toFinset={a₀,a₁}∪p.support.toFinset := by
  ext v
  simp only [crossingPairWalk,List.mem_toFinset,Walk.support_cons,List.mem_cons,
    Walk.mem_support_append_iff,Walk.support_nil,List.mem_nil_iff,or_false,
    mem_union,mem_insert,mem_singleton]
  constructor
  · rintro (h|h|h|h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inr (h.symm ▸ p.end_mem_support)
    · exact Or.inl (Or.inr h)
  · rintro ((h|h)|h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)

theorem crossingPairWalk_edges {a₀ a₁ b₀ b₁ : V} (h₀ : G.Adj a₀ b₀) (h₁ : G.Adj a₁ b₁)
    (p : G.Walk b₀ b₁) :
    (crossingPairWalk h₀ h₁ p).edgeSet={s(a₀,b₀),s(a₁,b₁)}∪p.edgeSet := by
  simp only [crossingPairWalk,Walk.edgeSet_cons,Walk.edgeSet_append,Walk.edgeSet_nil,
    Sym2.eq_swap]
  ext e
  simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false]
  tauto

theorem crossingPairWalk_isPath {a₀ a₁ b₀ b₁ : V} (h₀ : G.Adj a₀ b₀) (h₁ : G.Adj a₁ b₁)
    (p : G.Walk b₀ b₁) (hp : p.IsPath) (hne : a₀ ≠ a₁)
    (ha₀ : a₀∉p.support) (ha₁ : a₁∉p.support) :
    (crossingPairWalk h₀ h₁ p).IsPath := by
  apply Walk.IsPath.mk'
  simp only [crossingPairWalk,Walk.support_cons,Walk.support_append,Walk.support_nil,
    List.tail_cons]
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_append,List.mem_singleton,not_or]
    exact ⟨ha₀,hne⟩
  · apply List.nodup_append'.mpr
    refine ⟨hp.support_nodup,List.nodup_singleton _,?_⟩
    rw [List.disjoint_left]
    intro v hv hw
    exact ha₁ ((List.mem_singleton.mp hw) ▸ hv)

end
end Cycle12
