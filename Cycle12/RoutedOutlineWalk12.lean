import Cycle12.CycleOutlinePortLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def outlineVisits (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (z : c.W) : G.Walk (c.start z) (c.finish z) :=
  if h : z∈c.cycle.dropLast.support ∧ c.start z≠c.finish z then route ⟨z,h⟩
  else Walk.nil.copy rfl (by
    by_cases hz : z∈c.cycle.dropLast.support
    · exact not_not.mp (fun hn => h ⟨hz,hn⟩)
    · exact c.outside z hz)

theorem outlineVisits_switch (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) (z : c.Switch) :
    outlineVisits c route z=route z := by
  simp only [outlineVisits,dite_eq_left z.property]

theorem outlineVisits_nil (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) (z : c.W)
    (hz : ¬(z∈c.cycle.dropLast.support ∧ c.start z≠c.finish z)) :
    (outlineVisits c route z).Nil := by
  simp only [outlineVisits,dite_eq_right hz,Walk.nil_copy,Walk.nil_nil]

theorem outline_adj (c : CycleOutline G) (d : c.Q.Dart) (hd : d∈c.cycle.darts) :
    G.Adj (c.finish d.fst) (c.start d.snd) := by
  rw [(c.ports d hd).1,(c.ports d hd).2]
  exact (c.rep d).adj

def outlineLastDart (c : CycleOutline G) : c.Q.Dart :=
  ⟨(c.cycle.penultimate,c.base),c.cycle.adj_penultimate c.isCycle.not_nil⟩

theorem outlineLastDart_mem (c : CycleOutline G) : outlineLastDart c∈c.cycle.darts :=
  last_dart_mem c.cycle c.isCycle.not_nil

theorem outline_dropLast_darts (c : CycleOutline G) : c.cycle.dropLast.darts⊆c.cycle.darts := by
  rw [Walk.darts_dropLast]
  exact List.dropLast_subset _

theorem outline_last_adj (c : CycleOutline G) :
    G.Adj (c.finish c.cycle.penultimate) (c.start c.base) :=
  outline_adj c (outlineLastDart c) (outlineLastDart_mem c)

def outlineChain (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    VisitChain G (c.start c.base) (c.finish c.cycle.penultimate) :=
  VisitChain.of_walk c.start c.finish (outlineVisits c route) c.cycle.dropLast
    (fun d hd => outline_adj c d (outline_dropLast_darts c hd))

/-- The actual lifted closed walk. No vertex-disjointness assumption is
used here; its simplicity is replaced later by a soft collision budget. -/
def outlineClosedWalk (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    G.Walk (c.finish c.cycle.penultimate) (c.finish c.cycle.penultimate) :=
  Walk.cons (outline_last_adj c)
    (outlineChain c route).walk

theorem outline_route_union (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    (⋃ z∈c.cycle.dropLast.support, (outlineVisits c route z).edgeSet)=⋃ z,(route z).edgeSet := by
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z,hz,he⟩
    by_cases hne : c.start z≠c.finish z
    · exact ⟨⟨z,hz,hne⟩,by rwa [outlineVisits_switch c route ⟨z,hz,hne⟩] at he⟩
    · have hn := outlineVisits_nil c route z (by tauto)
      have hh := he
      simp only [Walk.edgeSet,Walk.edges_eq_nil.mpr hn,List.mem_nil_iff] at hh
      exact False.elim hh
  · rintro ⟨z,he⟩
    exact ⟨z,z.property.1,by rwa [outlineVisits_switch]⟩

theorem outlineClosedWalk_edges (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    (outlineClosedWalk c route).edgeSet=c.edges∪⋃ z,(route z).edgeSet := by
  have he (d : c.Q.Dart) (hd : d∈c.cycle.darts) :
      s(c.finish d.fst,c.start d.snd)=(c.rep d).edge := by
    rw [(c.ports d hd).1,(c.ports d hd).2]
    rfl
  have hlinks : {s(c.finish c.cycle.penultimate,c.start c.base)}∪
      {e | ∃ d∈c.cycle.dropLast.darts, e=s(c.finish d.fst,c.start d.snd)}=c.edges := by
    ext e
    constructor
    · rintro (h | ⟨d,hd,rfl⟩)
      · exact ⟨outlineLastDart c,outlineLastDart_mem c,
          h.trans (he (outlineLastDart c) (outlineLastDart_mem c))⟩
      · exact ⟨d,outline_dropLast_darts c hd,he d (outline_dropLast_darts c hd)⟩
    · rintro ⟨d,hd,rfl⟩
      rw [cycle_darts_split c.cycle c.isCycle.not_nil] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact Or.inr ⟨d,hd,(he d (outline_dropLast_darts c hd)).symm⟩
      · obtain rfl := List.mem_singleton.mp hd
        exact Or.inl (he (outlineLastDart c) (outlineLastDart_mem c)).symm
  rw [outlineClosedWalk,Walk.edgeSet_cons,VisitChain.edgeSet_eq]
  simp only [outlineChain,VisitChain.of_walk_links,VisitChain.of_walk_switchEdges]
  rw [Set.insert_eq,←Set.union_assoc,hlinks,outline_route_union]

theorem outlineClosedWalk_mem_support (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) (v : V) :
    v∈(outlineClosedWalk c route).support ↔
      ∃ z∈c.cycle.dropLast.support, v∈(outlineVisits c route z).support := by
  have hlast : c.cycle.penultimate∈c.cycle.dropLast.support := c.cycle.dropLast.end_mem_support
  simp only [outlineClosedWalk,Walk.support_cons,List.mem_cons,
    VisitChain.mem_support_iff,outlineChain,VisitChain.of_walk_visits,List.mem_map]
  constructor
  · rintro (rfl | ⟨p,⟨z,hz,rfl⟩,hp⟩)
    · exact ⟨c.cycle.penultimate,hlast,(outlineVisits c route _).end_mem_support⟩
    · exact ⟨z,hz,hp⟩
  · rintro ⟨z,hz,hv⟩
    exact Or.inr ⟨_,⟨z,hz,rfl⟩,hv⟩

theorem outlineClosedWalk_support (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    (outlineClosedWalk c route).support.toFinset=
      c.vertices∪univ.biUnion (fun z => routeInterior (route z)) := by
  ext v
  rw [List.mem_toFinset,outlineClosedWalk_mem_support,outline_ports_union]
  simp only [mem_union,mem_biUnion,List.mem_toFinset,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · rintro ⟨z,hz,hv⟩
    by_cases hs : v=c.start z
    · exact Or.inl ⟨z,hz,Or.inl hs⟩
    by_cases ht : v=c.finish z
    · exact Or.inl ⟨z,hz,Or.inr ht⟩
    by_cases hne : c.start z≠c.finish z
    · refine Or.inr ⟨⟨z,hz,hne⟩,?_⟩
      apply (mem_routeInterior_iff (route ⟨z,hz,hne⟩) v).mpr
      exact ⟨by rwa [←outlineVisits_switch c route ⟨z,hz,hne⟩],hs,ht⟩
    · have hn := outlineVisits_nil c route z (by tauto)
      rw [Walk.nil_iff_support_eq.mp hn] at hv
      exact False.elim (hs (List.mem_singleton.mp hv))
  · rintro (⟨z,hz,hv | hv⟩ | ⟨z,hz⟩)
    · exact ⟨z,hz,hv ▸ (outlineVisits c route z).start_mem_support⟩
    · exact ⟨z,hz,hv ▸ (outlineVisits c route z).end_mem_support⟩
    · exact ⟨z,z.property.1,by rw [outlineVisits_switch]; exact ((mem_routeInterior_iff (route z) v).mp hz).1⟩

end
end Cycle12
