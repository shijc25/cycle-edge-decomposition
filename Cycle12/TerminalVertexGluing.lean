import Cycle12.TerminalReduction

/-! Exact gluing over one shared vertex. The affine vertex term is charged
with n-1, and every original edge belongs to exactly one side. -/
namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem one_vertex_lifts_disjoint (G : SimpleGraph V) (S T : Finset V) (a : V)
    (hinter : S∩T={a}) :
    Disjoint (reservoirLift S (G.induce (S:Set V))).edgeSet
      (reservoirLift T (G.induce (T:Set V))).edgeSet := by
  rw [reservoirLift_induce,reservoirLift_induce]
  apply Set.disjoint_left.mpr
  intro e heS heT
  induction e using Sym2.ind with
  | _ u v =>
    change G.Adj u v ∧ u∈S ∧ v∈S at heS
    change G.Adj u v ∧ u∈T ∧ v∈T at heT
    have hu : u=a := by
      have hh := Finset.mem_inter.mpr ⟨heS.2.1,heT.2.1⟩
      simpa only [hinter,Finset.mem_singleton] using hh
    have hv : v=a := by
      have hh := Finset.mem_inter.mpr ⟨heS.2.2,heT.2.2⟩
      simpa only [hinter,Finset.mem_singleton] using hh
    exact heS.1.ne (hu.trans hv.symm)

theorem separated_lifts_cover (G : SimpleGraph V) (S T : Finset V)
    (hcover : S∪T=Finset.univ)
    (hcross : ∀ u∈S\T, ∀ v∈T\S, ¬G.Adj u v) :
    (reservoirLift S (G.induce (S:Set V))).edgeSet ∪
      (reservoirLift T (G.induce (T:Set V))).edgeSet=G.edgeSet := by
  rw [reservoirLift_induce,reservoirLift_induce]
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    change ((G.Adj u v ∧ u∈S ∧ v∈S) ∨ (G.Adj u v ∧ u∈T ∧ v∈T)) ↔ G.Adj u v
    constructor
    · rintro (h | h) <;> exact h.1
    · intro huv
      have hu : u∈S ∨ u∈T := by rw [← Finset.mem_union,hcover]; exact Finset.mem_univ _
      have hv : v∈S ∨ v∈T := by rw [← Finset.mem_union,hcover]; exact Finset.mem_univ _
      by_cases huS : u∈S <;> by_cases hvS : v∈S
      · exact Or.inl ⟨huv,huS,hvS⟩
      · have hvT := hv.resolve_left hvS
        by_cases huT : u∈T
        · exact Or.inr ⟨huv,huT,hvT⟩
        · exact (hcross u (Finset.mem_sdiff.mpr ⟨huS,huT⟩) v
            (Finset.mem_sdiff.mpr ⟨hvT,hvS⟩) huv).elim
      · have huT := hu.resolve_left huS
        by_cases hvT : v∈T
        · exact Or.inr ⟨huv,huT,hvT⟩
        · exact (hcross v (Finset.mem_sdiff.mpr ⟨hvS,hvT⟩) u
            (Finset.mem_sdiff.mpr ⟨huT,huS⟩) huv.symm).elim
      · exact Or.inr ⟨huv,hu.resolve_left huS,hv.resolve_left hvS⟩

theorem terminal_affine_one_vertex_gluing (G : SimpleGraph V) (S T : Finset V) (a : V)
    (hcover : S∪T=Finset.univ) (hinter : S∩T={a})
    (hcross : ∀ u∈S\T, ∀ v∈T\S, ¬G.Adj u v)
    (P : Cycle13.CyclePacking (G.induce (S:Set V)))
    (hP : P.cost ≤ 19*(S.card-1)+6*(G.induce (S:Set V)).edgeSet.ncard)
    (Q : Cycle13.CyclePacking (G.induce (T:Set V)))
    (hQ : Q.cost ≤ 19*(T.card-1)+6*(G.induce (T:Set V)).edgeSet.ncard) :
    ∃ C : Cycle13.CyclePacking G,
      C.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let H := reservoirLift S (G.induce (S:Set V))
  let K := reservoirLift T (G.induce (T:Set V))
  let P' := P.mapEmbedding (reservoirEmbedding S)
  let Q' := Q.mapEmbedding (reservoirEmbedding T)
  have hd := one_vertex_lifts_disjoint G S T a hinter
  have hu := separated_lifts_cover G S T hcover hcross
  have hH : H ≤ G := reservoirLift_le G S _ le_rfl
  have hK : K ≤ G := reservoirLift_le G T _ le_rfl
  have hrest : G.edgeSet\(H.edgeSet∪K.edgeSet)=∅ := by rw [hu]; exact Set.sdiff_self
  let C := P'.combine Q' hH hK hd
  have hcost : C.cost=P.cost+Q.cost := by
    have hPcost : P'.cost=P.cost := indexed_packing_cost_mapEmbedding P _
    have hQcost : Q'.cost=Q.cost := indexed_packing_cost_mapEmbedding Q _
    dsimp only [C]
    unfold Cycle13.CyclePacking.cost
    erw [Cycle13.CyclePacking.combine_count,Cycle13.CyclePacking.combine_singles,
      hrest,Set.ncard_empty]
    change 42*(P'.count+Q'.count)+23*(P'.singles+Q'.singles+0)=_
    calc
      _=P'.cost+Q'.cost := by unfold Cycle13.CyclePacking.cost; ring
      _=P.cost+Q.cost := by rw [hPcost,hQcost]
  have hHi : H.edgeSet.ncard=(G.induce (S:Set V)).edgeSet.ncard := by
    dsimp [H,reservoirLift]
    rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ (reservoirEmbedding S).sym2Map.injective]
  have hKi : K.edgeSet.ncard=(G.induce (T:Set V)).edgeSet.ncard := by
    dsimp [K,reservoirLift]
    rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ (reservoirEmbedding T).sym2Map.injective]
  have he : (G.induce (S:Set V)).edgeSet.ncard+(G.induce (T:Set V)).edgeSet.ncard=G.edgeSet.ncard := by
    rw [← hHi,← hKi,← Set.ncard_union_eq hd]
    exact congrArg Set.ncard hu
  have hsizes := Finset.card_union_add_card_inter S T
  rw [hcover,hinter,Finset.card_univ,Finset.card_singleton] at hsizes
  have ha : a∈S∩T := by rw [hinter]; exact Finset.mem_singleton_self _
  have hS := Finset.card_pos.mpr (show S.Nonempty from ⟨a,(Finset.mem_inter.mp ha).1⟩)
  have hT := Finset.card_pos.mpr (show T.Nonempty from ⟨a,(Finset.mem_inter.mp ha).2⟩)
  refine ⟨C,?_⟩
  calc
    C.cost=P.cost+Q.cost := hcost
    _ ≤ (19*(S.card-1)+6*(G.induce (S:Set V)).edgeSet.ncard)+
        (19*(T.card-1)+6*(G.induce (T:Set V)).edgeSet.ncard) := Nat.add_le_add hP hQ
    _ = _ := by omega

end
end Cycle12
