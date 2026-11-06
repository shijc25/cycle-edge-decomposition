import Cycle12.PreparedClassData12
import Cycle12.MatchingDemandIncidence12
import Cycle12.JointEndpointCertificate12
import Cycle12.GroupedDemandData12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The even groups contain precisely the paired original edges. -/
theorem matchingOriginalGroups_union (H : SimpleGraph V)
    (M : (⊤ : SimpleGraph H.edgeSet).Subgraph) (hM : M.IsMatching) (Q : ℕ) :
    (⋃ t,matchingOriginalGroup H M Q t)=originalEdgeSet H M.verts := by
  ext e
  constructor
  · intro he
    obtain ⟨t,k,hk,rfl⟩ := Set.mem_iUnion.mp he
    refine ⟨k,?_,rfl⟩
    apply Set.mem_toFinset.mp
    rw [←matchingEvenGroup_union M hM Q]
    exact mem_biUnion.mpr ⟨t,mem_univ _,hk⟩
  · rintro ⟨k,hk,rfl⟩
    have hu : k∈univ.biUnion (matchingEvenGroup M Q) := by
      rw [matchingEvenGroup_union M hM Q]
      exact Set.mem_toFinset.mpr hk
    obtain ⟨t,_,ht⟩ := mem_biUnion.mp hu
    exact Set.mem_iUnion.mpr ⟨t,⟨k,ht,rfl⟩⟩

theorem matchingOriginalGroups_card (H : SimpleGraph V)
    (M : (⊤ : SimpleGraph H.edgeSet).Subgraph) (hM : M.IsMatching) (Q : ℕ) :
    (⋃ t,matchingOriginalGroup H M Q t).ncard=2*Fintype.card M.edgeSet := by
  rw [matchingOriginalGroups_union H M hM Q,originalEdgeSet_card]
  have hc : M.verts.toFinset.card=2*Fintype.card M.edgeSet := by
    rw [←matchingPairVertices_union M hM,
      card_biUnion (fun e _ f _ hef => matchingPairVertices_disjoint M hM hef)]
    simp only [matchingPairVertices_card,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_comm]
  simpa only [←Set.ncard_eq_toFinset_card'] using hc

/-- Count matching groups using only the edges actually assigned to
those groups; the retained singleton is never charged a second time. -/
theorem matchingOriginalGroups_count (H : SimpleGraph V)
    (M : (⊤ : SimpleGraph H.edgeSet).Subgraph) (hM : M.IsMatching) {Q : ℕ} (hQ : 0<Q) :
    (Fintype.card (Fin (Fintype.card M.edgeSet/Q+1)):ℝ) ≤
      ((⋃ t,matchingOriginalGroup H M Q t).ncard:ℝ)/(2*Q)+1 := by
  have hh := demandGroup_count_bound (I:=M.edgeSet) hQ
  rw [matchingOriginalGroups_card H M hM Q,Nat.cast_mul,Nat.cast_ofNat]
  convert hh using 1 <;> ring

/-- Actual oriented matching edges, with injective endpoint maps on both
sides. The pairing remains the exact one from the preparation ledger. -/
structure MatchingRequestData12 (H : SimpleGraph V) (U T : Finset V)
    (M : (⊤ : SimpleGraph H.edgeSet).Subgraph) (Q : ℕ) where
  a : H.edgeSet → V
  b : H.edgeSet → V
  ports : ∀ e,a e∈U ∧ b e∈T ∧ H.Adj (a e) (b e) ∧ s(a e,b e)=e.val
  a_injective : Function.Injective a
  b_injective : Function.Injective b

namespace MatchingRequestData12
variable {H : SimpleGraph V} {U T : Finset V} {M : (⊤ : SimpleGraph H.edgeSet).Subgraph} {Q : ℕ}

abbrev Index (_D : MatchingRequestData12 H U T M Q) := M.edgeSet ⊕ M.edgeSet

def next (_D : MatchingRequestData12 H U T M Q) : Equiv.Perm M.edgeSet :=
  groupedCycleNext (demandGroup Q)

def left (D : MatchingRequestData12 H U T M Q) : D.Index → V :=
  Sum.elim (fun e => D.a e.val.out.2) (fun e => D.b e.val.out.1)

def right (D : MatchingRequestData12 H U T M Q) : D.Index → V :=
  Sum.elim (fun e => D.a (D.next e).val.out.1) (fun e => D.b e.val.out.2)

theorem endpoints (D : MatchingRequestData12 H U T M Q) (j : D.Index) :
    match j with
    | .inl _ => D.left j∈U ∧ D.right j∈U
    | .inr _ => D.left j∈T ∧ D.right j∈T := by
  cases j with
  | inl e => exact ⟨(D.ports _).1,(D.ports _).1⟩
  | inr e => exact ⟨(D.ports _).2.1,(D.ports _).2.1⟩

/-- These are the actual two-sided alternating requests, with one joint
certificate into the original paired edge class. -/
theorem certificate_exists (D : MatchingRequestData12 H U T M Q) (hM : M.IsMatching) :
    Nonempty (OriginalEndpointCertificate H D.left D.right
      (⋃ t,matchingOriginalGroup H M Q t)) := by
  have he : Function.Injective (fun e => s(D.a e,D.b e)) := by
    intro e f hef
    apply Subtype.ext
    simpa only [(D.ports e).2.2.2,(D.ports f).2.2.2] using hef
  obtain ⟨neighbor,hn,hinj⟩ := matching_demands_class_incidences H D.a D.b (fun e => (D.ports e).2.2.1)
    he M hM D.next (⋃ t,matchingOriginalGroup H M Q t) (by
      intro e he
      rw [matchingOriginalGroups_union H M hM Q]
      exact ⟨e,he,(D.ports e).2.2.2.symm⟩)
  have hp (k : D.Index × Bool) :
      (if (matchingDemandPick M D.next k).2 then D.b (matchingDemandPick M D.next k).1
        else D.a (matchingDemandPick M D.next k).1)=(if k.2 then D.right k.1 else D.left k.1) := by
    rcases k with ⟨e,t⟩
    cases e <;> cases t <;> rfl
  refine ⟨⟨neighbor,?_,?_,?_⟩⟩
  · intro k
    simpa only [hp] using (hn k).1
  · intro k
    simpa only [hp] using (hn k).2
  · simpa only [hp] using hinj

theorem distinct (D : MatchingRequestData12 H U T M Q) (hM : M.IsMatching) (j : D.Index) :
    D.left j ≠ D.right j := by
  cases j with
  | inl e =>
    intro he
    have hh : pairedOriginalItem M (e,true)=pairedOriginalItem M (D.next e,false) := D.a_injective he
    have h := pairedOriginalItem_injective M hM hh
    have htf : (true:Bool)=false := congrArg Prod.snd h
    cases htf
  | inr e =>
    intro he
    have hh : e.val.out.1=e.val.out.2 := D.b_injective he
    exact (edge_out_adj M.spanningCoe e).ne hh

theorem team_capacity (D : MatchingRequestData12 H U T M Q) (hQ : 0<Q)
    (t : Fin (Fintype.card M.edgeSet/Q+1)) : teamLoad (demandGroup Q (I:=M.edgeSet)) t ≤ Q := by
  simpa only [teamLoad,Fintype.card_subtype] using demandGroup_fiber_card (I:=M.edgeSet) hQ t

theorem hard_capacity (D : MatchingRequestData12 H U T M Q) (hQ : 0<Q)
    (t : Fin (Fintype.card M.edgeSet/Q+1)) :
    (groupPorts (demandGroup Q) (fun e : M.edgeSet => D.a e.val.out.1)
      (fun e => D.a e.val.out.2) t).card ≤ 2*Q ∧
    (groupPorts (demandGroup Q) (fun e : M.edgeSet => D.b e.val.out.1)
      (fun e => D.b e.val.out.2) t).card ≤ 2*Q := by
  exact ⟨(groupPorts_card _ _ _ _).trans (Nat.mul_le_mul_left 2 (D.team_capacity hQ t)),
    (groupPorts_card _ _ _ _).trans (Nat.mul_le_mul_left 2 (D.team_capacity hQ t))⟩

end MatchingRequestData12

/-- Instantiate alternating requests from the actual residual matching
kept in the two-pass crossing ledger. -/
theorem CrossingLedger12.request_data {G : SimpleGraph V} {U T : Finset V} {Q : ℕ}
    (D : CrossingLedger12 G U T Q)
    (hcross : ∀ {x y},G.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U)) :
    Nonempty (MatchingRequestData12 D.second.residue U T D.matching Q) := by
  obtain ⟨a,b,hp,ha,hb⟩ := orient_matching_original_edges D.second.residue U T
    (fun {_ _} h => hcross h.1.1) D.residue_degree
  exact ⟨⟨a,b,hp,ha,hb⟩⟩

end
end Cycle12
