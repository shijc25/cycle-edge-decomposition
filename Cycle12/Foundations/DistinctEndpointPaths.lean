import Cycle12.Foundations.ParityForest
import Cycle12.Foundations.UpstreamBridge

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

structure DistinctEndpointPaths (G : SimpleGraph V) where
  count : ℕ
  paths : Fin count → OAI.ErdosGallai.PositiveSimplePath G
  disjoint : Pairwise (fun i j => Disjoint (paths i).walk.edgeSet (paths j).walk.edgeSet)
  cover : (⋃ i, (paths i).walk.edgeSet) = G.edgeSet
  endpoint_injective : Function.Injective (fun z : Fin count × Bool =>
    if z.2 then (paths z.1).start else (paths z.1).finish)

theorem DistinctEndpointPaths.count_bound {G : SimpleGraph V} (P : DistinctEndpointPaths G) :
    2 * P.count ≤ Fintype.card V := by
  have h := Fintype.card_le_of_injective _ P.endpoint_injective
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm] using h

/-- Lovász's actual path/cycle decomposition becomes a path decomposition
with no repeated endpoint when all but at most one vertex have odd degree. -/
theorem distinct_endpoint_paths_of_almost_all_odd (G : SimpleGraph V) (root : V)
    (hodd : ∀ v : V, v ≠ root → Odd (G.degree v)) : Nonempty (DistinctEndpointPaths G) := by
  classical
  obtain ⟨k, P, hd, hc, hk⟩ := OAI.ErdosGallai.Lovasz.path_cycle_partition G
  let S : Finset V := univ.filter (fun v => Odd (G.degree v))
  have hnear : Fintype.card V ≤ S.card + 1 := by
    have hsub : (univ : Finset V) ⊆ insert root S := by
      intro v _
      by_cases hv : v = root
      · simp [hv]
      · exact mem_insert_of_mem (by simp [S, hodd v hv])
    have hcard := card_le_card hsub
    have hi := card_insert_le root S
    simpa only [card_univ] using hcard.trans hi
  have hS : Even S.card := G.even_card_odd_degree_vertices
  have hkn : 2 * k ≤ Fintype.card V :=
    hk.trans (Finset.card_le_univ _)
  have hks : 2 * k ≤ S.card := by
    obtain ⟨n, hn⟩ := hS
    omega
  have hopen := OAI.ErdosGallai.Lovasz.tight_partition_endpoints G P S hd hc
    (fun v hv => (mem_filter.mp hv).2) (by simpa using hks)
  let endpoint : Fin k × Bool → V := fun z => if z.2 then (P z.1).start else (P z.1).finish
  have he : ∀ v : S, ∃ z : Fin k × Bool, endpoint z = v := by
    intro v
    obtain ⟨i, _, h | h⟩ := OAI.ErdosGallai.Lovasz.endpoint_of_odd G P hd hc v
      ((mem_filter.mp v.property).2)
    · exact ⟨(i, true), h⟩
    · exact ⟨(i, false), h⟩
  choose pick hpick using he
  have hpi : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    exact (hpick v).symm.trans ((congrArg endpoint hvw).trans (hpick w))
  have hps : Function.Surjective pick := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective pick hpi hn
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hlt
    omega
  have hei : Function.Injective endpoint := by
    intro z t heq
    obtain ⟨v, rfl⟩ := hps z
    obtain ⟨w, rfl⟩ := hps t
    have hvw : v = w := Subtype.ext (by simpa only [hpick] using heq)
    exact congrArg pick hvw
  have hpaths : ∀ i, (P i).walk.IsPath ∧ 0 < (P i).walk.length := by
    intro i
    rcases (P i).simple with hp | ⟨h, _⟩
    · exact hp
    · exact ((hopen i).1 h.symm).elim
  exact ⟨⟨k, fun i => ⟨(P i).start, (P i).finish, (P i).walk,
    (hpaths i).1, (hpaths i).2⟩, hd, hc, hei⟩⟩

theorem connected_forest_path_partition (G : SimpleGraph V) (hG : G.Connected) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      F.edgeSet.ncard ≤ Fintype.card V - componentCount G ∧
      Nonempty (DistinctEndpointPaths (G \ F)) := by
  obtain ⟨root⟩ := hG.nonempty
  obtain ⟨F, hF, hacyc, hsize, hodd⟩ := exists_odd_remainder_forest G hG root
  refine ⟨F, hF, hacyc, hsize, distinct_endpoint_paths_of_almost_all_odd (G \ F) root ?_⟩
  intro v hv
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using hodd v hv

end
end Cycle13
