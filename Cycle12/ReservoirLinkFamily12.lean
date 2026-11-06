import Cycle12.HubFragmentFill12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Construct actual reservoir links with distinct spokes, pairwise
disjoint edge sets, and an explicit bank-edge ledger. -/
theorem sampled_link_family [Nonempty V] (G H : SimpleGraph V) (hHG : H ≤ G)
    (U : Finset V) {z upper : ℝ} (hU : ReservoirSample H U z upper)
    (source : I × Bool → V) (hout : ∀ k, source k ∉ U)
    (hsource : ∀ v, (univ.filter (fun k => source k = v)).card ≤ 2)
    (hz : 8192 ≤ z) (hzr : z ≤ (Fintype.card V:ℝ))
    (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) (hcard : Fintype.card I ≤ Fintype.card V) :
    ∃ L : ∀ i, ReservoirLink G (source (i,false)) (source (i,true)),
      (∀ i, ∀ v ∈ (L i).route.support, v ∈ U) ∧
      Pairwise (fun i j => Disjoint (L i).edges (L j).edges) ∧
      (∀ i, (L i).edges ⊆ H.edgeSet) ∧
      (∀ i, ∀ e ∈ (L i).edges, ∃ v, v ∈ e ∧ v ∈ U) := by
  obtain ⟨f,hf,_,hinj,hcap,hstrict⟩ := choose_endpoint_connectors H U source
    hz hzr hsquare (by exact_mod_cast hcard) hsource hout (fun k => hU.neighbors (source k))
  have hI : 2112*(Fintype.card I:ℝ) ≤ z^2 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num : (0:ℝ) ≤ 2112)).trans hsquare
  obtain ⟨P,hP,hPU,hPP,hPH⟩ := sampled_routes_ambient G H hHG U hU f (fun k => (hf k).1)
    hz hlog hI (fun v => (show ((univ.filter (fun k => f k = v)).card:ℝ) ≤
      (⌈8*(Fintype.card V:ℝ)/z⌉₊:ℝ) by exact_mod_cast hcap v).trans hstrict.le)
  let L : ∀ i, ReservoirLink G (source (i,false)) (source (i,true)) := fun i =>
    ⟨f (i,false),f (i,true),P i,hHG (hf (i,false)).2,hHG (hf (i,true)).2,hP i⟩
  let S : I → Set (Sym2 V) := fun i => {s(source (i,false),f (i,false)),s(source (i,true),f (i,true))}
  have hS : ∀ i, S i ⊆ H.edgeSet := by
    intro i e he
    rcases he with he | he
    · exact he ▸ (hf (i,false)).2
    · exact he ▸ (hf (i,true)).2
  have hSS : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    have ho : ∀ k, e ∈ S k → ∃ b, e = s(source (k,b),f (k,b)) := by
      intro k hk
      rcases hk with hk | hk
      · exact ⟨false,hk⟩
      · exact ⟨true,hk⟩
    obtain ⟨b,hb⟩ := ho i hi
    obtain ⟨c,hc⟩ := ho j hj
    exact hij (congrArg Prod.fst (hinj (a₁ := (i,b)) (a₂ := (j,c)) (hb.symm.trans hc)))
  have hPS : ∀ i j, Disjoint (P i).edgeSet (S j) := by
    intro i j
    apply Set.disjoint_left.mpr
    intro e hp hs
    rcases hs with he | he
    · rw [he] at hp
      exact hout (j,false) (hPU i _ ((P i).fst_mem_support_of_mem_edges hp))
    · rw [he] at hp
      exact hout (j,true) (hPU i _ ((P i).fst_mem_support_of_mem_edges hp))
  refine ⟨L,hPU,?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    change e ∈ (P i).edgeSet ∪ S i at hi
    change e ∈ (P j).edgeSet ∪ S j at hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact Set.disjoint_left.mp (hPP hij) hi hj
    · exact Set.disjoint_left.mp (hPS i j) hi hj
    · exact Set.disjoint_left.mp (hPS j i) hj hi
    · exact Set.disjoint_left.mp (hSS hij) hi hj
  · intro i
    exact Set.union_subset (hPH i) (hS i)
  · intro i e he
    change e ∈ (P i).edgeSet ∪ S i at he
    rcases he with he | he
    · induction e using Sym2.inductionOn with
      | _ x y => exact ⟨x,by simp,hPU i x ((P i).fst_mem_support_of_mem_edges he)⟩
    · rcases he with he | he
      · exact ⟨f (i,false),he ▸ (by simp),(hf (i,false)).1⟩
      · exact ⟨f (i,true),he ▸ (by simp),(hf (i,true)).1⟩

end
end Cycle12
