import Cycle12.ReservoirLinkFamily12
import Cycle12.HubFragmentPartition12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Every split fragment is joined through A and then closed through B.
The disjoint vertex banks make each resulting cycle simple; the statement
retains the exact old-edge coverage and bounds every added edge by H. -/
theorem close_hub_fragments [Nonempty V]
    (G H : SimpleGraph V) (hHG : H ≤ G) (A B : Finset V) (hAB : Disjoint A B)
    {z upperA upperB : ℝ} (hA : ReservoirSample H A z upperA) (hB : ReservoirSample H B z upperB)
    (F : I → HubFragment G)
    (hbody : Pairwise (fun i j => Disjoint (F i).body (F j).body))
    (hout : ∀ i, ∀ v ∈ (F i).support, v ∉ A ∧ v ∉ B)
    (houter : ∀ v, (univ.filter (fun k : I × Bool => (F k.1).outer k.2 = v)).card ≤ 2)
    (hnear : Function.Injective (fun k : {i // (F i).IsSplit} × Bool => (F k.1.val).near k.1.property k.2))
    (hz : 8192 ≤ z) (hzr : z ≤ (Fintype.card V:ℝ))
    (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) (hcard : Fintype.card I ≤ Fintype.card V) :
    ∃ C : ∀ i, G.Walk ((F i).outer false) ((F i).outer false),
      (∀ i, (C i).IsCycle) ∧
      Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
      (∀ i, (F i).body ⊆ (C i).edgeSet) ∧
      ∀ i, (C i).edgeSet ⊆ (F i).body ∪ H.edgeSet := by
  let J := {i // (F i).IsSplit}
  let sourceA : J × Bool → V := fun k => (F k.1.val).near k.1.property k.2
  have hoA : ∀ k, sourceA k ∉ A := fun k =>
    (hout k.1.val _ ((F k.1.val).near_mem_support k.1.property k.2)).1
  have hlA : ∀ v, (univ.filter (fun k => sourceA k = v)).card ≤ 2 := by
    intro v
    have hh : (univ.filter (fun k => sourceA k = v)).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      exact hnear ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
    omega
  have hJ : Fintype.card J ≤ Fintype.card V :=
    (Fintype.card_subtype_le _).trans hcard
  obtain ⟨links,hLU,hLL,hLH,hmeet⟩ := sampled_link_family G H hHG A hA sourceA hoA hlA
    hz hzr hlog hsquare hJ
  let L : ∀ i, ∀ h : (F i).IsSplit,
      ReservoirLink G ((F i).near h false) ((F i).near h true) := fun i h => links ⟨i,h⟩
  let Q : ∀ i, G.Walk ((F i).outer false) ((F i).outer true) := fun i => (F i).fill (L i)
  have hQ : ∀ i, (Q i).IsPath := by
    intro i
    apply (F i).fill_isPath (L i)
    intro h v hv hF
    exact (hout i v hF).1 (hLU ⟨i,h⟩ v hv)
  have hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) := by
    apply HubFragment.fill_family_disjoint F L hbody
    · intro i j hij hi hj
      exact hLL (i := ⟨i,hi⟩) (j := ⟨j,hj⟩) (fun he => hij (congrArg Subtype.val he))
    · intro i j hj
      apply Set.disjoint_left.mpr
      intro e heF heL
      obtain ⟨v,hv,hvA⟩ := hmeet ⟨j,hj⟩ e heL
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hh := (F i).endpoints_mem_support heF
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact (hout i _ hh.1).1 hvA
        · exact (hout i _ hh.2).1 hvA
  have hoB : ∀ i, ∀ v ∈ (Q i).support, v ∉ B := by
    intro i v hv
    rcases (F i).fill_support (L i) hv with hv | ⟨h,hv⟩
    · exact (hout i v hv).2
    · exact fun hvB => Finset.disjoint_left.mp hAB (hLU ⟨i,h⟩ v hv) hvB
  let sourceB : I × Bool → V := fun k => (F k.1).outer k.2
  obtain ⟨C,hC,hCC,hQC,hCH⟩ := close_external_path_family G H hHG B hB sourceB Q hQ hQQ hoB
    houter hz hzr hlog hsquare hcard
  refine ⟨C,hC,hCC,fun i => ((F i).fill_contains_body (L i)).trans (hQC i),?_⟩
  intro i e he
  rcases hCH i he with he | he
  · have he' : e ∈ (F i).body ∪ ⋃ h : (F i).IsSplit, (L i h).edges :=
      ((F i).fill_edges (L i)) ▸ he
    rcases he' with he | he
    · exact Or.inl he
    · obtain ⟨h,he⟩ := Set.mem_iUnion.mp he
      exact Or.inr (hLH ⟨i,h⟩ he)
  · exact Or.inr he

end
end Cycle12
