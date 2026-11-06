import Cycle12.Foundations.IndependentExtension

/-! In a matching graph on at most six vertices, choose at most three
independent vertices, containing prescribed isolated vertices, and leave
at most three vertices unchosen. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem small_matching_independent_selection (H : SimpleGraph V)
    (hd : ∀ v, H.degree v ≤ 1) (hn : Fintype.card V ≤ 6)
    (Z : Finset V) (hZ : Z.card ≤ 3) (hiso : ∀ z∈Z, ∀ v, ¬H.Adj z v) :
    ∃ C : Finset V, Z⊆C ∧ C.card ≤ 3 ∧ H.IsIndepSet C ∧ (univ\C).card ≤ 3 := by
  let T := (univ : Finset (Finset V)).filter (fun M => Z⊆M ∧ H.IsIndepSet M)
  have hT : T.Nonempty := ⟨Z,mem_filter.mpr ⟨mem_univ _,Subset.rfl,
    fun z hz v hv _ => hiso z hz v⟩⟩
  obtain ⟨M,hMT,hmax⟩ := exists_max_image T Finset.card hT
  obtain ⟨hZM,hM⟩ := (mem_filter.mp hMT).2
  have hneighbor : ∀ v, v∉M → ∃ u∈M, H.Adj v u := by
    intro v hv
    by_contra h
    push Not at h
    have hnew : insert v M∈T := by
      refine mem_filter.mpr ⟨mem_univ _,hZM.trans (subset_insert _ _),?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hx | hx <;> rcases mem_insert.mp hy with hy | hy
      · exact (hxy (hx.trans hy.symm)).elim
      · subst x; exact h y hy
      · subst y; exact fun hh => h x hx hh.symm
      · exact hM hx hy hxy
    have hh := hmax (insert v M) hnew
    rw [card_insert_of_notMem hv] at hh
    omega
  let N := univ\M
  have hchoice : ∀ v : N, ∃ u : M, H.Adj v.val u.val := by
    intro v
    obtain ⟨u,hu,hvu⟩ := hneighbor v.val (mem_sdiff.mp v.property).2
    exact ⟨⟨u,hu⟩,hvu⟩
  choose g hg using hchoice
  have hginj : Function.Injective g := by
    intro x y he
    apply Subtype.ext
    have hcard : (H.neighborFinset (g x).val).card ≤ 1 := by
      rw [card_neighborFinset_eq_degree]
      exact hd _
    apply card_le_one.mp hcard
    · exact (H.mem_neighborFinset _ _).mpr (hg x).symm
    · exact (H.mem_neighborFinset _ _).mpr (he ▸ (hg y).symm)
  have hNM := Fintype.card_le_of_injective g hginj
  simp only [Fintype.card_coe] at hNM
  by_cases hMsmall : M.card ≤ 3
  · exact ⟨M,hZM,hMsmall,hM,hNM.trans hMsmall⟩
  · obtain ⟨C,hZC,hCM,hC⟩ := exists_subsuperset_card_eq hZM hZ (by omega : 3 ≤ M.card)
    refine ⟨C,hZC,hC.le,?_,?_⟩
    · exact fun x hx y hy hxy => hM (hCM hx) (hCM hy) hxy
    · have hh := card_sdiff_add_card_eq_card (subset_univ C)
      rw [card_univ,hC] at hh
      omega

end
end Cycle13
