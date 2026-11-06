import Cycle12.Foundations.TerminalReduction
import Cycle12.Foundations.IndexedDegreeSum

/-! The two actual three-hub reductions, composed. For an even regular
demand graph in the GMM range, six vertices can be removed while reducing
the maximum demand degree by two; every residual solution pulls back. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

set_option maxHeartbeats 1500000 in
theorem regular_six_vertex_reduction (a b : I → V) (hne : ∀ i, a i≠b i)
    {k : ℕ} (hk : 2 ≤ k) (hdeg : ∀ v, Suppression.incidenceDegree a b v=2*k)
    (hbound : 2*k+4 ≤ 2*(Fintype.card V/6)) :
    Nonempty (TerminalReduction a b 6 (2*k-2)) := by
  obtain ⟨w,hsep⟩ := exists_independent_three a b hne (fun v => (hdeg v).le)
    (by omega : 2*(2*k+1)<Fintype.card V)
  obtain ⟨A₁,A₂,hdis,hA₁,hA₂⟩ := exists_disjoint_indexed_two_factors a b hne hk hdeg
  have hnY := seedInterior_card w
  obtain ⟨F,B,hF,hB,hBi,hzero,hsmall⟩ := exists_second_factor a b hne w hsep hdis hA₁ hA₂
    (d:=2*k-2) (fun v => by rw [hdeg]; omega) (by omega)
  let Borig := B.image Subtype.val
  have hBorig : Borig.card ≤ 3 := by
    rw [card_image_of_injective _ Subtype.val_injective,hB]
  have hBind : ∀ i, i∉A₁ → ¬(a i∈Borig ∧ b i∈Borig) := by
    intro i hi
    exact independent_inside_no_edge (remainderLeft a A₁) (remainderLeft b A₁)
      (fun j => hne j.val) w B hBi ⟨i,hi⟩
  obtain ⟨D₁,t₁,ht₁,hd₁,hp₁,hi₁,hr₁⟩ := exists_three_hub_reduction a b w hsep A₁
    (fun v => (hA₁ v).le) Borig hBorig (by intro r; rw [hdeg,hA₁]; omega)
  let a₁ := D₁.residualLeft t₁
  let b₁ := D₁.residualRight
  let F₁ : Finset (SeedKeep (remainderLeft a A₁) (remainderLeft b A₁) w ⊕
      SeedStar (remainderLeft a A₁) (remainderLeft b A₁) w) := F.image Sum.inl
  have hF₁ : ∀ v, indexedDegreeOn a₁ b₁ F₁ v=
      indexedDegreeOn (seedKeepLeft (remainderLeft a A₁) (remainderLeft b A₁) w)
        (seedKeepRight (remainderLeft a A₁) (remainderLeft b A₁) w) F v :=
    fun v => residual_inl_factor_degree D₁ t₁ F v
  let w₂ := tripleOfFinset B hB
  have hw₂ : ∀ r, w₂ r∈B := tripleOfFinset_mem B hB
  have hsep₂ : ∀ r s i, ¬(a₁ i=w₂ r ∧ b₁ i=w₂ s) := by
    intro r s i hi
    apply hi₁ hBind i
    exact ⟨mem_image.mpr ⟨w₂ r,hw₂ r,congrArg Subtype.val hi.1.symm⟩,
      mem_image.mpr ⟨w₂ s,hw₂ s,congrArg Subtype.val hi.2.symm⟩⟩
  let B₂ := (univ.filter (fun v => indexedDegreeOn a₁ b₁ F₁ v ≤ 1))\B
  have hB₂ : B₂.card ≤ 3 := by simpa only [B₂,hF₁] using hsmall
  have hquota₂ : ∀ r, Suppression.incidenceDegree a₁ b₁ (w₂ r)+5 ≤
      Fintype.card (SeedInterior w)/3+indexedDegreeOn a₁ b₁ F₁ (w₂ r) := by
    intro r
    have hp := hp₁ (w₂ r) (mem_image.mpr ⟨w₂ r,hw₂ r,rfl⟩)
    rw [hA₁,hdeg] at hp
    change Suppression.incidenceDegree a₁ b₁ (w₂ r)+2=2*k at hp
    omega
  obtain ⟨D₂,t₂,ht₂,hd₂,hp₂,hi₂,hr₂⟩ := exists_three_hub_reduction a₁ b₁ w₂ hsep₂ F₁
    (fun v => (hF₁ v).symm ▸ hF v) B₂ hB₂ hquota₂
  refine ⟨{
    Vertices := SeedInterior w₂
    vertexFintype := inferInstance
    vertexDecidableEq := inferInstance
    Edges := SeedKeep (remainderLeft a₁ F₁) (remainderLeft b₁ F₁) w₂ ⊕
      SeedStar (remainderLeft a₁ F₁) (remainderLeft b₁ F₁) w₂
    edgeFintype := Fintype.ofFinite _
    left := D₂.residualLeft t₂
    right := D₂.residualRight
    order := by have hh := seedInterior_card w₂; omega
    degree := ?_
    pullback := ?_ }⟩
  · intro v
    have hvB : v.val∉B := by
      intro hv
      obtain ⟨r,hr⟩ := mem_tripleOfFinset B hB hv
      exact v.property r hr.symm
    have hlow : 1 ≤ indexedDegreeOn a₁ b₁ F₁ v.val := by
      by_contra hh
      have hz : indexedDegreeOn a₁ b₁ F₁ v.val=0 := by omega
      rw [hF₁] at hz
      exact hvB (hzero v.val hz)
    have hfirst := hd₁ v.val
    rw [hA₁,hdeg] at hfirst
    change Suppression.incidenceDegree a₁ b₁ v.val+2 ≤ 2*k+1 at hfirst
    by_cases hv₂ : v.val∈B₂
    · have hsecond := hp₂ v hv₂
      simp only [incidenceDegree_eq_ncard] at hfirst hsecond ⊢
      omega
    · have hhigh : 2 ≤ indexedDegreeOn a₁ b₁ F₁ v.val := by
        by_contra hh
        exact hv₂ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,hvB⟩)
      have hsecond := hd₂ v
      simp only [incidenceDegree_eq_ncard] at hfirst hsecond ⊢
      omega
  · rintro ⟨R⟩
    obtain ⟨S⟩ := hr₂ R
    exact hr₁ S

end
end Cycle13
