import Cycle12.Foundations.MaximumTwoFactor
import Cycle12.Foundations.SmallIndependentSelection
import Cycle12.Foundations.NeighborNearMatching
import Cycle12.Foundations.SeedDeficiency

/-! Choosing the protected triple from a maximal partial two-factor.
The argument uses the total degree deficiency, without classifying path
components. Parallel demand edges remain individually indexed. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem factor_low_support_degree (a b : I → V) (F : Finset I)
    (hsat : ∀ i, i∉F → indexedDegreeOn a b F (a i)=2 ∨ indexedDegreeOn a b F (b i)=2)
    (v : {v // indexedDegreeOn a b F v ≤ 1}) :
    ((indexedSupport a b).comap (fun x : {v // indexedDegreeOn a b F v ≤ 1} => x.val)).degree v ≤
      indexedDegreeOn a b F v.val := by
  let e : {v // indexedDegreeOn a b F v ≤ 1} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let H := indexedSupport (fun i : F => a i.val) (fun i : F => b i.val)
  have hsub : (indexedSupport a b).comap e ≤ H.comap e := by
    intro x y h
    obtain ⟨hne,i,hi⟩ := h
    have hiF : i∈F := by
      apply maximal_two_factor_low_edge a b univ F (fun i _ => hsat i) (mem_univ i)
      · rcases Sym2.eq_iff.mp hi with hh | hh
        · rw [hh.1]; exact x.property
        · rw [hh.1]; exact y.property
      · rcases Sym2.eq_iff.mp hi with hh | hh
        · rw [hh.2]; exact y.property
        · rw [hh.2]; exact x.property
    exact ⟨hne,⟨i,hiF⟩,hi⟩
  have hh := (SimpleGraph.degree_le_of_le hsub (v:=v)).trans (comap_degree_le H e v)
  have hd := indexedSupport_degree_le (fun i : F => a i.val) (fun i : F => b i.val) v.val
  rw [indexedDegreeOn_subtype] at hd
  exact hh.trans hd

theorem deficient_factor_protected_triple (a b : I → V) (F : Finset I) {d : ℕ}
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ d)
    (hsat : ∀ i, i∉F → indexedDegreeOn a b F (a i)=2 ∨ indexedDegreeOn a b F (b i)=2)
    (hdef : (∑ v, (2-indexedDegreeOn a b F v)) ≤ 6)
    (hspace : 2*(d+1) < Fintype.card V) :
    ∃ B : Finset V, B.card=3 ∧ (indexedSupport a b).IsIndepSet B ∧
      (∀ v, indexedDegreeOn a b F v=0 → v∈B) ∧
      ((univ.filter (fun v => indexedDegreeOn a b F v ≤ 1))\B).card ≤ 3 := by
  let L := {v : V // indexedDegreeOn a b F v ≤ 1}
  let H := (indexedSupport a b).comap (fun v : L => v.val)
  let Z : Finset L := univ.filter (fun v => indexedDegreeOn a b F v.val=0)
  have hL : Fintype.card L ≤ 6 := by
    have hpoint : ∀ v, (if indexedDegreeOn a b F v ≤ 1 then 1 else 0) ≤
        2-indexedDegreeOn a b F v := by intro v; split_ifs <;> omega
    have hh := sum_le_sum (s:=univ) (fun v _ => hpoint v)
    simpa only [sum_boole,Nat.cast_id,Fintype.card_subtype,L] using hh.trans hdef
  have hZ : Z.card ≤ 3 := by
    have hpoint : ∀ v : L, (if indexedDegreeOn a b F v.val=0 then 2 else 0) ≤
        2-indexedDegreeOn a b F v.val := by intro v; split_ifs <;> omega
    have hh := sum_le_sum (s:=univ) (fun v _ => hpoint v)
    have hsum : (∑ v : L, (2-indexedDegreeOn a b F v.val)) ≤
        ∑ v, (2-indexedDegreeOn a b F v) := by
      rw [← sum_subtype (univ.filter (fun v => indexedDegreeOn a b F v ≤ 1))
        (p:=fun v => indexedDegreeOn a b F v ≤ 1) (fun v => by simp)
        (fun v => 2-indexedDegreeOn a b F v)]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have he : (∑ v : L, if indexedDegreeOn a b F v.val=0 then 2 else 0)=2*Z.card := by
      simp only [← sum_filter, sum_const, nsmul_eq_mul, Nat.cast_id, Z]
      omega
    rw [he] at hh
    omega
  have hH : ∀ v : L, H.degree v ≤ indexedDegreeOn a b F v.val :=
    fun v => factor_low_support_degree a b F hsat v
  obtain ⟨C,hZC,hC,hCi,hout⟩ := small_matching_independent_selection H
    (fun v => (hH v).trans v.property) hL Z hZ (by
      intro z hz v hadj
      have he := (mem_filter.mp hz).2
      have hh := hH z
      have hp := SimpleGraph.Adj.degree_pos_left (G:=H) hadj
      omega)
  let S : Finset V := C.image Subtype.val
  have hSc : S.card=C.card := card_image_of_injective _ Subtype.val_injective
  have hSi : (indexedSupport a b).IsIndepSet S := by
    intro x hx y hy hxy hadj
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
    exact hCi hu hv (fun he => hxy (congrArg Subtype.val he)) hadj
  obtain ⟨B,hSB,hB,_,hBi⟩ := exists_independent_extension (indexedSupport a b) S ∅
    (fun v => (indexedSupport_degree_le a b v).trans (hd v)) hSi (by simp)
    (hSc ▸ hC) (by simpa using hspace)
  refine ⟨B,hB,hBi,?_,?_⟩
  · intro v hv
    let z : L := ⟨v,by omega⟩
    exact hSB (mem_image.mpr ⟨z,hZC (mem_filter.mpr ⟨mem_univ _,hv⟩),rfl⟩)
  · have hsub : (univ.filter (fun v => indexedDegreeOn a b F v ≤ 1))\B ⊆
        (univ\C).image Subtype.val := by
      intro v hv
      have hp := mem_sdiff.mp hv
      let z : L := ⟨v,(mem_filter.mp hp.1).2⟩
      refine mem_image.mpr ⟨z,mem_sdiff.mpr ⟨mem_univ _,?_⟩,rfl⟩
      intro hz
      exact hp.2 (hSB (mem_image.mpr ⟨z,hz,rfl⟩))
    exact (card_le_card hsub).trans (card_image_le.trans hout)

theorem exists_factor_protected_triple (a b : I → V) (hne : ∀ i, a i≠b i)
    (F₀ : Finset I) (hcap : ∀ v, indexedDegreeOn a b F₀ v ≤ 2)
    (hdef : (∑ v, (2-indexedDegreeOn a b F₀ v)) ≤ 6) {d : ℕ}
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ d)
    (hspace : 2*(d+1) < Fintype.card V) :
    ∃ F : Finset I, ∃ B : Finset V, F₀⊆F ∧
      (∀ v, indexedDegreeOn a b F v ≤ 2) ∧ B.card=3 ∧
      (indexedSupport a b).IsIndepSet B ∧
      (∀ v, indexedDegreeOn a b F v=0 → v∈B) ∧
      ((univ.filter (fun v => indexedDegreeOn a b F v ≤ 1))\B).card ≤ 3 := by
  obtain ⟨F,hF₀,_,hF,hsat⟩ := exists_maximal_two_factor a b hne univ F₀ (subset_univ _) hcap
  have hdefF : (∑ v, (2-indexedDegreeOn a b F v)) ≤ 6 := by
    apply le_trans (sum_le_sum (fun v _ => ?_)) hdef
    exact Nat.sub_le_sub_left (indexedDegreeOn_mono a b hF₀ v) 2
  obtain ⟨B,hB⟩ := deficient_factor_protected_triple a b F hd
    (fun i => hsat i (mem_univ _)) hdefF hspace
  exact ⟨F,B,hF₀,hF,hB⟩

end
end Cycle13
