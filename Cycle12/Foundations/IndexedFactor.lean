import Cycle12.Foundations.IndexedOrientation
import Mathlib.Combinatorics.Hall.Finite

/-! A two-factor in a regular indexed loopless multigraph. Hall's
inequality counts edge indices, so parallel edges retain their multiplicity. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem regular_indexed_hall (s t : I → V) {k : ℕ} (hk : 0 < k)
    (hs : ∀ v, (univ.filter (fun i => s i=v)).card=k)
    (ht : ∀ v, (univ.filter (fun i => t i=v)).card=k) :
    ∃ (f : V ↪ I) (p : V ≃ V), ∀ v, s (f v)=v ∧ t (f v)=p v := by
  let N : V → Finset V := fun v => (univ.filter (fun i => s i=v)).image t
  have hall : ∀ A : Finset V, A.card ≤ (A.biUnion N).card := by
    intro A
    let B := A.biUnion N
    have hsub : univ.filter (fun i => s i∈A) ⊆ univ.filter (fun i => t i∈B) := by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr ⟨s i,(mem_filter.mp hi).2,
        mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩⟩⟩
    have hleft : (univ.filter (fun i => s i∈A)).card=A.card*k := by
      rw [← sum_card_fiberwise_eq_card_filter]
      simp only [hs,sum_const,nsmul_eq_mul,Nat.cast_id]
    have hright : (univ.filter (fun i => t i∈B)).card=B.card*k := by
      rw [← sum_card_fiberwise_eq_card_filter]
      simp only [ht,sum_const,nsmul_eq_mul,Nat.cast_id]
    have hh := card_le_card hsub
    rw [hleft,hright] at hh
    exact le_of_mul_le_mul_right hh hk
  obtain ⟨p,hpinj,hp⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  have hpi : ∀ v, ∃ i, s i=v ∧ t i=p v := by
    intro v
    obtain ⟨i,hi,hit⟩ := mem_image.mp (hp v)
    exact ⟨i,(mem_filter.mp hi).2,hit⟩
  choose f hfs hft using hpi
  have hfinj : Function.Injective f := by
    intro x y h
    exact (hfs x).symm.trans ((congrArg s h).trans (hfs y))
  exact ⟨⟨f,hfinj⟩,Equiv.ofBijective p ⟨hpinj,Finite.surjective_of_injective hpinj⟩,
    fun v => ⟨hfs v,hft v⟩⟩

theorem BalancedIndexedOrientation.incidence_eq (a b : I → V)
    (O : BalancedIndexedOrientation a b) (v : V) :
    Suppression.incidenceDegree a b v=
      (univ.filter (fun i => O.source i=v)).card+
      (univ.filter (fun i => O.target i=v)).card := by
  have hpoint : ∀ i, ((if a i=v then (1:ℕ) else 0)+(if b i=v then 1 else 0))=
      ((if O.source i=v then 1 else 0)+(if O.target i=v then 1 else 0)) := by
    intro i
    rcases O.endpoints i with h | h <;> simp [h.1,h.2,add_comm]
  unfold Suppression.incidenceDegree
  rw [sum_congr rfl (fun i _ => hpoint i),sum_add_distrib]
  simp only [sum_boole,Nat.cast_id]

def indexedDegreeOn (a b : I → V) (F : Finset I) (v : V) : ℕ :=
  ∑ i∈F, ((if a i=v then 1 else 0)+(if b i=v then 1 else 0))

theorem indexedDegreeOn_univ (a b : I → V) (v : V) :
    indexedDegreeOn a b univ v=Suppression.incidenceDegree a b v := rfl

theorem indexedDegreeOn_sdiff (a b : I → V) (F : Finset I) (v : V) :
    indexedDegreeOn a b (univ\F) v+indexedDegreeOn a b F v=
      Suppression.incidenceDegree a b v := by
  exact sum_sdiff (subset_univ F)

theorem indexed_factor_source_count (s t : I → V) (f : V ↪ I) (p : V ≃ V)
    (hf : ∀ v, s (f v)=v ∧ t (f v)=p v) (v : V) :
    ((univ.image f).filter (fun i => s i=v)).card=1 ∧
    ((univ.image f).filter (fun i => t i=v)).card=1 := by
  have hs : (univ.image f).filter (fun i => s i=v)={f v} := by
    ext i
    simp only [mem_filter,mem_image,mem_univ,true_and,mem_singleton]
    constructor
    · rintro ⟨⟨w,rfl⟩,hw⟩
      have he : w=v := (hf w).1.symm.trans hw
      exact congrArg f he
    · rintro rfl
      exact ⟨⟨v,rfl⟩,(hf v).1⟩
  have ht : (univ.image f).filter (fun i => t i=v)={f (p.symm v)} := by
    ext i
    simp only [mem_filter,mem_image,mem_univ,true_and,mem_singleton]
    constructor
    · rintro ⟨⟨w,rfl⟩,hw⟩
      have he : w=p.symm v := p.injective ((hf w).2.symm.trans (hw.trans (p.apply_symm_apply v).symm))
      exact congrArg f he
    · rintro rfl
      exact ⟨⟨p.symm v,rfl⟩,(hf _).2.trans (p.apply_symm_apply v)⟩
  simp [hs,ht]

theorem exists_indexed_two_factor (a b : I → V) (hne : ∀ i, a i≠b i)
    {k : ℕ} (hk : 0 < k) (hdeg : ∀ v, Suppression.incidenceDegree a b v=2*k) :
    ∃ F : Finset I, ∀ v, indexedDegreeOn a b F v=2 := by
  obtain ⟨O⟩ := exists_balanced_indexed_orientation a b hne
    (fun v => (hdeg v).symm ▸ even_two_mul k)
  have hs : ∀ v, (univ.filter (fun i => O.source i=v)).card=k := by
    intro v
    have hh := O.incidence_eq a b v
    rw [hdeg v,O.balanced v] at hh
    have hb := O.balanced v
    omega
  have ht : ∀ v, (univ.filter (fun i => O.target i=v)).card=k := by
    intro v
    rw [← O.balanced v,hs]
  obtain ⟨f,p,hf⟩ := regular_indexed_hall O.source O.target hk hs ht
  refine ⟨univ.image f,fun v => ?_⟩
  have hpoint : ∀ i, ((if a i=v then (1:ℕ) else 0)+(if b i=v then 1 else 0))=
      ((if O.source i=v then 1 else 0)+(if O.target i=v then 1 else 0)) := by
    intro i
    rcases O.endpoints i with h | h <;> simp [h.1,h.2,add_comm]
  unfold indexedDegreeOn
  rw [sum_congr rfl (fun i _ => hpoint i),sum_add_distrib]
  simp only [sum_boole,Nat.cast_id]
  obtain ⟨hc,hd⟩ := indexed_factor_source_count O.source O.target f p hf v
  omega

end
end Cycle13
