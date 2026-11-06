import Cycle12.Foundations.IncidenceSubdivision

/-! Balanced orientations of indexed loopless multigraphs, obtained from
the simple incidence subdivision without identifying parallel edges. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

structure BalancedIndexedOrientation (a b : I → V) where
  source : I → V
  target : I → V
  endpoints : ∀ i, (source i=a i ∧ target i=b i) ∨ (source i=b i ∧ target i=a i)
  balanced : ∀ v, (univ.filter (fun i => source i=v)).card=
    (univ.filter (fun i => target i=v)).card

theorem exists_balanced_indexed_orientation (a b : I → V) (hne : ∀ i, a i≠b i)
    (heven : ∀ v, Even (Suppression.incidenceDegree a b v)) :
    Nonempty (BalancedIndexedOrientation a b) := by
  let H := edgeIncidenceGraph a b
  obtain ⟨D,hi,hbal,hcover⟩ := H.exists_balanced_orientation (incidence_even a b hne heven)
  have hcounts : ∀ i : I,
      (D.filter (fun d => d.fst=Sum.inr i)).card=1 ∧
      (D.filter (fun d => d.snd=Sum.inr i)).card=1 := by
    intro i
    have hc := orientation_incidence_count H D hi hcover (.inr i)
    have hb := hbal (.inr i)
    have hd := incidence_internal_degree a b hne i
    simp only [← ncard_neighborSet] at hc hd
    change (H.neighborSet (.inr i)).ncard=2 at hd
    omega
  have hin : ∀ (i : I) (p q : H.Dart), p∈D → q∈D →
      p.snd=Sum.inr i → q.snd=Sum.inr i → p=q := by
    intro i p q hp hq hps hqs
    exact card_le_one.mp (by rw [(hcounts i).2]) p (mem_filter.mpr ⟨hp,hps⟩)
      q (mem_filter.mpr ⟨hq,hqs⟩)
  have hout : ∀ (i : I) (p q : H.Dart), p∈D → q∈D →
      p.fst=Sum.inr i → q.fst=Sum.inr i → p=q := by
    intro i p q hp hq hps hqs
    exact card_le_one.mp (by rw [(hcounts i).1]) p (mem_filter.mpr ⟨hp,hps⟩)
      q (mem_filter.mpr ⟨hq,hqs⟩)
  have hchoice : ∀ i : I, ∃ (s t : V) (p q : H.Dart),
      ((s=a i ∧ t=b i) ∨ (s=b i ∧ t=a i)) ∧ p∈D ∧ q∈D ∧
      p.fst=Sum.inl s ∧ p.snd=Sum.inr i ∧ q.fst=Sum.inr i ∧ q.snd=Sum.inl t := by
    intro i
    obtain ⟨p,hp⟩ := card_pos.mp (show 0<(D.filter (fun d => d.snd=Sum.inr i)).card by rw [(hcounts i).2]; omega)
    obtain ⟨q,hq⟩ := card_pos.mp (show 0<(D.filter (fun d => d.fst=Sum.inr i)).card by rw [(hcounts i).1]; omega)
    have hp := mem_filter.mp hp
    have hq := mem_filter.mp hq
    have hpf : ∃ s : V, p.fst=Sum.inl s := by
      cases h : p.fst with
      | inl s => exact ⟨s,rfl⟩
      | inr j =>
        have hh := p.adj
        rw [h,hp.2] at hh
        exact False.elim hh
    have hqt : ∃ t : V, q.snd=Sum.inl t := by
      cases h : q.snd with
      | inl t => exact ⟨t,rfl⟩
      | inr j =>
        have hh := q.adj
        rw [hq.2,h] at hh
        exact False.elim hh
    obtain ⟨s,hps⟩ := hpf
    obtain ⟨t,hqt⟩ := hqt
    have hs : s=a i ∨ s=b i := by have hh := p.adj; rw [hps,hp.2] at hh; exact hh
    have ht : t=a i ∨ t=b i := by have hh := q.adj; rw [hq.2,hqt] at hh; exact hh
    have hst : s≠t := by
      intro he
      have hpq : p=q := hi p hp.1 q hq.1 (by
        change s(p.fst,p.snd)=s(q.fst,q.snd)
        rw [hps,hp.2,hq.2,hqt,he,Sym2.eq_swap])
      have hh := congrArg (fun d : H.Dart => d.fst) hpq
      rw [hps,hq.2] at hh
      cases hh
    refine ⟨s,t,p,q,?_,hp.1,hq.1,hps,hp.2,hq.2,hqt⟩
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs,ht⟩
    · exact Or.inr ⟨hs,ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  choose s t p q hpat hpD hqD hps hpt hqs hqt using hchoice
  have hs : ∀ v, (univ.filter (fun i => s i=v)).card=
      (D.filter (fun d => d.fst=Sum.inl v)).card := by
    intro v
    apply card_bij (fun i _ => p i)
    · intro i hi
      exact mem_filter.mpr ⟨hpD i,(hps i).trans (congrArg Sum.inl (mem_filter.mp hi).2)⟩
    · intro i hi j hj he
      have hh := congrArg (fun d : H.Dart => d.snd) he
      rw [hpt,hpt] at hh
      exact Sum.inr.inj hh
    · intro d hd
      have hd := mem_filter.mp hd
      have hde : ∃ i : I, d.snd=Sum.inr i := by
        cases h : d.snd with
        | inr i => exact ⟨i,rfl⟩
        | inl w => have hh := d.adj; rw [hd.2,h] at hh; exact False.elim hh
      obtain ⟨i,hi⟩ := hde
      have he := hin i (p i) d (hpD i) hd.1 (hpt i) hi
      have hv : s i=v := Sum.inl.inj ((hps i).symm.trans ((congrArg (fun d : H.Dart => d.fst) he).trans hd.2))
      exact ⟨i,mem_filter.mpr ⟨mem_univ _,hv⟩,he⟩
  have ht : ∀ v, (univ.filter (fun i => t i=v)).card=
      (D.filter (fun d => d.snd=Sum.inl v)).card := by
    intro v
    apply card_bij (fun i _ => q i)
    · intro i hi
      exact mem_filter.mpr ⟨hqD i,(hqt i).trans (congrArg Sum.inl (mem_filter.mp hi).2)⟩
    · intro i hi j hj he
      have hh := congrArg (fun d : H.Dart => d.fst) he
      rw [hqs,hqs] at hh
      exact Sum.inr.inj hh
    · intro d hd
      have hd := mem_filter.mp hd
      have hde : ∃ i : I, d.fst=Sum.inr i := by
        cases h : d.fst with
        | inr i => exact ⟨i,rfl⟩
        | inl w => have hh := d.adj; rw [h,hd.2] at hh; exact False.elim hh
      obtain ⟨i,hi⟩ := hde
      have he := hout i (q i) d (hqD i) hd.1 (hqs i) hi
      have hv : t i=v := Sum.inl.inj ((hqt i).symm.trans ((congrArg (fun d : H.Dart => d.snd) he).trans hd.2))
      exact ⟨i,mem_filter.mpr ⟨mem_univ _,hv⟩,he⟩
  exact ⟨⟨s,t,hpat,fun v => (hs v).trans ((hbal (.inl v)).trans (ht v).symm)⟩⟩

end
end Cycle13
